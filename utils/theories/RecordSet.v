From MetaRocq.Template Require Import Ast.
From MetaRocq.Template Require Import AstUtils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Template Require Import Loader.
From MetaRocq.Template Require Import TemplateMonad.
From MetaRocq.Utils Require Import monad_utils.
From MetaRocq.Utils Require Import utils.

Global Unset Asymmetric Patterns.

Import MRMonadNotation.

Class SetterFromGetter {A B} (a : A -> B) :=
  setter_from_getter : (B -> B) -> A -> A.

Definition aRelevant (na : name) : aname :=
  {| binder_name := na; binder_relevance := Relevant |}.

Definition make_setters (T : Type) : TemplateMonad unit :=
  Tast <- tmQuote T;;
  ind <- match Tast with
        | tInd ind _ => ret ind
        | tApp (tInd ind _) _ => ret ind
        | _ => tmFail "Cannot extract inductive, are you sure you passed a type?"
        end;;
  mib <- tmQuoteInductive (inductive_mind ind);;
  match ind_finite mib with
  | BiFinite => ret tt
  | _ => tmFail "Unexpected finite kind; are you sure you are creating setters for a record?"
  end;;
  oib <- match nth_error (ind_bodies mib) (inductive_ind ind) with
         | Some oib => ret oib
         | None => tmFail "Could not find inductive in mutual inductive?"
         end;;
  '(ctor, ar) <- match ind_ctors oib with
                 | [c] => ret (c.(cstr_type), c.(cstr_arity))
                 | _ => tmFail "Type should have exactly one constructor"
                 end;;

  let fix find_getter_kns (t : term) : TemplateMonad (list kername) :=
      match t with
      | tProd na A B =>
        kn <-
        match binder_name na with
        | nNamed id => ret ((inductive_mind ind).1, id)
        | nAnon => tmFail "Records with anonymous fields are not supported"
        end;;
        kns <- find_getter_kns B;;
        ret (kn :: kns)
      | tLetIn na a A B => find_getter_kns B
      | _ => ret []
      end in

  getter_kns <- find_getter_kns ctor;;

  let fix create_setters (t : term) (idx : nat) : TemplateMonad unit :=
      match t with
      | tProd na A B =>
        match binder_name na with
        | nNamed id =>
          (* Create setter *)
          let getter_kn := ((inductive_mind ind).1, id) in

          let body :=
              tLambda
                (aRelevant (nNamed "f"))
                (tProd (aRelevant nAnon) A A)
                (tLambda
                   (aRelevant (nNamed "r"))
                   (tInd ind [])
                   (tApp
                      (tConstruct ind 0 [])
                      (mapi
                         (fun i (gkn : kername) =>
                            let get := tApp (tConst gkn []) [tRel 0] in
                            if eq_kername gkn getter_kn then
                              tApp (tRel 1) [get]
                            else
                              get)
                         getter_kns))) in

          let setter_id := "set_" ^ ind_name oib ^ "_" ^ id in
          tmMkDefinition setter_id body;;

          (* Create SetterFromGetter instance *)
          setter_gr <- tmLocate1 setter_id;;
          setter_kn <- match setter_gr with
          | ConstRef kn => ret kn
          | _ => tmFail "Unexpected global_reference after unquoting"
          end;;

          (* I could not find a way to specify the type of an unquoted constant,
             so we always unquote as a cast *)
          let body :=
              tCast
                (tConst setter_kn [])
                Cast
                (tApp
                   <% @SetterFromGetter %>
                   [tInd ind []; A; tConst getter_kn []]) in

          let setter_from_getter_id := "setter_from_getter_" ^ ind_name oib ^ "_" ^ id in
          tmMkDefinition setter_from_getter_id body;;

          tmLocate1 setter_from_getter_id >>= tmExistingInstance global
        | nAnon => ret tt
        end;;
        create_setters B (S idx)
      | tLetIn na a A B => create_setters B idx
      | _ => ret tt
      end in
  create_setters ctor 0.

Module RecordSetNotations.
  Declare Scope record_set.
  Delimit Scope record_set with rs.
  Open Scope rs.
  Notation "x <| proj ::= f |>" := ((_ : SetterFromGetter proj) f x)
                                   (at level 12, f at next level, left associativity) : record_set.
  Notation "x <| proj := v |>" := ((_ : SetterFromGetter proj) (fun _ => v) x)
                                  (at level 12, left associativity) : record_set.
  Notation "x <| proj1 ; proj2 ; .. ; projn ::= f |>" :=
    ((_ : SetterFromGetter proj1)
       ((_ : SetterFromGetter proj2) .. ((_ : SetterFromGetter projn) f) ..) x)
    (at level 12, left associativity).
  Notation "x <| proj1 ; proj2 ; .. ; projn := v |>" :=
    ((_ : SetterFromGetter proj1)
       ((_ : SetterFromGetter proj2) .. ((_ : SetterFromGetter projn) (fun _ => v)) ..) x)
    (at level 12, left associativity).
End RecordSetNotations.
