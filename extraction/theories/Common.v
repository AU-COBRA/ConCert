From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import String.

From MetaCoq Require Import monad_utils.
From MetaCoq Require Import MCPrelude.
From MetaCoq Require Import MCProd.
From MetaCoq Require Import MCString.
From MetaCoq Require Import MCSquash.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import SafeErasureFunction.
From MetaCoq.Erasure Require Import SafeTemplateErasure.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICValidity TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import SafeTemplateChecker.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.
From ConCert.Extraction Require Import Optimize.

Module T := MetaCoq.Template.Ast.
Module P := MetaCoq.PCUIC.PCUICAst.
Module E := MetaCoq.Erasure.EAst.
Module TUtil := MetaCoq.Template.AstUtils.
Module PUtil := MetaCoq.PCUIC.PCUICAstUtils.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module EF := MetaCoq.Erasure.SafeErasureFunction.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.

Local Open Scope string.
Import ListNotations.
Import MonadNotation.

(* This is here so that we get a typing error if Chain ever changes *)
Check (fun _ => eq_refl) :
  forall chain,
    Blockchain.account_balance chain = let (_, _, _, f) := chain in f.
Local Open Scope bool.
Import E.

Definition kername_of_string (s : string) : kername :=
  let l := rev (str_split "." s) in
  (MPfile (tl l), hd "" l).

Definition ConCertChain : kername :=
  Eval compute in kername_of_string "ConCert.Execution.Blockchain.Chain".

Definition uses_account_balance (t : term) : bool :=
  (fix f (t : term) (ab_funcs : list bool) :=
     match t with
     | tBox => false
     | tRel i => nth i ab_funcs false
     | tVar _ => false
     | tEvar _ ts => fold_left (fun b t => b || f t ab_funcs) ts false
     | tLambda _ t => f t (false :: ab_funcs)
     | tLetIn _ val body => f val ab_funcs || f body (false :: ab_funcs)
     | tApp head body => f head ab_funcs || f body ab_funcs
     | tConst _ => false
     | tConstruct _ _ => false
     | tCase (ind, _) disc brs =>
       f disc ab_funcs ||
       if eq_kername (inductive_mind ind) ConCertChain then
         match brs with
         | [(4, tLambda _ (tLambda _ (tLambda _ (tLambda _ t))))] =>
           f t (true :: false :: false :: false :: ab_funcs)
         | _ => fold_left (fun b '(_, t) => b || f t ab_funcs) brs false
         end
       else
         fold_left (fun b '(_, t) => b || f t ab_funcs) brs false
     | tProj _ t => f t ab_funcs
     | tFix defs _
     | tCoFix defs _ =>
       let ab_funcs := (repeat false (List.length defs) ++ ab_funcs)%list in
       fold_left (fun b d => b || f (dbody d) ab_funcs) defs false
     end) t [].

Definition result_of_typing_result
           {A}
           (Σ : P.global_env_ext)
           (tr : typing_result A) : result A string :=
  match tr with
  | Checked a => ret a
  | TypeError err => Err (string_of_type_error Σ err)
  end.

Definition string_of_env_error Σ e :=
  match e with
  | IllFormedDecl s e =>
    "IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error Σ e
  | AlreadyDeclared s => "Alreadydeclared " ++ s
  end%string.

Definition result_of_EnvCheck {A} (ec : EnvCheck A) : result A string :=
  match ec with
  | CorrectDecl a => ret a
  | EnvError Σ err => Err (string_of_env_error Σ err)
  end.

Definition result_of_option {A} (o : option A) (err : string) : result A string :=
  match o with
  | Some a => ret a
  | None => Err err
  end.

(* These next functions deal with specializing globals that might
   refer to a ChainBase variable in the context. They work by
   replacing uses of it with the specified term, and by removing it
   from applications. For example:
   Inductive Foo (cb : ChainBase) := ctor (addr : Address cb).
   Definition a (cb : ChainBase) (n : nat) := n.
   Definition b (cb : ChainBase) (addr : Foo cb) (n : N) :=
     a cb (N.to_nat n).

   becomes
   Inductive Foo := ctor (addr : Address replacement_term).
   Definition a (n : nat) := n.
   Definition b (addr : Foo) (n : N) :=
     a (N.to_nat n).

   Note: Only specializes ChainBase when it is the very first abstraction.  *)
Module ChainBaseSpecialization.
  Import P.
  Definition ChainBase_kername : kername :=
    Eval compute in kername_of_string "ConCert.Execution.Blockchain.ChainBase".

  Section ChainBaseSpecialization.
    Context (replacement_term : term).

    Definition contains (n : kername) : list kername -> bool :=
      existsb (eq_kername n).

    Inductive VarInfo :=
    (* this var is a ChainBase that should be replaced by the replacement term *)
    | replace
    (* this var has type ChainBase -> ... and its first argument should be removed *)
    | specialize
    | none.

    Fixpoint specialize_term
             (specialized : list kername) : list VarInfo -> term -> result term string :=
      fix f Γ t :=
        match t with
        | tRel n =>
          vi <- result_of_option (nth_error Γ n) "Unbound tRel";;
          match vi with
          | replace => ret replacement_term
          | specialize => Err "Unapplied tRel that should be specialized appears in term"
          | none => ret t
          end
        | tVar _ => ret t
        | tEvar n ts =>
          ts <- monad_map (f Γ) ts;;
          ret (tEvar n ts)
        | tSort univ =>
          ret t
        | tProd name ty body =>
          ty <- f Γ ty;;
          body <- f (none :: Γ) body;;
          ret (tProd name ty body)
        | tLambda name ty body =>
          ty <- f Γ ty;;
          body <- f (none :: Γ) body;;
          ret (tLambda name ty body)
        | tLetIn name val val_ty body =>
          val <- f Γ val;;
          val_ty <- f (none :: Γ) val_ty;;
          body <- f (none :: Γ) body;;
          ret (tLetIn name val val_ty body)
        | tApp (tConst name _ as head) arg
        | tApp (tInd {| inductive_mind := name |} _ as head) arg
        | tApp (tConstruct {| inductive_mind := name |} _ _ as head) arg =>
          if contains name specialized then
            ret head
          else
            arg <- f Γ arg;;
            ret (tApp head arg)
        | tApp (tRel i as head) arg =>
          vi <- result_of_option (nth_error Γ i) "Unbound tRel";;
          match vi with
          | replace => Err "Unexpected application"
          | specialize => ret (tRel (i - 1)) (* removed chain base inbetween, hacky *)
          | none => arg <- f Γ arg;;
                    ret (tApp head arg)
          end
        | tApp head arg =>
          head <- f Γ head;;
          arg <- f Γ arg;;
          ret (tApp head arg)
        | tConst name _
        | tInd {| inductive_mind := name |} _
        | tConstruct {| inductive_mind := name |} _ _ =>
          if contains name specialized then
            Err ("Unapplied '"
                   ++ string_of_kername name
                   ++ "' (or constructor) appears in term; this needs to be specialized")
          else
            ret t
        | tCase ind ret_ty disc brs =>
          ret_ty <- f Γ ret_ty;;
          disc <- f Γ disc;;
          brs <- monad_map (fun '(ar, t) => t <- f Γ t;; ret (ar, t)) brs;;
          ret (tCase ind ret_ty disc brs)
        | tProj proj body =>
          body <- f Γ body;;
          ret (tProj proj body)
        | tFix defs i =>
          let Γ := (repeat none (List.length defs) ++ Γ)%list in
          defs <- monad_map (fun (d : def term) =>
                               dtype <- f Γ (dtype d);;
                               dbody <- f Γ (dbody d);;
                               ret {| dname := dname d;
                                      dtype := dtype;
                                      dbody := dbody;
                                      rarg := rarg d |}) defs;;
          ret (tFix defs i)
        | tCoFix defs i =>
          let Γ := (repeat none (List.length defs) ++ Γ)%list in
          defs <- monad_map (fun (d : def term) =>
                               dtype <- f Γ (dtype d);;
                               dbody <- f Γ (dbody d);;
                               ret {| dname := dname d;
                                      dtype := dtype;
                                      dbody := dbody;
                                      rarg := rarg d |}) defs;;
          ret (tCoFix defs i)
        end.

    Definition specialize_body
               (specialized : list kername)
               (name : kername)
               (Γ : list VarInfo)
               (remove : bool)
               (t : term) : result term string :=
      match remove, t with
      | true, tLambda _ _ body =>
        map_error (fun s => "While specializing body in " ++ string_of_kername name ++ ": " ++ s)
                  (specialize_term specialized (replace :: Γ) body)

      | true, _ => Err ("Expected lambda in " ++ string_of_kername name ++ ", got" ++ nl ++ PUtil.string_of_term t)
      | false, _ => specialize_term specialized Γ t
      end.

    Definition specialize_type
               (specialized : list kername)
               (name : kername)
               (Γ : list VarInfo)
               (remove : bool)
               (t : term) : result term string :=
      match remove, t with
      | true, tProd _ _ body =>
        map_error (fun s => "While specializing type in " ++ string_of_kername name ++ ": " ++ s)
                  (specialize_term specialized (replace :: Γ) body)

      | true, _ => Err ("Expected product in " ++ string_of_kername name ++ ", got" ++ nl ++ PUtil.string_of_term t)
      | false, _ => specialize_term specialized Γ t
      end.

    Definition specialize_decl
               (specialized : list kername)
               (kn : kername)
               (decl : global_decl) : result (list kername * global_decl) string :=
      match decl with
      | ConstantDecl cst =>
        let remove := match cst_type cst with
                      | tProd _ (tInd ind _) _ =>
                        eq_kername (inductive_mind ind) (ChainBase_kername)
                      | _ => false
                      end in

        type <- specialize_type specialized kn [] remove (cst_type cst);;
        body <- match cst_body cst with
                | Some body => body <- specialize_body specialized kn [] remove body;;
                               ret (Some body)
                | None => ret None
                end;;

        ret (if remove then kn :: specialized else specialized,
             ConstantDecl
               {| cst_type := type;
                  cst_body := body;
                  cst_universes := cst_universes cst |})

      | InductiveDecl mib =>
        let params := rev (ind_params mib) in
        let remove := match params with
                      | {| decl_type := tInd ind _ |} :: _ =>
                        eq_kername (inductive_mind ind) ChainBase_kername
                      | _ => false
                      end in
        let go '(params, Γ) cdecl :=
            body <- match decl_body cdecl with
                    | Some body =>
                      body <- map_error (fun s => "While specializing param body of "
                                                    ++ string_of_kername kn ++ ": " ++ s)
                                        (specialize_term specialized Γ body);;
                      ret (Some body)
                    | None => ret None
                    end;;
            type <- map_error (fun s => "While specializing param type of "
                                          ++ string_of_kername kn ++ ": " ++ s)
                              (specialize_term specialized Γ (decl_type cdecl));;
            let cdecl :=
                {| decl_name := decl_name cdecl;
                   decl_body := body;
                   decl_type := type |} in
            ret (params ++ [cdecl], none :: Γ)%list in
        '(params, _) <- monad_fold_left
                          go
                          (if remove then tl params else params)
                          ([], if remove then [replace] else []);;
        let params := rev params in
        let go oib :=
            type <- specialize_type specialized (kn.1, ind_name oib) [] remove (ind_type oib);;
            (* Context with all mutually inductive types added,
             specializing them if we removed an abstraction.
             Ctors themselves will be abstracted over parameters. *)
            let ctorΓ := repeat (if remove then specialize else none)
                                (List.length (ind_bodies mib)) in
            ctors <- monad_map
                       (fun '(name, t, n) =>
                          t <- specialize_type specialized (kn.1, name) ctorΓ remove t;;
                          ret (name, t, n))
                       (ind_ctors oib);;
            (* Projections are just the type of the data value and
             checked in a context with parameters and the record value
             itself *)
            let projΓ := none :: repeat none (List.length params) in
            projs <- monad_map
                       (fun '(name, t) =>
                          t <- map_error (fun s => "While specializing projection "
                                                     ++ name ++ ": " ++ s)
                                         (specialize_term specialized projΓ t);;
                          ret (name, t))
                       (ind_projs oib);;
            ret
              {| ind_name := ind_name oib;
                 ind_type := type;
                 ind_kelim := ind_kelim oib;
                 ind_ctors := ctors;
                 ind_projs := projs; |} in
        bodies <- monad_map go (ind_bodies mib);;
        ret (if remove then kn :: specialized else specialized,
             InductiveDecl
               {| ind_finite := ind_finite mib;
                  ind_npars := List.length params;
                  ind_params := params;
                  ind_bodies := bodies;
                  ind_universes := ind_universes mib;
                  ind_variance := ind_variance mib; |})
      end.
  End ChainBaseSpecialization.

  Definition axiomatized_ChainBase_kername : kername :=
    Eval compute in kername_of_string "ConCert.Extraction.Common.axiomatized_ChainBase".

  Definition axiomatized_ChainBase_decl : global_decl :=
    ConstantDecl
      {| cst_type :=
           tInd
             {| inductive_mind := ChainBase_kername;
                inductive_ind := 0; |}
             [];
         cst_body := None;
         cst_universes := Monomorphic_ctx ContextSet.empty |}.

  (* Specialize ChainBase away in all definitions in an environment.
     Note: this will also add an axiomatized chain base to the environment. *)
  Fixpoint specialize_env_rev (Σ : global_env) : result global_env string :=
    match Σ with
    | [] => ret []
    | (name, decl) :: Σ =>
      if eq_kername name ChainBase_kername then
        let rep_term := tConst axiomatized_ChainBase_kername [] in
        let go '(specialized, newΣ) '(name, decl) :=
            '(specialized, decl) <- specialize_decl rep_term specialized name decl;;
            ret (specialized, (name, decl) :: newΣ) in
        '(_, newΣ_rev) <- monad_fold_left go Σ ([], []);;
        ret ((name, decl)
               :: (axiomatized_ChainBase_kername, axiomatized_ChainBase_decl)
               :: rev newΣ_rev)
      else
        Σ <- specialize_env_rev Σ;;
        ret ((name, decl) :: Σ)
    end.

  (* TODO: There are many reverses here, we should improve this. *)
  Definition specialize_env (Σ : global_env) : result global_env string :=
    Σrev <- specialize_env_rev (List.rev Σ);;
    ret (List.rev Σrev).
End ChainBaseSpecialization.

(* We assume well-formedness for performance reasons. Since quoted terms meant to be well-formed it is a reasonable assumption. *)
Axiom assume_env_wellformed : forall Σ, ∥PT.wf Σ∥.

(* We provide a flag to control if we want to retype the environment or just assume well-formed. *)
Definition specialize_ChainBase_and_check
           (retype : bool)
           (Σ : T.global_env) :
  result { Σ : P.global_env & ∥PT.wf Σ∥ } string :=
  let Σ := fix_global_env_universes Σ in
  let Σ := T2P.trans_global_decls Σ in
  if retype then
    G <- result_of_EnvCheck (check_wf_env_only_univs Σ);;
    ret (Σ; G.π2.p2)
  else
    Σ <- ChainBaseSpecialization.specialize_env Σ;;
    ret (Σ; assume_env_wellformed Σ).

(* Specialize, erase and debox the specified template environment
   (depending on the flags passed to the function).
   Generalization over ChainBase is first specialized away, turning
   things like

   Inductive Foo (cb : ChainBase) := ctor (addr : Address cb).
   Definition a (cb : ChainBase) (n : nat) := n.
   Definition b (cb : ChainBase) (addr : Foo cb) (n : N) :=
     a cb (N.to_nat n).

   into

   Inductive Foo := ctor (addr : Address axiomatized_ChainBase).
   Definition a (n : nat) := n.
   Definition b (addr : Foo) (n : N) :=
     a (N.to_nat n).

   After the environment has been specialized the dependencies of the
   specified seeds are recursively erased and deboxed, except for
   names for which [ignore] returns [true], whose decls are ignored. The result is
   returned in proper topological order. Assumption: the global
   environment type checks. *)
Definition general_specialize_erase_debox_template_env
           (Σ : T.global_env)
           (seeds : list kername)
           (ignore : kername -> bool)
           (retype : bool)
           (debox : bool): result ExAst.global_env string :=
  '(Σ; wfΣ) <- specialize_ChainBase_and_check retype Σ;;
  let ignored_names := filter ignore (map fst Σ) in
  Σ' <- map_error string_of_erase_global_decl_error
                 (general_erase_global_decls_deps_recursive Σ wfΣ ignore seeds) ;;
  if debox then
    ret (remove_unused_args Σ')
  else ret Σ'.

(* Like above, but takes a list of names to ignore and assumes that the environment is well-formed *)
Definition specialize_erase_debox_template_env_no_wf_check
           (Σ : T.global_env)
           (seeds : list kername)
           (ignored : list kername) : result ExAst.global_env string :=
  general_specialize_erase_debox_template_env Σ seeds (fun kn => contains kn ignored) false true.

(* Like above, but does not debox *)
Definition specialize_erase_template_env_no_wf_check
           (Σ : T.global_env)
           (seeds : list kername)
           (ignored : list kername) : result ExAst.global_env string :=
  general_specialize_erase_debox_template_env Σ seeds (fun kn => contains kn ignored) false false.

Definition ignored_concert_types :=
  Eval compute in
    map kername_of_string
        ["ConCert.Execution.Blockchain.ActionBody";
        "ConCert.Execution.Blockchain.Address";
        "ConCert.Execution.Blockchain.Amount";
        "ConCert.Execution.Blockchain.ChainBase";
        "ConCert.Execution.Blockchain.Chain";
        "ConCert.Execution.Blockchain.ContractCallContext";
        "ConCert.Execution.Serializable.SerializedValue"].

Import T.
Definition extract_def_name {A : Type} (a : A) : TemplateMonad kername :=
  a <- tmEval cbn a;;
  quoted <- tmQuote a;;
  let (head, args) := TUtil.decompose_app quoted in
  match head with
  | tConst name _ => ret name
  | _ => tmFail ("Expected constant at head, got " ++ TUtil.string_of_term head)
  end.

Record ContractExtractionSet :=
  { env : ExAst.global_env;
    init_name : kername;
    receive_name : kername; }.

Definition get_contract_extraction_set
           `{ChainBase}
           {Setup Msg State}
           `{Serializable Setup}
           `{Serializable Msg}
           `{Serializable State}
           (contract : Contract Setup Msg State) : TemplateMonad ContractExtractionSet :=
  init_name <- extract_def_name (Blockchain.init contract);;
  receive_name <- extract_def_name (Blockchain.receive contract);;
  p <- tmQuoteRec contract;;
  let seeds := [init_name; receive_name] in
  match specialize_erase_debox_template_env_no_wf_check p.1 seeds ignored_concert_types with
  | Ok Σ => ret {| env := Σ; init_name := init_name; receive_name := receive_name; |}
  | Err err => tmFail err
  end.

(** Extracts a constant name, inductive name or returns None *)
Definition to_kername (t : Ast.term) : option kername :=
  match t with
  | Ast.tConst c _ => Some c
  | Ast.tInd c _ => Some c.(inductive_mind)
  | _ => None
  end.

Definition to_kername_dummy (t : Ast.term) :  kername :=
  let dummy := (MPfile [],"") in
  match (to_kername t) with
  | Some v => v
  | None => dummy
  end.

Notation "<%% t %%>" := (to_kername_dummy <% t %>).

Definition to_string_name (t : Ast.term) : string :=
  match to_kername t with
  | Some kn => string_of_kername kn
  | None => "Not a constant or inductive"
  end.

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

(** Returns a pair of a kername (if [t] is a constant) and a new name.
 Used in a similar way as [Extract Inlined Constant] of the standard extraction *)
Definition remap (t : Ast.term) (new_name : string) :  kername * string :=
  let nm := to_kername_dummy t in
  (nm, new_name).

(** ** Validation of applied constants and constructors *)

Definition is_fully_applied_ctor (Σ : P.global_env)
           (ind : inductive)
           (ctor : nat) (n_app : nat) :=
  match PCUICChecker.lookup_constructor_decl Σ ind.(inductive_mind) ind.(inductive_ind) ctor with
  | PCUICChecker.Checked (_,_,ty) =>
    let (dom, _) :=
        PCUICAstUtils.decompose_prod ty in
    Nat.eqb n_app (List.length dom.2)
  | _ => false
  end.

Definition find_indices {A : Type}
           (f : A -> bool) : list A -> list nat :=
  let worker := fix go (i : nat) l :=
              match l with
              | [] => []
              | x :: tl =>
                if f x then i :: go (1+i)%nat tl
                else go (1+i)%nat tl
              end in
  worker 0.

Fixpoint last_option {A} (l : list A) : option A :=
  match l with
  | [] => None
  | [a] => Some a
  | a :: (_ :: _) as l0 => last_option l0
  end.

Import ExAst.

Definition is_TBox (t : box_type) : bool :=
  match t with
  | TBox => true
  | _ => false
  end.

Definition last_box_index l := last_option (find_indices is_TBox l).

Fixpoint lookup_env (Σ : P.global_env) (id : kername) : option P.global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if eq_kername id hd.1 then Some hd.2
    else lookup_env tl id
  end.

Definition lookup_ind_decl (Σ : P.global_env) ind i :=
  match lookup_env Σ ind with
  | Some (P.InductiveDecl {| P.ind_bodies := l; P.ind_universes := uctx |}) =>
    match nth_error l i with
    | Some body => Some body
    | None => None
    end
  | _ => None
  end.

Definition lookup_const (Σ : P.global_env) const :=
  match lookup_env Σ const with
  | Some (P.ConstantDecl b) => Some b
  | _ => None
  end.

Definition erase_type_to_typing_result {A} (e : erase_type_error) : typing_result A:=
  match e with
  | NotPrenex => TypeError (Msg "Not Prenex")
  | TypingError te => TypeError te
  | GeneralError msg => TypeError (Msg msg)
  end.

Program Fixpoint is_logargs_applied_const (Σ : P.global_env)
           (HΣ : ∥ PCUICTyping.wf Σ ∥)
           (const : kername) (n_app : nat) : typing_result bool :=
  match Σ with
  | (kn, P.ConstantDecl cst) :: Σ' =>
    if eq_kername kn const then
      let Σext := (Σ', universes_decl_of_decl (P.ConstantDecl cst)) in
      match erase_type Σext _ [] Vector.nil cst.(P.cst_type) _ [] with
      | ResultMonad.Ok ety =>
        let (dom, _) := decompose_arr ety.2 in
        match last_box_index dom with
        | Some i => ret (Nat.leb (i+1) n_app)
        | None => ret true
        end
      | ResultMonad.Err e => erase_type_to_typing_result e
      end
    else is_logargs_applied_const Σ' _ const n_app
  | _ :: Σ' => is_logargs_applied_const Σ' _ const n_app
  | _ => TypeError (Msg ("Constant not found: " ++ string_of_kername const))
  end.
Next Obligation. cbn;intros;subst; now sq; inversion HΣ. Qed.
Next Obligation.
  intros. sq.
  unfold lookup_const in *. subst.
  inversion HΣ;subst;cbn in *.
  unfold on_constant_decl in *.
  destruct (P.cst_body cst).
  - cbn in X0.
    eapply validity_term; [easy|exact X0].
  - cbn in X0.
    destruct X0 as (s & ?).
    right.
    now exists s.
Qed.
Next Obligation. cbn;intros;subst; now sq; inversion HΣ. Qed.
Next Obligation. cbn;intros;subst; now sq; inversion HΣ. Qed.
Next Obligation. cbn;intros;subst; now sq; inversion HΣ. Qed.
Next Obligation. cbn;intros;subst; now sq; inversion HΣ. Qed.

Program Definition test_applied_to_logargs  (p : Ast.program) (const : kername) (n_app : nat)
  : EnvCheck bool :=
  let p := fix_program_universes p in
  let Σ := (trans_global (Ast.empty_ext p.1)).1 in
  G <- check_wf_env_only_univs Σ ;;
  t <- wrap_error (P.empty_ext Σ) "during cheking applied constant" (is_logargs_applied_const (P.empty_ext Σ) _ const n_app) ;;
  ret (Monad:=envcheck_monad) t.
Next Obligation.
  intros.
  unfold PCUICTyping.wf_ext, empty_ext.
  unfold PCUICTyping.on_global_env_ext.
  destruct G as (?&H&H0). now sq.
Qed.

MetaCoq Quote Recursively Definition ex_combine := combine.

Example test_combine_true :
  (test_applied_to_logargs ex_combine (to_kername_dummy <% @combine %>) 2)
  =
  CorrectDecl true.
Proof. reflexivity. Qed.

Example test_combine_false :
  (test_applied_to_logargs ex_combine (to_kername_dummy <% @combine %>) 1)
  =
  CorrectDecl false.
Proof. reflexivity. Qed.


Definition test_fully_applied_constructor (p : Ast.program) (ind_nm : kername) (ind_i : nat) (ctor : nat) (n_app : nat) :=
  let p := fix_program_universes p in
  let Σ := (trans_global (Ast.empty_ext p.1)).1 in
  (is_fully_applied_ctor Σ (mkInd ind_nm ind_i) ctor n_app).

MetaCoq Quote Recursively Definition q_prod
  := (fun (x y : nat) => (x,y)).

Example test_pair_true :
  (test_fully_applied_constructor q_prod (to_kername_dummy <% prod %>) 0 0 4)
  = true.
Proof. reflexivity. Qed.

Example test_pair_false :
  (test_fully_applied_constructor q_prod (to_kername_dummy <% prod %>) 0 0 3)
  = false.
Proof. reflexivity. Qed.


Definition forallb_defs {A : Set} (f : A -> bool) (ds : list (E.def A)) :=
  (* this way of defining is fixpoint-firendly, i.e. is we [map] first and then apply [forallb] it fails to work with the definition below *)
  forallb (fun x => f x.(E.dbody)) ds.

Open Scope bool.

Definition check_ctors_applied (Σ : P.global_env) :=
  fix go (apps : list E.term) (t : E.term) :=
    match t with
    | E.tRel i => true
    | E.tEvar ev args => forallb (go []) args
    | E.tLambda na M => go [] M
    | E.tApp u v => (go (v :: apps) u) && (go [] v)
    | E.tLetIn na b b' => (go [] b) && (go [] b')
    | E.tCase ind c brs =>
      let brs' := forallb (fun x => go [] (snd x)) brs in
      (go [] c) && brs'
    | E.tProj p c => go [] c
    | E.tFix mfix idx =>
      forallb_defs (go []) mfix
    | E.tCoFix mfix idx =>
      forallb_defs (go []) mfix
    | E.tBox => true
    | E.tVar _ => true
    | E.tConst _ => true
    | E.tConstruct ind i =>
      is_fully_applied_ctor Σ ind i (List.length apps)
    end.

Definition check_consts_applied
  (Σ : P.global_env_ext) (HΣ : ∥ PCUICTyping.wf Σ ∥) :=
  fix go (apps : list E.term) (t : E.term) : typing_result bool:=
    match t with
    | E.tRel i => ret true
    | E.tEvar ev args =>
      res <- monad_map (go []) args ;;
      ret (forallb id res)
    | E.tLambda na M => go [] M
    | E.tApp u v =>
      b1 <- go (v :: apps) u ;;
      b2 <- go [] v ;;
      ret (b1 && b2)
    | E.tLetIn na b b' =>
      b1 <- go [] b;;
      b2 <- go [] b';;
      ret (b1 && b2)
    | E.tCase ind c brs =>
      b1 <- go [] c ;;
      res <- monad_map (fun x => go [] (snd x)) brs ;;
      ret (b1 && forallb id res)
    | E.tProj p c => go [] c
    | E.tFix mfix idx =>
      res <- monad_map (fun x => go [] (E.dbody x)) mfix ;;
      ret (forallb id res)
    | E.tCoFix mfix idx =>
      res <- monad_map (fun x => go [] (E.dbody x)) mfix ;;
      ret (forallb id res)
    | E.tBox => ret true
    | E.tVar _ => ret true
    | E.tConst nm => is_logargs_applied_const Σ HΣ nm (List.length apps)
    | E.tConstruct ind i => ret true
    end.

Program Definition check_applied
        (Σ : P.global_env)
        (wf : ∥PCUICTyping.wf Σ∥)
        (et : E.term) : EnvCheck bool :=
  is_const_applied <- wrap_error (P.empty_ext Σ) "during checking applied constant"
                                 (check_consts_applied (P.empty_ext Σ) _ [] et) ;;
  let is_constr_applied := check_ctors_applied Σ [] et in
  ret (Monad:=envcheck_monad) (andb is_const_applied is_constr_applied).
Next Obligation. auto. Qed.

Definition erase_and_check_applied (p : Ast.program) : EnvCheck bool :=
  let p := fix_program_universes p in
  let Σ := (trans_global (Ast.empty_ext p.1)).1 in
  G <- check_wf_env_only_univs Σ ;;
  et <- erase_template_program p ;;
  check_applied Σ (proj2 (projT2 G)) et.2.

Definition erase_and_check_applied_no_wf_check (p : Ast.program) : EnvCheck bool :=
  let p := fix_program_universes p in
  let Σ := (trans_global (Ast.empty_ext p.1)).1 in
  et <- erase_template_program p ;;
  check_applied Σ (assume_env_wellformed Σ) et.2.

Definition print_sum (s : string + string) :=
  match s with
  | inl s' => s'
  | inr s' => s'
  end.

Definition opt_to_template {A} (o : option A) : TemplateMonad A:=
  match o with
  | Some v => ret v
  | None => tmFail "None"
  end.

Definition EnvCheck_to_template {A } (ec : EnvCheck A) : TemplateMonad A :=
  match ec with
  | CorrectDecl a => ret a
  | EnvError Σ e => tmFail (string_of_env_error Σ e)
  end.

(* The definitions below are ment to be used ONLY when translating [ExAst.global_env] into [EAst.global_contex] for PRINTING purposes. Because in general it's not possible to recover the "standard" [EAst] representation of inductives from the data structures of [ExAst]*)
Definition trans_cst (cst : ExAst.constant_body) : EAst.constant_body :=
  {| EAst.cst_body := ExAst.cst_body cst |}.

Definition trans_oib (oib : ExAst.one_inductive_body) : EAst.one_inductive_body :=
  {| EAst.ind_name := oib.(ExAst.ind_name);
     EAst.ind_kelim := InType; (* just a "random" pick, not involved in printing *)
     EAst.ind_ctors := map (fun '(nm, _) => ((nm,EAst.tBox),0)) oib.(ExAst.ind_ctors);
     EAst.ind_projs := [] |}.

Definition trans_mib (mib : ExAst.mutual_inductive_body) : EAst.mutual_inductive_body :=
  {| EAst.ind_npars := mib.(ExAst.ind_npars);
     EAst.ind_bodies := map trans_oib mib.(ExAst.ind_bodies) |}.

Definition trans_global_decls (Σ : ExAst.global_env) : EAst.global_context :=
  let map_decl kn (decl : ExAst.global_decl) : list (kername * EAst.global_decl) :=
      match decl with
      | ExAst.ConstantDecl cst => [(kn, EAst.ConstantDecl (trans_cst cst))]
      | ExAst.InductiveDecl _ mib => [(kn, EAst.InductiveDecl (trans_mib mib))]
      | ExAst.TypeAliasDecl _ => []
      end in
  flat_map (fun '(kn, decl) => map_decl kn decl) Σ.
