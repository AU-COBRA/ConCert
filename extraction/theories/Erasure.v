From ConCert.Extraction Require Import StringExtra.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import String.
From Coq Require VectorDef.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EArities.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import Prelim.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICConfluence.
From MetaCoq.PCUIC Require Import PCUICCumulativity.
From MetaCoq.PCUIC Require Import PCUICElimination.
From MetaCoq.PCUIC Require Import PCUICGeneration.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require Import PCUICNormal.
From MetaCoq.PCUIC Require Import PCUICPrincipality.
From MetaCoq.PCUIC Require Import PCUICSN.
From MetaCoq.PCUIC Require Import PCUICSR.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICValidity.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.
From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.

Local Open Scope string_scope.
Import ListNotations.
Import MonadNotation.
Set Equations Transparent.

Module P := PCUICAst.

Section FixSigma.
Local Existing Instance extraction_checker_flags.
Context (Σ : global_env_ext).
Context (wfextΣ : ∥wf_ext Σ∥).
Let wfΣ : ∥wf Σ∥ := ltac:(now sq).


Notation term_rel := (SafeErasureFunction.term_rel Σ).
Instance WellFounded_term_rel : WellFounded term_rel :=
  (SafeErasureFunction.wf_reduction Σ wfΣ).

Definition Is_conv_to_Sort Γ T : Prop :=
  exists univ, ∥red Σ Γ T (tSort univ)∥.

(* type_flag of a term indexed by the term's type. For example, for
      t    :   T
   eq_refl : 5 = 5 : Prop
   we would pass T to flag_of_type below, and it would give
   is_logical = true, is_arity = false. On the other hand, for
   (fun (X : Type) => X) : Type -> Type
   we would pass Type -> Type and get is_logical = false, is_arity = true.
*)
Record type_flag {Γ T} :=
  build_flag
    { (* Type is proposition when fully applied, i.e. either
         (T : Prop, or T a0 .. an : Prop). If this is an arity,
         indicates whether this is a logical arity (i.e. into Prop). *)
      is_logical : bool;
      (* Term is a type scheme, i.e. type is an arity.
         T = SProp/Type/Prop or ... -> SProp/Type/Prop *)
      is_arity : {Is_conv_to_Arity Σ Γ T} + {~Is_conv_to_Arity Σ Γ T};
      (* Term is a type, i.e. type is a sort. *)
      is_sort : {Is_conv_to_Sort Γ T} + {~Is_conv_to_Sort Γ T};
    }.

Global Arguments type_flag : clear implicits.

Lemma sq_red_transitivity {Γ A} B {C} :
  ∥red Σ Γ A B∥ ->
  ∥red Σ Γ B C∥ ->
  ∥red Σ Γ A C∥ .
Proof.
  intros.
  sq.
  now transitivity B.
Qed.

Lemma isArity_red Γ u v :
  isArity u ->
  red Σ Γ u v ->
  isArity v.
Proof.
  intros arity_u red.
  induction red; [easy|].
  eapply isArity_red1; eassumption.
Qed.

Lemma Is_conv_to_Arity_red Γ T T' :
  Is_conv_to_Arity Σ Γ T ->
  ∥ red Σ Γ T T' ∥ ->
  Is_conv_to_Arity Σ Γ T'.
Proof.
  unfold Is_conv_to_Arity.
  intros [T'' (redT'' & is_arity)] red.
  sq.
  destruct (red_confluence wfΣ red redT'') as (a & reda' & reda'').
  exists a.
  split; [easy|].
  clear -is_arity reda''.
  eapply isArity_red; eauto.
Qed.

Lemma isWfArity_or_Type_prod_cod Γ na A B :
  ∥ isWfArity_or_Type Σ Γ (tProd na A B) ∥ ->
  ∥ isWfArity_or_Type Σ (Γ,, vass na A) B ∥.
Proof.
  destruct wfΣ as [wfΣu].
  intros [[ar|isT]]; constructor.
  - left.
    apply isWfArity_prod_inv in ar.
    now destruct ar as ((s & typ) & ar).
  - destruct isT as [univ typ].
    apply inversion_Prod in typ; [|easy].
    destruct typ as (? & s & ? & ? & ?).
    right.
    exists s.
    easy.
Qed.

Equations fot_discr (T : term) : Prop :=
fot_discr (tProd _ _ _) := False;
fot_discr (tSort _) := False;
fot_discr _ := True.

Inductive fot_view : term -> Type :=
| fot_view_prod na A B : fot_view (tProd na A B)
| fot_view_sort univ : fot_view (tSort univ)
| fot_view_other t : fot_discr t -> fot_view t.

Equations fot_viewc (t : term) : fot_view t :=
fot_viewc (tProd na A B) := fot_view_prod na A B;
fot_viewc (tSort univ) := fot_view_sort univ;
fot_viewc t := fot_view_other t _.

Lemma watwf {Γ T} (wat : ∥isWfArity_or_Type Σ Γ T∥) : wellformed Σ Γ T.
Proof. now apply wat_wellformed. Qed.

Opaque SafeErasureFunction.wf_reduction.
Equations(noeqns) flag_of_type (Γ : context) (T : term) (wat : ∥isWfArity_or_Type Σ Γ T∥)
  : typing_result (type_flag Γ T)
  by wf ((Γ;T; (watwf wat)) : (∑ Γ t, wellformed Σ Γ t)) term_rel :=
flag_of_type Γ T wat with inspect (hnf wfΣ Γ T (watwf wat)) :=
  | exist T is_hnf with fot_viewc T := {
    | fot_view_prod na A B with flag_of_type (Γ,, vass na A) B _ := {
      | Checked flag_cod := ret {| is_logical := is_logical flag_cod;
                                   is_arity := match is_arity flag_cod with
                                               | left isar => left _
                                               | right notar => right _
                                               end;
                                   is_sort := right _ |};
      | TypeError t := TypeError t
      };
    | fot_view_sort univ := ret {| is_logical := Universe.is_prop univ;
                                   is_arity := left _;
                                   is_sort := left _; |};
    | fot_view_other T discr with type_of Σ wfΣ _ Γ T _ := {
      | Checked (existT _ K typK) with reduce_to_sort wfΣ Γ K _ := {
        | Checked (existT _ univ red_univ) :=
          ret {| is_logical := Universe.is_prop univ;
                 is_arity := right _;
                 is_sort := right _; |};
        | TypeError t := TypeError t
        };
      | TypeError t := TypeError t
      }
    }.
Next Obligation.
  pose proof (@hnf_sound _ _ wfΣ _ _ (watwf wat)) as [red_hnf].
  apply isWfArity_or_Type_prod_cod.
  rewrite is_hnf.
  destruct wfΣ, wat.
  sq.
  eapply isWfArity_or_Type_red; [easy|exact red_hnf|easy].
Qed.
Next Obligation.
  pose proof (@hnf_sound _ _ wfΣ Γ T (watwf wat)) as [sound].
  sq.
  exists na, A.
  rewrite is_hnf.
  easy.
Qed.
Next Obligation.
  destruct isar as [Bconv [Bred Bar]].
  exists (tProd na A Bconv).
  split; [|easy].
  apply (sq_red_transitivity (tProd na A B)); [rewrite is_hnf; apply hnf_sound|].
  sq.
  now apply red_prod_alt.
Qed.
Next Obligation.
  contradiction notar.
  assert (prod_conv: Is_conv_to_Arity Σ Γ (tProd na A B)).
  { eapply Is_conv_to_Arity_red with T; [easy|].
    rewrite is_hnf.
    apply hnf_sound. }
  destruct prod_conv as [tm [[redtm] ar]].
  destruct wfΣ.
  apply invert_red_prod in redtm; [|easy].
  destruct redtm as (A' & B' & (-> & redAA') & redBB').
  exists B'; easy.
Qed.
Next Obligation.
  destruct H as [univ [red_sort]].
  pose proof (@hnf_sound _ _ wfΣ Γ T (watwf wat)) as [red_prod].
  rewrite <- is_hnf in red_prod.
  destruct wfΣ as [wfΣu].
  pose proof (red_confluence wfΣu red_sort red_prod) as (v' & redv'1 & redv'2).
  apply invert_red_sort in redv'1.
  subst.
  apply invert_red_prod in redv'2 as (? & ? & (? & ?) & ?); easy.
Qed.
Next Obligation.
  exists (tSort univ).
  split; [|easy].
  rewrite is_hnf.
  apply hnf_sound.
Qed.
Next Obligation.
  exists univ.
  rewrite is_hnf.
  apply hnf_sound.
Qed.
Next Obligation.
  case wfextΣ.
  now intros [].
Qed.
Next Obligation.
  destruct wat as [[ar|isT]].
  - (* We need to show that T is not convertible to an arity under
       the assumption that hnf of T is neither tProd nor tSort.
       To do this we will need to use some completeness fact about hnf,
       which is not proved in MetaCoq yet, so we defer this proof for now. *)
    exact (todo "not an arity because of discr").
  - destruct isT as [[]].
    now econstructor.
Qed.
Next Obligation.
  destruct typK as [typK].
  apply wat_wellformed; [easy|].
  destruct wfΣ.
  sq.
  eapply validity; [easy| |exact typK].
  now eapply typing_wf_local.
Qed.
Next Obligation.
  exact (todo "also needs discr like above").
Qed.
Next Obligation.
  exact (todo "also needs discr like above").
Qed.
Transparent SafeErasureFunction.wf_reduction.

(** OCaml-like types with boxes *)
Inductive box_type :=
| TBox
| TAny
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TVar (_ : nat) (* Index of type variable *)
| TInd (_ : inductive)
| TConst (_ : ident).

Definition redβιζ : RedFlags.t :=
  {| RedFlags.beta := true;
     RedFlags.iota := true;
     RedFlags.zeta := true;
     RedFlags.delta := false;
     RedFlags.fix_ := true;
     RedFlags.cofix_ := true |}.

Inductive term_sub_ctx : context * term -> context * term -> Type :=
| sub_prod_dom Γ na A B : term_sub_ctx (Γ, A) (Γ, tProd na A B)
| sub_prod_cod Γ na A B : term_sub_ctx (Γ,, vass na A, B) (Γ, tProd na A B)
| sub_app_arg Γ arg hd arg1 :
    In arg (decompose_app (tApp hd arg1)).2 ->
    term_sub_ctx (Γ, arg) (Γ, tApp hd arg1).

Definition erase_type_rel : Relation_Definitions.relation (∑ Γ t, wellformed Σ Γ t) :=
  fun '(Γs; ts; wfs) '(Γl; tl; wfl) =>
    ∥∑r, red Σ Γl tl r × term_sub_ctx (Γs, ts) (Γl, r)∥.

Lemma well_founded_erase_type_rel : well_founded erase_type_rel.
Proof.
  Admitted.

Instance WellFounded_erase_type_rel : WellFounded erase_type_rel :=
  Wf.Acc_intro_generator 1000 well_founded_erase_type_rel.

Lemma reduce_term_sr {Γ t red wft s} :
  s = reduce_term red Σ wfΣ Γ t wft ->
  ∥isWfArity_or_Type Σ Γ t∥ ->
  ∥isWfArity_or_Type Σ Γ s∥.
Proof.
  intros -> [wat].
  pose proof (reduce_term_sound red Σ wfΣ Γ t wft) as [redt].
  destruct wfΣ.
  sq.
  eapply isWfArity_or_Type_red; [easy|exact redt|easy].
Qed.

Lemma isWfArity_or_Type_prod_dom_eq Γ t na A B red wft :
  ∥ isWfArity_or_Type Σ Γ t ∥ ->
  tProd na A B = reduce_term red Σ wfΣ Γ t wft ->
  ∥ isWfArity_or_Type Σ Γ A ∥.
Proof.
  intros wat eq.
  pose proof (reduce_term_sr eq wat) as [wat_prod].
  clear wat eq.
  destruct wfΣ as [wfΣu].
  constructor.
  right.
  destruct wat_prod as [ar|isT].
  - apply isWfArity_prod_inv in ar.
    destruct ar as ((s & typ) & ar).
    now econstructor.
  - destruct isT as [univ typ].
    apply inversion_Prod in typ; [|easy].
    destruct typ as (s & ? & ? & ? & ?).
    exists s.
    easy.
Qed.

Lemma isWfArity_or_Type_prod_cod_eq Γ t na A B red wft :
  ∥ isWfArity_or_Type Σ Γ t ∥ ->
  tProd na A B = reduce_term red Σ wfΣ Γ t wft ->
  ∥ isWfArity_or_Type Σ (Γ,, vass na A) B ∥.
Proof.
  intros wat eq.
  pose proof (reduce_term_sr eq wat) as [wat_prod].
  clear wat eq.
  destruct wfΣ as [wfΣu].
  destruct wat_prod as [ar|isT]; constructor.
  - apply isWfArity_prod_inv in ar.
    destruct ar as ((s & typ) & ar).
    now left.
  - destruct isT as [univ typ].
    apply inversion_Prod in typ; [|easy].
    destruct typ as (? & s & ? & ? & ?).
    right.
    exists s.
    easy.
Qed.

Lemma rec_prod_dom Γ t na A B rf wft :
  tProd na A B = reduce_term rf Σ wfΣ Γ t wft ->
  ∥ ∑ r, red Σ Γ t r × term_sub_ctx (Γ, A) (Γ, r) ∥.
Proof.
  intros eq.
  pose proof (reduce_term_sound rf Σ wfΣ Γ t wft) as [red].
  sq.
  exists (tProd na A B).
  split; [rewrite eq; easy|].
  constructor.
Qed.

Lemma rec_prod_cod Γ t na A B rf wft :
  tProd na A B = reduce_term rf Σ wfΣ Γ t wft ->
  ∥ ∑ r, red Σ Γ t r × term_sub_ctx (Γ,, vass na A, B) (Γ, r) ∥.
Proof.
  intros eq.
  pose proof (reduce_term_sound rf Σ wfΣ Γ t wft) as [red].
  sq.
  exists (tProd na A B).
  split; [rewrite eq; easy|].
  constructor.
Qed.

Import VectorDef.VectorNotations.
Open Scope list.

Definition erase_app_head (t : term) : typing_result box_type :=
  match t with
  | tConst nm _ => ret (TConst nm)
  | tInd ind _ => ret (TInd ind)
  | _ => TypeError (Msg ("Unsupported head in decomposed application "
                           ++ string_of_term t))
  end.

Equations erase_type_discr (t : term) : Prop := {
  | tRel _ := False;
  | tSort _ := False;
  | tProd _ _ _ := False;
  | tApp _ _ := False;
  | tConst _ _ := False;
  | tInd _ _ := False;
  | _ := True
  }.

Inductive erase_type_view : term -> Type :=
| et_view_rel i : erase_type_view (tRel i)
| et_view_sort u : erase_type_view (tSort u)
| et_view_prod na A B : erase_type_view (tProd na A B)
| et_view_app hd arg : erase_type_view (tApp hd arg)
| et_view_const kn u : erase_type_view (tConst kn u)
| et_view_ind ind u : erase_type_view (tInd ind u)
| et_view_other t : erase_type_discr t -> erase_type_view t.

Equations erase_type_viewc (t : term) : erase_type_view t := {
  | tRel i := et_view_rel i;
  | tSort u := et_view_sort u;
  | tProd na A B := et_view_prod na A B;
  | tApp hd arg := et_view_app hd arg;
  | tConst kn u := et_view_const kn u;
  | tInd ind u := et_view_ind ind u;
  | t := et_view_other t _
  }.

Inductive tRel_kind :=
(* tRel refers to type variable n in the list of type vars *)
| rel_type_var (n : nat)
(* tRel refers to an inductive type (used in constructors of inductives) *)
| rel_inductive (ind : inductive)
(* tRel refers to something logical *)
| rel_logical
(* tRel refers to something that is not a type (for example, a
non-nullary type scheme or a value *)
| rel_nontype.

Inductive erase_type_error :=
| NotPrenex
| TypingError (te : type_error)
| GeneralError (msg : string).

Definition wrap_typing_result {A} (tr : typing_result A) : result A erase_type_error :=
  match tr with
  | Checked a => ret a
  | TypeError te => Err (TypingError te)
  end.

Opaque WellFounded_erase_type_rel SafeErasureFunction.wf_reduction.
(* Marked noeqns until we need to prove things about it to make its
definition faster *)
Equations(noeqns) erase_type
          (Γ : context)
          (erΓ : Vector.t tRel_kind (List.length Γ))
          (t : term)
          (wat : ∥isWfArity_or_Type Σ Γ t∥)
          (tvars : list name)
  : result (list name × box_type) erase_type_error
  by wf ((Γ; t; (watwf wat)) : (∑ Γ t, wellformed Σ Γ t)) erase_type_rel :=
erase_type Γ erΓ t wat tvars with inspect (reduce_term redβιζ Σ wfΣ Γ t (watwf wat)) :=
  | exist t eq_hnf with (f <- flag_of_type Γ t _;; ret (is_logical f)) := {
    | TypeError te := Err (TypingError te);

    | Checked true := ret (tvars, TBox);

    | Checked false with erase_type_viewc t := {

      | et_view_rel i with @Vector.nth_order _ _ erΓ i _ := {
        | rel_type_var n := ret (tvars, TVar n);
        | rel_inductive ind := ret (tvars, TInd ind);
        | rel_logical := ret (tvars, TBox);
        | rel_nontype := ret (tvars, TAny) (* unreachable *)
        };

      | et_view_sort _ := ret (tvars, TBox);

      | et_view_prod na A B with flag_of_type Γ A _ := {
          (* For logical things just box and proceed *)
        | Checked {| is_logical := true |} :=
          '(tvars, bt) <- erase_type (Γ,, vass na A) (rel_logical :: erΓ)%vector B _ tvars;;
          ret (tvars, TArr TBox bt);

          (* If the type isn't an arity now, then it's a "normal" type like nat. *)
        | Checked {| is_arity := right _ |} :=
          '(tvars_dom, dom) <- erase_type Γ erΓ A _ tvars;;

          (* If domain added new type vars then it is not in prenex form.
             TODO: We can probably produce something nicer by just erasing to TAny
             in this situation. *)
          (if List.length tvars <? List.length tvars_dom then
             Err NotPrenex
           else
             ret tt);;

          '(tvars, cod) <- erase_type (Γ,, vass na A) (rel_nontype :: erΓ)%vector B _ tvars;;
          ret (tvars, TArr dom cod);

        (* Ok, so it is an arity. If it is a sort then add a type variable. *)
        | Checked {| is_sort := left _ |} :=
          '(tvars, cod) <- erase_type
                             (Γ,, vass na A) (rel_type_var (List.length tvars) :: erΓ)%vector
                             B _
                             (tvars ++ [na]);;
          ret (tvars, TArr TBox cod);

        (* Finally this must be a non-nullary non-logical arity.
           This is not in prenex form. *)
        | Checked _ := Err NotPrenex;

        | TypeError te := Err (TypingError te)

        };

      | et_view_app orig_hd orig_arg with inspect (decompose_app (tApp orig_hd orig_arg)) := {
        | exist (hd, decomp_args) eq_decomp with erase_app_head hd := {
          | TypeError te := Err (TypingError te);

          | Checked hdbt :=
            let erase_arg (a : term) (i : In a decomp_args) : result box_type erase_type_error :=
                '(aT; typ) <- wrap_typing_result (type_of Σ wfΣ _ Γ a _);;
                ft <- wrap_typing_result (flag_of_type Γ aT _);;
                match ft with
                | {| is_logical := true |} => ret TBox
                | {| is_sort := left conv_sort |} =>
                  '(tvars_arg, bt) <- erase_type Γ erΓ a _ tvars;;
                  if List.length tvars <? List.length tvars_arg then
                    Err NotPrenex
                  else
                    ret bt
                | _ => ret TAny (* Arity or value *)
                end in

            let fix erase_args
                 (args : list term) (inc : incl args decomp_args)
                 (r : box_type) : result (list name * box_type) erase_type_error :=
               match args return incl args decomp_args ->
                                 result (list name * box_type) erase_type_error with
               | [] => fun _ => ret (tvars, r)
               | a :: args =>
                 fun inc =>
                 abt <- erase_arg a _;;
                 erase_args args _ (TApp r abt)
               end inc in

            erase_args decomp_args _ hdbt

          (*
          (* The code below gives a weird error *)
          where erase_args (args : list term) (inc : incl args decomp_args)
                           (result : box_type)
                : typing_result (list name * box_type) :=
          erase_args [] _ r := ret ([], r);
          (* We will fail if the arg is not a type, but let's first check to see if
             it is a logical type scheme, in which case we can get away with boxing
             it. For instance: Say we are processing [sig A P] in
               A : Type, P : A -> Prop |- sig A P : Type.
             The P argument here is not strictly a type, but is rather a type scheme.
             So we get the flag of its type, and box it. *)
          erase_args (a :: args) _ r := abt <- erase_arg a _;;
                                        erase_args args _ (TApp r abt)

          where erase_arg (a : term) (i : In a decomp_args) : typing_result box_type :=
          erase_arg a i with type_of Σ wfΣ _ Γ a _ := {
            | TypeError te := TypeError te;
            | Checked (aT; typ) with flag_of_type Γ aT _ := {
              | TypeError te := TypeError te;
              | Checked {| is_logical := true |} := ret TBox;
              (* If aT is a sort, then a is a type, so continue erasing it *)
              | Checked {| is_sort := left _ |} with erase_type Γ a _ var_map := {
                | TypeError te := TypeError te;
                | Checked ([], bt) := ret bt;
                | Checked _ := TypeError (Msg ("Type is not in prenex form"))
                };

              | Checked _ := TypeError (Msg ("Cannot erase argument; "
                                               ++ "it is not a type or logical type scheme "
                                               ++ string_of_term a))
              }
            }
          *)
          }
        };

      | et_view_const kn _ := ret (tvars, TConst kn);

      | et_view_ind ind _ := ret (tvars, TInd ind);

      | et_view_other t _ := Err (GeneralError ("Unsupported type " ++ string_of_term t))

      }
    }.
Next Obligation. now eapply reduce_term_sr. Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf wat) as [wat_rel].
  destruct wfΣ as [wfΣu].
  destruct wat_rel as [isar|(univ & typ)].
  - now destruct isar as (? & ? & ? & ?).
  - apply inversion_Rel in typ; [|easy].
    apply nth_error_Some.
    destruct typ as (? & _ & ? & _).
    congruence.
Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_dom_eq. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_cod_eq. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_cod_eq. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_dom_eq. Qed.
Next Obligation. now eapply rec_prod_dom. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_cod_eq. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation. now case wfextΣ; intros [[]]. Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf wat) as [[isar|(univ & typ)]].
  - now destruct isar as (? & ? & ? & ?).
  - unfold PCUICTypingDef.typing in typ.
    replace (tApp orig_hd orig_arg) with (mkApps hd decomp_args) in typ; cycle 1.
    { symmetry. apply decompose_app_inv.
      now rewrite <- eq_decomp. }
    destruct wfΣ as [wfΣu].
    apply type_mkApps_inv in typ; [|easy].
    destruct typ as (? & ? & (? & spine) & ?).
    clear -spine i.
    induction spine; [easy|].
    destruct i.
    + subst a.
      econstructor; easy.
    + easy.
Qed.
Next Obligation.
  destruct typ as [typ].
  destruct wfΣ.
  sq.
  eapply validity_term.
  - easy.
  - now eapply typing_wf_local.
  - exact typ.
Qed.
Next Obligation.
  destruct conv_sort as (univ & reduniv).
  destruct wfΣ as [wfΣu].
  sq.
  right.
  exists univ.
  eapply type_reduction.
  - easy.
  - now eapply typing_wf_local.
  - exact typ.
  - easy.
Qed.
Next Obligation.
  pose proof (reduce_term_sound redβιζ Σ wfΣ Γ t (watwf wat)).
  sq.
  exists (tApp orig_hd orig_arg).
  split; [rewrite eq_hnf; easy|].
  constructor.
  rewrite <- eq_decomp.
  easy.
Qed.
Next Obligation.
  now specialize (inc a (or_introl eq_refl)).
Qed.
Next Obligation.
  now specialize (inc a0 (or_intror H)).
Qed.
Transparent WellFounded_erase_type_rel SafeErasureFunction.wf_reduction.
End FixSigma.

Global Arguments is_logical {_ _ _}.
Global Arguments is_sort {_ _ _}.
Global Arguments is_arity {_ _ _}.
