From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import String.
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
From MetaCoq.PCUIC Require Import PCUICInversion.
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

Section fix_sigma.
Local Existing Instance extraction_checker_flags.
Context (Σ : global_env_ext).
Context (wfextΣ : ∥wf_ext Σ∥).
Let wfΣ : ∥wf Σ∥ := ltac:(now sq).

Notation term_rel := (SafeErasureFunction.term_rel Σ).
Instance WellFounded_term_rel : WellFounded term_rel :=
  (SafeErasureFunction.wf_reduction Σ wfΣ).

Check (fun X : Type => X).
(* Flag of a term indexed by the term's type. For example, for
      t    :   T
   eq_refl : 5 = 5 : Prop
   we would pass T to flag_of_type below, and it would give
   is_logical = true, is_arity = false. On the other hand, for
   (fun (X : Type) => X) : Type -> Type
   we would pass Type -> Type and get is_logical = false, is_arity = true.
*)
Record Flag {Γ T} :=
  build_flag
    { (* Term is a proof when fully applied, i.e. either
         (t : T : Prop, or t a0 .. an : Prop) *)
      is_logical : bool;
      (* Term is a type scheme, i.e. T = SProp/Type/Prop or iterated product *)
      is_arity : {Is_conv_to_Arity Σ Γ T} + {~Is_conv_to_Arity Σ Γ T};
    }.

Global Arguments Flag : clear implicits.

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

Equations fot_discr (T : term) : Prop :=
fot_discr (tProd _ _ _) := False;
fot_discr (tSort _) := False;
fot_discr _ := True.

Inductive FotView : term -> Type :=
| fot_view_prod na A B : FotView (tProd na A B)
| fot_view_sort univ : FotView (tSort univ)
| fot_view_other t : fot_discr t -> FotView t.

Equations fot_viewc (t : term) : FotView t :=
fot_viewc (tProd na A B) := fot_view_prod na A B;
fot_viewc (tSort univ) := fot_view_sort univ;
fot_viewc t := fot_view_other t _.

Opaque SafeErasureFunction.wf_reduction.
Equations flag_of_type
          (Γ : context) (wfΓ : ∥wf_local Σ Γ∥)
          (T : term) (wtT : welltyped Σ Γ T)
  : typing_result (Flag Γ T)
  by wf ((Γ;T; or_introl wtT) : (∑ Γ t, wellformed Σ Γ t)) term_rel :=
flag_of_type Γ wfΓ T wtT with inspect (hnf wfΣ Γ T (or_introl wtT)) :=
  | exist T is_hnf with fot_viewc T := {
    | fot_view_prod na A B with flag_of_type (Γ,, vass na A) _ B _ := {
      | Checked flag_cod := ret {| is_logical := is_logical flag_cod;
                                   is_arity := _ |};
      | TypeError t := TypeError t
      };
    | fot_view_sort univ := ret {| is_logical := Universe.is_prop univ;
                                   is_arity := left _; |};
    | fot_view_other T discr with type_of Σ wfΣ _ Γ T _ := {
      | Checked (existT _ K typK) with reduce_to_sort wfΣ Γ K _ := {
        | Checked (existT _ univ _) :=
          ret {| is_logical := Universe.is_prop univ;
                 is_arity := right _; |};
        | TypeError t := TypeError t
        };
      | TypeError t := TypeError t
      }
    }.
Next Obligation.
  pose proof (@hnf_sound _ _ wfΣ Γ T (or_introl wtT)) as [sound].
  rewrite <- is_hnf in sound.
  assert (wt: welltyped Σ Γ (tProd na A B)) by (eapply red_welltyped; easy).
  destruct wt as [? typ].
  destruct wfΣ.
  apply inversion_Prod in typ as (s & _ & Hs & _); [|easy].
  now sq; apply wf_local_vass with s.
Qed.
Next Obligation.
  enough (wtprod: welltyped Σ Γ (tProd na A B)).
  { destruct wtprod as [? wtprod].
    destruct wfΣ.
    apply inversion_Prod in wtprod as (? & ? & ? & ? & ?); [|easy].
    econstructor.
    easy. }
  rewrite is_hnf.
  apply red_welltyped with T; [easy|easy|].
  apply hnf_sound.
Qed.
Next Obligation.
  pose proof (@hnf_sound _ _ wfΣ Γ T (or_introl wtT)) as [sound].
  sq.
  exists na, A.
  rewrite is_hnf.
  easy.
Qed.
Next Obligation.
  destruct flag_cod as [logical [ar|not_ar]].
  - left.
    destruct ar as [Bconv [Bred Bar]].
    exists (tProd na A Bconv).
    split; [|easy].
    apply (sq_red_transitivity (tProd na A B)); [rewrite is_hnf; apply hnf_sound|].
    sq.
    now apply red_prod_alt.
  - right.
    intros is_conv.
    contradiction not_ar.
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

Lemma is_type_scheme_spec Γ wfΓ T wtT f :
  flag_of_type Γ wfΓ T wtT = Checked f ->
  is_type_scheme f ->
  {Is_conv_to_Arity Σ Γ T} + {~Is_conv_to_Arity Σ Γ T}.
Proof.
  intros checks ts.
  funelim (flag_of_type Γ wfΓ T wtT).
  -
