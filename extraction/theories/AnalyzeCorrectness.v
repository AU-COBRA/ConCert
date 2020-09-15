From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From Coq Require Import Arith.
From Coq Require Import Btauto.
From Coq Require Import Bool.
From Coq Require Import List.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Template Require Import utils.
Import ListNotations.
Open Scope bool.

Lemma nth_clear_bit_eq k bs :
  nth k (clear_bit k bs) false = false.
Proof.
  revert bs.
  induction k as [|k IH]; intros bs; cbn in *.
  - now destruct bs.
  - now destruct bs.
Qed.

Lemma nth_clear_bit_neq k k' bs :
  k <> k' ->
  nth k (clear_bit k' bs) false = nth k bs false.
Proof.
  revert bs k'.
  induction k as [|k IH]; intros bs k' ne.
  - destruct k'; [easy|].
    now destruct bs.
  - destruct k'.
    + destruct bs; [|easy].
      now destruct k.
    + destruct bs; [easy|].
      cbn.
      now apply IH.
Qed.

Lemma nth_bitmask_or k bs1 bs2 :
  nth k (bs1 #|| bs2) false = nth k bs1 false || nth k bs2 false.
Proof.
  revert bs1 bs2.
  induction k; intros bs1 bs2.
  + cbn.
    destruct bs1, bs2; try easy.
    cbn.
    btauto.
  + destruct bs1, bs2; try easy.
    * cbn in *.
      btauto.
    * cbn in *.
      easy.
Qed.

Lemma nth_tl {A} k (l : list A) d :
  nth k (tl l) d = nth (S k) l d.
Proof.
  destruct l.
  - now destruct k.
  - easy.
Qed.

Lemma nth_dead_context_vars k bs t :
  nth k (dead_context_vars bs t) false = nth k bs false && is_dead k t.
Proof.
  revert k bs.
  induction t using term_forall_list_ind; intros k bs; cbn in *; auto; try btauto.
  - destruct (Nat.eqb_spec n k) as [->|].
    + now rewrite nth_clear_bit_eq; btauto.
    + rewrite nth_clear_bit_neq by easy.
      now btauto.
  - revert k bs.
    induction H; intros k bs; cbn.
    + now btauto.
    + rewrite H, IHForall.
      now btauto.
  - now rewrite nth_tl, IHt.
  - rewrite nth_tl.
    rewrite IHt2.
    cbn.
    rewrite IHt1.
    now btauto.
  - rewrite IHt2, IHt1.
    now btauto.
  - induction X; cbn in *.
    + rewrite IHt.
      now btauto.
    + rewrite p0, IHX.
      now btauto.
  - rewrite nth_nth_error, nth_error_skipn, <- nth_nth_error.
    generalize #|m|.
    intros.
    induction H; cbn in *.
    + rewrite app_nth2; rewrite repeat_length; [|easy].
      rewrite minus_plus.
      now btauto.
    + rewrite H, IHForall.
      now btauto.
  - rewrite nth_nth_error, nth_error_skipn, <- nth_nth_error.
    generalize #|m|.
    intros.
    induction H; cbn in *.
    + rewrite app_nth2; rewrite repeat_length; [|easy].
      rewrite minus_plus.
      now btauto.
    + rewrite H, IHForall.
      now btauto.
Qed.

Lemma hd_nth {A} d (l : list A) :
  hd d l = nth 0 l d.
Proof. now destruct l. Qed.

Lemma func_body_dead_params_valid_mask dead_before t ty mask dead_after :
  func_body_dead_params dead_before t ty = (mask, dead_after) ->
  dead_after = dead_context_vars dead_before t /\ valid_dearg_mask mask t.
Proof.
  revert dead_before ty mask dead_after.
  induction t using term_forall_list_ind;
    intros dead_before ty mask dead_after fun_eq;
    cbn in *;
    try solve [now noconf fun_eq].
  - destruct ty; try solve [now noconf fun_eq].
    destruct (func_body_dead_params _ _ _) eqn:fun_eq'.
    noconf fun_eq.
    apply IHt in fun_eq' as (-> & valid).
    split; [easy|].
    propify.
    split; [|easy].
    destruct (hd _ _) eqn:hd_eq; [|easy].
    rewrite hd_nth in hd_eq.
    now rewrite nth_dead_context_vars in hd_eq.
  - destruct (func_body_dead_params _ _ _) eqn:fun_eq'.
    noconf fun_eq.
    now apply IHt2 in fun_eq'.
Qed.
