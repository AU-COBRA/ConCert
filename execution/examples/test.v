(*
  Implementation of the Basic Attention Token.
  Ported from https://github.com/brave-intl/basic-attention-token-crowdsale/blob/66c886cc4bfb0493d9e7980f392ca7921ef1e7fc/contracts/BAToken.sol
*)
From Coq Require Import ZArith.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.

Import ListNotations.
Import RecordSetNotations.

Section Test.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Import Logic.Decidable.
Check decidable.

Lemma reachable_empty_state :
  reachable empty_state.
Proof.
  do 2 constructor.
Qed.

Lemma reachable_trans : forall from to,
  reachable from -> ChainTrace from to -> reachable to.
Proof.
  intros.
  inversion H.
  constructor.
  eapply ChainedList.clist_app; eauto.
Qed.

Lemma reachable_step : forall from to,
  reachable from -> ChainStep from to -> reachable to.
Proof.
  intros.
  inversion H.
  constructor.
  econstructor; eauto.
Qed.

Definition reachable_through mid to := reachable mid /\ inhabited (ChainTrace mid to).

Lemma reachable_through_refl : forall bstate,
  reachable bstate -> reachable_through bstate bstate.
Proof.
  intros.
  split; auto.
  do 2 constructor.
Qed.

Lemma reachable_through_trans' : forall from mid to,
  reachable_through from mid -> ChainStep mid to -> reachable_through from to.
Proof.
  intros.
  destruct H as [reachable [trace]].
  split; auto.
  constructor.
  econstructor; eauto.
Qed.

Lemma reachable_through_trans : forall from mid to,
  reachable_through from mid -> reachable_through mid to -> reachable_through from to.
Proof.
  intros.
  destruct H as [reachable_from [trace_from]].
  destruct H0 as [_ [trace_mid]].
  split; auto.
  constructor.
  eapply ChainedList.clist_app; eauto.
Qed.

Lemma reachable_through_step : forall from to,
  reachable from -> ChainStep from to -> reachable_through from to.
Proof.
  intros.
  apply reachable_through_refl in H.
  eapply reachable_through_trans'; eauto.
Qed.

Lemma act_decidable : forall bstate act,
  reachable bstate ->
  decidable (exists bstate' new_acts, inhabited (ActionEvaluation bstate act bstate' new_acts)).
Proof. Admitted.

Definition produces_no_new_acts act : Prop :=
  forall bstate bstate' new_acts, ActionEvaluation bstate act bstate' new_acts -> new_acts = [].

Lemma q : forall {A} (P : A -> Prop),
  ~ (exists x, P x) -> forall x, ~ (P x).
Proof.
  intros.
  intro.
  apply H.
  now exists x.
Qed.

Lemma empty_queue : forall bstate (P : Environment -> Prop),
  reachable bstate ->
  Forall act_is_from_account (chain_state_queue bstate) ->
  Forall produces_no_new_acts (chain_state_queue bstate) ->
  P bstate ->
  (forall bstate act (bstate' : ChainState) new_acts, P bstate -> inhabited (ActionEvaluation bstate act bstate' new_acts) -> P bstate' ) ->
    exists bstate', reachable_through bstate bstate' /\ P bstate' /\ (chain_state_queue bstate') = [].
Proof.
  intros.
  remember (chain_state_queue bstate).
  generalize dependent bstate.
  induction l; intros.
  - exists bstate.
    split; auto.
    now apply reachable_through_refl.
  - destruct (act_decidable bstate a); auto.
    + destruct H4 as [mid_env [new_acts [action_evaluation]]].
      pose (mid := build_chain_state mid_env (new_acts ++ l)).
      assert (step : ChainStep bstate mid).
      { eapply step_action; eauto. }
      apply Forall_inv in H1 as produces_no_acts.
      apply produces_no_acts in action_evaluation as new_acts_eq.
      subst. cbn in *.
      eapply H3 with (bstate' := mid) in H2; eauto.
      apply Forall_inv_tail in H0.
      apply Forall_inv_tail in H1.
      apply IHl in H2; eauto.
      * destruct H2 as [to [reachable_through [P_to queue_to]]].
        exists to.
        split.
        -- apply reachable_through_step in step; eauto.
           eapply reachable_through_trans; eauto.
        -- auto.
      * eapply reachable_step; eauto.
    + pose (mid := bstate<| chain_state_queue := l |>).
      assert (step : ChainStep bstate mid).
      { eapply step_action_invalid.
        -- reflexivity.
        -- eauto.
        -- eauto.
        -- now apply Forall_inv in H0.
        -- intros.
           intro.
           now apply H4.
      }
      apply Forall_inv_tail in H0.
      apply Forall_inv_tail in H1.
      apply reachable_step in step as reachable_mid; eauto.
      apply IHl in reachable_mid; eauto.
      destruct reachable_mid as [to [reachable_through [P_to queue_to]]].
      exists to.
      split.
      * apply reachable_through_step in step; eauto.
        eapply reachable_through_trans; eauto.
      * auto.
Qed.





End Test.
