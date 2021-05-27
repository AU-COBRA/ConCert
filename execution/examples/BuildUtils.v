From Coq Require Import ZArith List Lia Logic.Decidable.
Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.
From ConCert Require Import Blockchain.
Require Import Serializable.

Section BuildUtils.
Context {BaseTypes : ChainBase}.

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

Lemma finalized_heigh_chain_height : forall bstate,
  reachable bstate ->
  finalized_height bstate < S (chain_height bstate).
Proof.
  intros.
  destruct H as [H].
  remember empty_state.
  induction H as [ | H from to trace IH step ]; subst.
  - apply Nat.lt_0_1.
  - destruct_chain_step. (*inversion step as [ header _ valid_block _ env_eq | act _ new_acts _ eval _ | eq ].*)
    + inversion valid_header. now rewrite_environment_equiv.
    + inversion eval; rewrite_environment_equiv; now apply IH.
    + rewrite_environment_equiv. now apply IH.
    + inversion prev_next. now apply IH.
Qed.

Lemma contract_states_deployed : forall to (addr : Address) (state : SerializedValue),
  reachable to ->
  env_contract_states to addr = Some state ->
  exists wc, env_contracts to addr = Some wc.
Proof.
  intros.
  destruct H as [trace].
  generalize dependent state.
  remember empty_state.
  induction trace; intros.
  - subst. cbn in H0. congruence.
  - destruct_chain_step;
      try inversion eval; subst;
      (rewrite_environment_equiv || rewrite <- env_eq in * || rewrite prev_next in *);
      try (apply IHtrace in H0 as [wc H0]; auto; exists wc; (now rewrite_environment_equiv || assumption));
      clear H5; cbn in *; destruct_address_eq; subst;
      ((apply IHtrace in H0 as [wc_new H0]; auto; exists wc_new) || exists wc);
      rewrite_environment_equiv; cbn; destruct_address_eq; try easy.
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

Lemma reachable_through_contract_deployed : forall from to addr wc,
  reachable_through from to -> env_contracts from addr = Some wc ->
    env_contracts to addr = Some wc.
Proof.
  intros.
  destruct H as [reachable [trace]].
  induction trace.
  - assumption.
  - destruct_chain_step; try inversion eval;
      (rewrite_environment_equiv || inversion prev_next); 
      try (apply IHtrace; assumption).
    + cbn. destruct_address_eq; auto.
      subst. rewrite IHtrace in H3; auto.
      congruence.
Qed.

Lemma reachable_through_contract_state : forall from to addr cstate,
  reachable_through from to -> env_contract_states from addr = Some cstate ->
    exists new_cstate, env_contract_states to addr = Some new_cstate.
Proof.
  intros.
  generalize dependent cstate.
  destruct H as [reachable [trace]].
  induction trace; intros.
  - exists cstate. assumption.
  - destruct_chain_step;
      try inversion eval; apply IHtrace in H0 as [new_cstate H0]; auto;
      try (exists new_cstate; (rewrite_environment_equiv || inversion prev_next); cbn; assumption).
    + exists new_cstate.
      rewrite_environment_equiv. cbn.
      destruct_address_eq; auto. subst.
      apply contract_states_deployed in H0 as [wc' H0].
      -- congruence.
      -- eapply reachable_trans; eauto.
    + destruct (address_eqb addr to_addr) eqn:address_eq; 
        [exists new_state | exists new_cstate];
        rewrite_environment_equiv; cbn; destruct_address_eq; easy.
Qed.

Lemma reachable_through_chain_height : forall from to,
  reachable_through from to -> from.(chain_height) <= to.(chain_height).
Proof.
  intros.
  destruct H as [reachable [trace]].
  induction trace.
  - auto.
  - destruct_chain_step;
      try inversion eval;
      try now (rewrite_environment_equiv || inversion prev_next).
    + rewrite_environment_equiv.
      inversion valid_header. now cbn.
Qed.

Lemma reachable_through_current_slot : forall from to,
  reachable_through from to -> from.(current_slot) <= to.(current_slot).
Proof.
  intros.
  destruct H as [reachable [trace]].
  induction trace.
  - auto.
  - destruct_chain_step;
      try inversion eval;
      try now (rewrite_environment_equiv || inversion prev_next).
    + rewrite_environment_equiv.
      inversion valid_header. now cbn.
Qed.

Lemma reachable_through_finalized_height : forall from to,
  reachable_through from to -> from.(finalized_height) <= to.(finalized_height).
Proof.
  intros.
  destruct H as [reachable [trace]].
  induction trace.
  - auto.
  - destruct_chain_step;
      try inversion eval;
      try now (rewrite_environment_equiv || inversion prev_next).
    + rewrite_environment_equiv.
      inversion valid_header. now cbn.
Qed.

Axiom deployable_address_decidable : forall bstate wc setup act_from amount,
  reachable bstate ->
  decidable (exists addr state, address_is_contract addr = true 
            /\ env_contracts bstate addr = None
            /\ wc_init wc
                  (transfer_balance act_from addr amount bstate)
                  (build_ctx act_from addr amount amount)
                  setup = Some state).

Open Scope Z_scope.
Lemma action_evaluation_decidable : forall bstate act,
  reachable bstate ->
  decidable (exists bstate' new_acts, inhabited (ActionEvaluation bstate act bstate' new_acts)).
Proof.
  intros.
  destruct act eqn:Hact.
  destruct act_body.
  - destruct (amount >=? 0) eqn:amount_positive.
    destruct (amount <=? env_account_balances bstate act_from) eqn:balance.
    destruct (address_is_contract to) eqn:to_is_contract.
    destruct (env_contracts bstate to) eqn:to_contract.
    destruct (env_contract_states bstate to) eqn:contract_state.
    pose (new_to_balance := if (address_eqb act_from to)
                         then (env_account_balances bstate to)
                         else (env_account_balances bstate to) + amount).
    destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_from to new_to_balance amount)
        s None) eqn:receive.
    + destruct p.
      pose (bstate' := (set_contract_state to s0
                       (transfer_balance act_from to amount bstate))).
      left.
      exists bstate', (map (build_act to) l).
      constructor. eapply eval_call with (msg := None).
      * rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive. eauto.
      * rewrite Z.leb_le in balance. eauto.
      * eauto.
      * eauto.
      * reflexivity.
      * assert (new_to_balance_eq : env_account_balances bstate' to = new_to_balance).
        { cbn. unfold new_to_balance; destruct_address_eq; try congruence; lia. }
        rewrite <- new_to_balance_eq in receive. eauto.
      * reflexivity.
      * constructor; reflexivity.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg; inversion H5. subst.
      assert (new_to_balance_eq : env_account_balances bstate_new to_addr =
                                  new_to_balance).
      { inversion H8.
        rewrite account_balances_eq.
        unfold new_to_balance. cbn.
        destruct_address_eq; try congruence; subst; lia.
      }
      now rewrite <- new_to_balance_eq in receive.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg; inversion H5. subst.
      congruence.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg; inversion H5. subst.
      congruence.
    + pose (bstate' := (transfer_balance act_from to amount bstate)).
      left.
      exists bstate', [].
      constructor. eapply eval_transfer.
      * rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive. eauto.
      * rewrite Z.leb_le in balance. eauto.
      * eauto.
      * eauto.
      * constructor; reflexivity.
      * reflexivity.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      * inversion H4. subst.
        now rewrite Z.leb_gt in balance.
      * destruct msg; inversion H5. subst.
        now rewrite Z.leb_gt in balance.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      * inversion H4. subst.
        now rewrite Z.geb_leb, Z.leb_gt in amount_positive.
      * destruct msg; inversion H5. subst.
        now rewrite Z.geb_leb, Z.leb_gt in amount_positive.
  - destruct (amount >=? 0) eqn:amount_positive.
    destruct (amount <=? env_account_balances bstate act_from) eqn:balance.
    destruct (env_contracts bstate to) eqn:contract.
    destruct (env_contract_states bstate to) eqn:contract_state.
    pose (new_to_balance := if (address_eqb act_from to)
                         then (env_account_balances bstate to)
                         else (env_account_balances bstate to) + amount).
    destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_from to new_to_balance amount)
        s (Some msg)) eqn:receive.
    + destruct p.
      pose (bstate' := (set_contract_state to s0
                       (transfer_balance act_from to amount bstate))).
      left.
      exists bstate', (map (build_act to) l).
      constructor. eapply eval_call with (msg0 := Some msg).
      * rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive. eauto.
      * rewrite Z.leb_le in balance. eauto.
      * eauto.
      * eauto.
      * reflexivity.
      * assert (new_to_balance_eq : env_account_balances bstate' to = new_to_balance).
        { cbn. unfold new_to_balance; destruct_address_eq; try congruence; lia. }
        rewrite <- new_to_balance_eq in receive. eauto.
      * reflexivity.
      * constructor; reflexivity.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. subst.
      assert (new_to_balance_eq : env_account_balances bstate_new to_addr =
                                  new_to_balance).
      { inversion H8.
        rewrite account_balances_eq.
        unfold new_to_balance. cbn.
        destruct_address_eq; try congruence; subst; lia.
      }
      now rewrite <- new_to_balance_eq in receive.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. now subst.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. now subst.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. subst.
      now rewrite Z.leb_gt in balance.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. subst.
      now rewrite Z.geb_leb, Z.leb_gt in amount_positive.
  - destruct (amount >=? 0) eqn:amount_positive.
    destruct (amount <=? env_account_balances bstate act_from) eqn:balance.
    apply deployable_address_decidable
      with (wc:=c) (setup:=setup) (act_from:=act_from) (amount:=amount)
      in H.
    destruct H as [[to [state [to_is_contract_addr [to_not_deployed init]]]] | no_deployable_addr].
    + pose (bstate' := (set_contract_state to state
                       (add_contract to c
                       (transfer_balance act_from to amount bstate)))).
      left.
      exists bstate', [].
      constructor. eapply eval_deploy.
      * rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive. eauto.
      * rewrite Z.leb_le in balance. eauto.
      * eauto.
      * eauto.
      * reflexivity.
      * eauto.
      * constructor; reflexivity.
      * reflexivity.
    + right. intro.
      apply no_deployable_addr.
      destruct H as [bstate_new [new_acts [H]]].
      inversion H; try congruence; try (destruct msg; inversion H4).
      now exists to_addr, state.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence; try (destruct msg; inversion H5).
      inversion H5. subst.
      now rewrite Z.leb_gt in balance.
    + right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence; try (destruct msg; inversion H5).
      inversion H5. subst.
      now rewrite Z.geb_leb, Z.leb_gt in amount_positive.
Qed.
Close Scope Z_scope.

Definition produces_no_new_acts act : Prop :=
  forall bstate bstate' new_acts, ActionEvaluation bstate act bstate' new_acts -> new_acts = [].

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
  - destruct (action_evaluation_decidable bstate a); auto.
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

End BuildUtils.
