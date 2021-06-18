From Coq Require Import ZArith List Lia Logic.Decidable.
Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.
From ConCert Require Import Blockchain.
Require Import Serializable.

Section BuildUtils.
Context {BaseTypes : ChainBase}.

(* The empty state is always reachable *)
Lemma reachable_empty_state :
  reachable empty_state.
Proof.
  do 2 constructor.
Qed.

(* Transitivity property of reachable and ChainTrace *)
Lemma reachable_trans : forall from to,
  reachable from -> ChainTrace from to -> reachable to.
Proof.
  intros.
  inversion H.
  constructor.
  eapply ChainedList.clist_app; eauto.
Qed.

(* Transitivity property of reachable and ChainStep *)
Lemma reachable_step : forall from to,
  reachable from -> ChainStep from to -> reachable to.
Proof.
  intros.
  inversion H.
  constructor.
  econstructor; eauto.
Qed.

(* If a state is reachable then the finalized_height cannot be larger than the chain_height *)
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

(* If a state is reachable and contract state is stored on an address 
    then that address must also have some contract deployed to it *)
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

(* If a state is reachable and contract state is stored on an address 
    then that address must be a contract address *)
Lemma contract_states_addr_format : forall to (addr : Address) (state : SerializedValue),
  reachable to ->
  env_contract_states to addr = Some state ->
  address_is_contract addr = true.
Proof.
  intros.
  apply contract_states_deployed in H0 as [wc  H0]; auto.
  eapply contract_addr_format; eauto.
Qed.

(* A state `to` is reachable through `mid` if `mid` is reachable and there exists a trace
    from `mid` to `to`. This captures that there is a valid execution ending up in `to`
    and going through the state `mid` at some point *)
Definition reachable_through mid to := reachable mid /\ inhabited (ChainTrace mid to).

(* A state is always reachable through itself *)
Lemma reachable_through_refl : forall bstate,
  reachable bstate -> reachable_through bstate bstate.
Proof.
  intros.
  split; auto.
  do 2 constructor.
Qed.

(* Transitivity property of reachable_through and ChainStep *)
Lemma reachable_through_trans' : forall from mid to,
  reachable_through from mid -> ChainStep mid to -> reachable_through from to.
Proof.
  intros.
  destruct H as [reachable [trace]].
  split; auto.
  constructor.
  econstructor; eauto.
Qed.

(* Transitivity property of reachable_through *)
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

(* Reachable_through can also be constructed from ChainStep instead of a
   ChainTrace since a ChainTrace can be constructed from a ChainStep *)
Lemma reachable_through_step : forall from to,
  reachable from -> ChainStep from to -> reachable_through from to.
Proof.
  intros.
  apply reachable_through_refl in H.
  eapply reachable_through_trans'; eauto.
Qed.

(* If a state has a contract deployed to some addr then any other state
    reachable through the first state must also have the same contract
    deployed to the same addr *)
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

(* If a state has a contract state on some addr then any other state
    reachable through the first state must also have the some contracts
    state on the same addr *)
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

(* If a state is reachable through another state then it cannot have a lower chain height *)
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

(* If a state is reachable through another state then it cannot have a lower current slot *)
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

(* If a state is reachable through another state then it cannot have a lower finalized height *)
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

(* This axiom states that for any reachable state and any contract it is
    decidable wether or there is an address where the contract can be deployed to.
   This is not provable in general with the assumption ChainBase makes about
    addresses and the function address_is_contract. However this should be
    provable in any sensible instance of ChainBase *)
Axiom deployable_address_decidable : forall bstate wc setup act_from amount,
  reachable bstate ->
  decidable (exists addr state, address_is_contract addr = true 
            /\ env_contracts bstate addr = None
            /\ wc_init wc
                  (transfer_balance act_from addr amount bstate)
                  (build_ctx act_from addr amount amount)
                  setup = Some state).

(* For any reachable state and an action it is decidable if it is
    possible to evaluate the action in the state *)
Open Scope Z_scope.
Lemma action_evaluation_decidable : forall bstate act,
  reachable bstate ->
  decidable (exists bstate' new_acts, inhabited (ActionEvaluation bstate act bstate' new_acts)).
Proof.
  intros.
  destruct act eqn:Hact.
  destruct act_body.
  - (* act_body = act_transfer to amount *)
    destruct (amount >=? 0) eqn:amount_positive.
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
    + (* Case: act_transfer is evaluable by eval_call *)
      destruct p.
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
    + (* Case: act_transfer is not evaluable by eval_call
          because wc_receive returned None *)
      right. intro.
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
    + (* Case: act_transfer is not evaluable by eval_call
          because no contract state was stored at to addr *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg; inversion H5. subst.
      congruence.
    + (* Case: act_transfer is not evaluable by eval_call
          because no contract was deployed at to addr *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg; inversion H5. subst.
      congruence.
    + (* Case: act_transfer is evaluable by eval_transfer *)
      pose (bstate' := (transfer_balance act_from to amount bstate)).
      left.
      exists bstate', [].
      constructor. eapply eval_transfer.
      * rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive. eauto.
      * rewrite Z.leb_le in balance. eauto.
      * eauto.
      * eauto.
      * constructor; reflexivity.
      * reflexivity.
    + (* Case: act_transfer is not evaluable by eval_transfer or eval_call
          because act_from does not have enough balance *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      * inversion H4. subst.
        now rewrite Z.leb_gt in balance.
      * destruct msg; inversion H5. subst.
        now rewrite Z.leb_gt in balance.
    + (* Case: act_transfer is not evaluable by eval_transfer or eval_call
          because amount was negative *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      * inversion H4. subst.
        now rewrite Z.geb_leb, Z.leb_gt in amount_positive.
      * destruct msg; inversion H5. subst.
        now rewrite Z.geb_leb, Z.leb_gt in amount_positive.
  - (* act_body = act_call to amount msg *)
    destruct (amount >=? 0) eqn:amount_positive.
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
    + (* Case: act_call is evaluable by eval_call *)
      destruct p.
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
    + (* Case: act_call is not evaluable by eval_call
          because wc_receive returned None *)
      right. intro.
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
    + (* Case: act_call is not evaluable by eval_call
          because no contract state was stored at to addr *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. now subst.
    + (* Case: act_call is not evaluable by eval_call
          because no contract was deployed at to addr *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. now subst.
    + (* Case: act_call is not evaluable by eval_call
          because act_from does not have enough balance *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. subst.
      now rewrite Z.leb_gt in balance.
    + (* Case: act_call is not evaluable by eval_call
          because amount was negative *)
       right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence.
      destruct msg0; inversion H5. subst.
      now rewrite Z.geb_leb, Z.leb_gt in amount_positive.
  - (* act_body = act_deploy amount c setup *)
    destruct (amount >=? 0) eqn:amount_positive.
    destruct (amount <=? env_account_balances bstate act_from) eqn:balance.
    apply deployable_address_decidable
      with (wc:=c) (setup:=setup) (act_from:=act_from) (amount:=amount)
      in H.
    destruct H as [[to [state [to_is_contract_addr [to_not_deployed init]]]] | no_deployable_addr].
    + (* Case: act_deploy is evaluable by eval_deploy *)
      pose (bstate' := (set_contract_state to state
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
    + (* Case: act_deploy is not evaluable by eval_deploy
          because no there is no available contract address
          that this contract can be deployed to *)
      right. intro.
      apply no_deployable_addr.
      destruct H as [bstate_new [new_acts [H]]].
      inversion H; try congruence; try (destruct msg; inversion H4).
      now exists to_addr, state.
    + (* Case: act_deploy is not evaluable by eval_deploy
          because act_from does not have enough balance *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence; try (destruct msg; inversion H5).
      inversion H5. subst.
      now rewrite Z.leb_gt in balance.
    + (* Case: act_deploy is not evaluable by eval_deploy
          because amount was negative *)
      right. intro.
      destruct H0 as [bstate_new [new_acts [H0]]].
      inversion H0; try congruence; try (destruct msg; inversion H5).
      inversion H5. subst.
      now rewrite Z.geb_leb, Z.leb_gt in amount_positive.
Qed.
Close Scope Z_scope.

(* Property stating that an action does not produce any new action when evaluated *)
Definition produces_no_new_acts act : Prop :=
  forall bstate bstate' new_acts, ActionEvaluation bstate act bstate' new_acts -> new_acts = [].

(* For any reachable state it is possible to empty the chain_state_queue
    if the queue only contains action that satisfy the following
    1) the action is from a user and not a contract
    2) the action does not produce any actions when evaluated
   For any property that holds on the starting state this also hold on
    the state with an empty queue if it can be proven that the property
    holds after evaluating any action.
*)
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
  - (* Case: queue is already empty, thus we are already done *)
    exists bstate.
    intuition.
    now apply reachable_through_refl.
  - (* Case: queue contains at least one action, 
        thus we need to either discard or evaluate it *)
    apply list.Forall_cons_1 in H0 as [H0 H0'].
    apply list.Forall_cons_1 in H1 as [H1 H1'].
    destruct (action_evaluation_decidable bstate a); auto.
    + (* Case: the action is evaluable *)
      destruct H4 as [mid_env [new_acts [action_evaluation]]].
      pose (build_chain_state mid_env (new_acts ++ l)) as mid.
      assert (step : ChainStep bstate mid) by (eapply step_action; eauto).
      apply H1 in action_evaluation as new_acts_eq.
      eapply H3 with (bstate' := mid) in H2; eauto.
      apply IHl in H2 as [to [reachable_through [P_to queue_to]]]; subst; eauto.
      * exists to.
        intuition.
        apply reachable_through_step in step; eauto.
        eapply reachable_through_trans; eauto.
      * eapply reachable_step; eauto.
    + (* Case: the action not is evaluable *)
      pose (bstate<| chain_state_queue := l |>) as mid.
      assert (step : ChainStep bstate mid).
      { eapply step_action_invalid; try easy.
        intros. apply H4.
        now do 2 eexists.
      }
      apply reachable_step in step as reachable_mid; eauto.
      apply IHl in reachable_mid as [to [reachable_through [P_to queue_to]]]; eauto.
      exists to.
      intuition.
      apply reachable_through_step in step; eauto.
      eapply reachable_through_trans; eauto.
Qed.

End BuildUtils.
