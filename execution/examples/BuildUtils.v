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

Hint Resolve reachable_empty_state
             reachable_trans
             reachable_step : core.

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
  now eapply ChainedList.clist_app.
Qed.

(* Reachable_through can also be constructed from ChainStep instead of a
   ChainTrace since a ChainTrace can be constructed from a ChainStep *)
Lemma reachable_through_step : forall from to,
  reachable from -> ChainStep from to -> reachable_through from to.
Proof.
  intros.
  apply reachable_through_refl in H.
  now eapply reachable_through_trans'.
Qed.

(* Any ChainState that is reachable through another ChainState is reachable *)
Lemma reachable_through_reachable : forall from to,
  reachable_through from to -> reachable to.
Proof.
  intros.
  destruct H as [[trace_from] [trace_to]].
  constructor.
  now eapply ChainedList.clist_app.
Qed.

Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

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

Ltac action_not_decidable :=
  right; intro;
  match goal with
  | H : exists bstate new_acts, inhabited (ActionEvaluation _ _ bstate new_acts) |- False =>
    destruct H as [bstate_new [new_acts [H]]];
    inversion H; try congruence
  end; repeat
  match goal with
  | H : {| act_from := _; act_body := _ |} = {| act_from := _; act_body := match ?msg with | Some _ => _ | None =>_ end |} |- False =>
    destruct msg
  | H : {| act_from := _; act_body := _ |} = {| act_from := _; act_body := _ |} |- False =>
    inversion H; subst; clear H
  end.

Ltac action_decidable :=
  left; do 2 eexists; constructor;
  match goal with
  | H : wc_receive _ _ _ _ ?m = Some _ |- _ => eapply (eval_call _ _ _ _ m)
  | H : wc_init _ _ _ _ = Some _ |- _ => eapply eval_deploy
  | H : context [act_transfer _ _] |- _ => eapply eval_transfer
  end;
  eauto; try now constructor.

Ltac rewrite_balance :=
  match goal with
  | H := context [if (_ =? ?to)%address then _ else _ ],
    H2 : Environment |- _ =>
    assert (new_to_balance_eq : env_account_balances H2 to = H);
    [ try rewrite_environment_equiv; cbn; unfold H; destruct_address_eq; try congruence; lia |
    now rewrite <- new_to_balance_eq in *]
  end.

(* For any reachable state and an action it is decidable if it is
    possible to evaluate the action in the state *)
Open Scope Z_scope.
Lemma action_evaluation_decidable : forall bstate act,
  reachable bstate ->
  decidable (exists bstate' new_acts, inhabited (ActionEvaluation bstate act bstate' new_acts)).
Proof.
  intros.
  destruct act eqn:Hact.
  destruct act_body;
    (destruct (amount >=? 0) eqn:amount_positive;
    [destruct (amount <=? env_account_balances bstate act_from) eqn:balance |
      action_not_decidable; now rewrite Z.geb_leb, Z.leb_gt in amount_positive (* Eliminate cases where amount is negative *)];
    [| action_not_decidable; now rewrite Z.leb_gt in balance ]); (* Eliminate cases where sender does not have enough balance *)
  try (destruct (address_is_contract to) eqn:to_is_contract;
    [destruct (env_contracts bstate to) eqn:to_contract;
    [destruct (env_contract_states bstate to) eqn:contract_state |] |]);
  try now action_not_decidable. (* Eliminate cases with obvious contradictions *)
  all : rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive.
  all : rewrite Z.leb_le in balance.
  - (* act_body = act_transfer to amount *)
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
      action_decidable.
      rewrite_balance.
    + (* Case: act_transfer is not evaluable by eval_call
          because wc_receive returned None *)
      action_not_decidable.
      rewrite_balance.
  - (* act_body = act_transfer to amount *)
    (* Case: act_transfer is evaluable by eval_transfer *)
    pose (bstate' := (transfer_balance act_from to amount bstate)).
    action_decidable.
  - (* act_body = act_call to amount msg *)
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
      action_decidable.
      rewrite_balance.
    + (* Case: act_call is not evaluable by eval_call
          because wc_receive returned None *)
      action_not_decidable.
      rewrite_balance.
  - (* act_body = act_call to amount msg *)
    (* Case: contradiction *)
    action_not_decidable.
    now apply contract_addr_format in H3; auto.
  - (* act_body = act_deploy amount c setup *)
    apply deployable_address_decidable
      with (wc:=c) (setup:=setup) (act_from:=act_from) (amount:=amount)
      in H.
    destruct H as [[to [state [to_is_contract_addr [to_not_deployed init]]]] | no_deployable_addr].
    + (* Case: act_deploy is evaluable by eval_deploy *)
      pose (bstate' := (set_contract_state to state
                       (add_contract to c
                       (transfer_balance act_from to amount bstate)))).
      action_decidable.
    + (* Case: act_deploy is not evaluable by eval_deploy
          because no there is no available contract address
          that this contract can be deployed to *)
      action_not_decidable.
      apply no_deployable_addr.
      eauto.
Qed.
Close Scope Z_scope.

(* Property stating that an action does not produce any new action when evaluated *)
Definition produces_no_new_acts act : Prop :=
  forall bstate bstate' new_acts, ActionEvaluation bstate act bstate' new_acts -> new_acts = [].

Definition emptyable queue : Prop :=
  Forall act_is_from_account queue /\
  Forall produces_no_new_acts queue.

Lemma empty_queue_is_emptyable : emptyable [].
Proof.
  now constructor.
Qed.

Lemma emptyable_cons : forall x l,
  emptyable (x :: l) -> emptyable l.
Proof.
  intros x l [H H1].
  apply Forall_inv_tail in H.
  apply Forall_inv_tail in H1.
  now constructor.
Qed.

(* For any reachable state it is possible to empty the chain_state_queue
    if the queue only contains action that satisfy the following
    1) the action is from a user and not a contract
    2) the action does not produce any actions when evaluated
   For any property that holds on the starting state this also hold on
    the state with an empty queue if it can be proven that the property
    holds after evaluating any action.
*)
Lemma empty_queue : forall bstate (P : ChainState -> Prop),
  reachable bstate ->
  emptyable (chain_state_queue bstate) ->
  P bstate ->
  (forall (bstate bstate' : ChainState) act acts, reachable bstate -> reachable bstate' -> P bstate ->
    chain_state_queue bstate = act :: acts -> chain_state_queue bstate' = acts ->
    (inhabited (ActionEvaluation bstate act bstate' []) \/ EnvironmentEquiv bstate bstate') -> P bstate' ) ->
    exists bstate', reachable_through bstate bstate' /\ P bstate' /\ (chain_state_queue bstate') = [].
Proof.
  intros.
  destruct H0 as [H0 H3].
  remember (chain_state_queue bstate).
  generalize dependent bstate.
  induction l; intros.
  - (* Case: queue is already empty, thus we are already done *)
    exists bstate.
    intuition.
  - (* Case: queue contains at least one action, 
        thus we need to either discard or evaluate it *)
    apply list.Forall_cons_1 in H0 as [H0 H0'].
    apply list.Forall_cons_1 in H3 as [H3 H3'].
    destruct (action_evaluation_decidable bstate a); auto.
    + (* Case: the action is evaluable *)
      destruct H4 as [mid_env [new_acts [action_evaluation]]].
      pose (build_chain_state mid_env (new_acts ++ l)) as mid.
      assert (step : ChainStep bstate mid) by (eapply step_action; eauto).
      apply H3 in action_evaluation as new_acts_eq.
      eapply H2 with (bstate' := mid) in H1; eauto.
      subst.
      apply IHl in H1 as [to [reachable_through [P_to queue_to]]]; subst; eauto.
      exists to.
      intuition.
      eauto.
      now subst.
      now subst.
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
      eauto.
      eapply (H2 bstate mid); eauto.
      now right.
Qed.

Lemma wc_receive_to_receive : forall {Setup Msg State : Type}
                                    `{Serializable Setup}
                                    `{Serializable Msg}
                                    `{Serializable State}
                                    (contract : Contract Setup Msg State)
                                    chain cctx cstate msg new_cstate new_acts,
  contract.(receive) chain cctx cstate (Some msg) = Some (new_cstate, new_acts) <->
  wc_receive contract chain cctx ((@serialize State _) cstate) (Some ((@serialize Msg _) msg)) = Some ((@serialize State _) new_cstate, new_acts).
Proof.
  split; intros.
  - cbn.
    rewrite 2!deserialize_serialize.
    now rewrite H2.
  - apply wc_receive_strong in H2.
    destruct H2 as [a [b [c [H3 [H4 [H5 H6]]]]]].
    apply serialize_injective in H5. subst.
    rewrite deserialize_serialize in H3.
    inversion H3. subst.
    destruct b eqn:Hmsg.
    + cbn in H4.
      now rewrite deserialize_serialize in H4.
    + inversion H4.
Qed.

Open Scope Z_scope.
Lemma add_block : forall bstate reward creator acts slot_incr,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  address_is_contract creator = false ->
  reward >= 0->
  (slot_incr > 0)%nat ->
  Forall act_is_from_account acts ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        (add_new_block_to_env {| block_height := S (chain_height bstate);
          block_slot := current_slot bstate + slot_incr;
          block_finalized_height := finalized_height bstate;
          block_creator := creator;
          block_reward := reward; |} bstate)).
Proof.
  intros.
  pose (header := 
    {| block_height := S (chain_height bstate);
       block_slot := current_slot bstate + slot_incr;
       block_finalized_height := finalized_height bstate;
       block_creator := creator;
       block_reward := reward; |}).
  pose (bstate_with_acts := (bstate<|chain_state_queue := acts|>
                                   <|chain_state_env := add_new_block_to_env header bstate|>)).
  assert (step_with_acts : ChainStep bstate bstate_with_acts).
  { eapply step_block; try easy.
    - constructor; try easy.
      + cbn. lia.
      + split; try (cbn; lia). cbn.
        now apply finalized_heigh_chain_height.
  }
  exists bstate_with_acts.
  split; eauto.
  split; eauto.
  constructor; try reflexivity.
Qed.

Lemma forward_time : forall bstate reward creator slot,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  address_is_contract creator = false ->
  reward >= 0 ->
    (exists bstate' header,
       reachable_through bstate bstate'
    /\ (slot <= current_slot bstate')%nat
    /\ chain_state_queue bstate' = []
    /\ EnvironmentEquiv
        bstate'
        (add_new_block_to_env header bstate)).
Proof.
  intros.
  destruct (slot - current_slot bstate)%nat eqn:H3.
  - apply NPeano.Nat.sub_0_le in H3.
    exists bstate.
    exists {| block_height := chain_height bstate;
       block_slot := current_slot bstate;
       block_finalized_height := finalized_height bstate;
       block_creator := creator;
       block_reward := 0; |}.
    split; eauto.
    split; eauto.
    split; eauto.
    constructor; eauto.
    + destruct bstate.
      destruct chain_state_env.
      destruct env_chain.
      reflexivity.
    + intro.
      cbn.
      now destruct_address_eq.
  - eapply add_block with (slot_incr := S n) in H1; try easy.
    destruct H1 as [bstate_with_act [reach [queue env_eq]]].
    do 2 eexists.
    split; eauto.
    split; eauto.
    rewrite_environment_equiv.
    cbn.
    lia.
Qed.

Lemma evaluate_action : forall {Setup Msg State : Type}
                              `{Serializable Setup}
                              `{Serializable Msg}
                              `{Serializable State}
                               (contract : Contract Setup Msg State)
                               bstate from caddr amount msg acts new_acts
                               cstate new_cstate,
  reachable bstate ->
  chain_state_queue bstate = {| act_from := from;
                                act_body := act_call caddr amount ((@serialize Msg _) msg) |} :: acts ->
  amount >= 0 ->
  env_account_balances bstate from >= amount ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  env_contract_states bstate caddr = Some ((@serialize State _) cstate) ->
  Blockchain.receive contract (transfer_balance from caddr amount bstate)
                     (build_ctx from caddr (if (address_eqb from caddr)
                         then (env_account_balances bstate caddr)
                         else (env_account_balances bstate caddr) + amount) amount)
                     cstate (Some msg) = Some (new_cstate, new_acts) ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ env_contract_states bstate' caddr = Some ((@serialize State _) new_cstate)
    /\ chain_state_queue bstate' = (map (build_act caddr) new_acts) ++ acts
    /\ EnvironmentEquiv
        bstate'
        (set_contract_state caddr ((@serialize State _) new_cstate) (transfer_balance from caddr amount bstate))).
Proof.
  intros.
  apply Z.ge_le in H5.
  pose (new_to_balance := if (address_eqb from caddr)
                         then (env_account_balances bstate caddr)
                         else (env_account_balances bstate caddr) + amount).
  pose (bstate' := (bstate<|chain_state_queue := (map (build_act caddr) new_acts) ++ acts|>
                          <|chain_state_env := set_contract_state caddr ((@serialize State _) new_cstate)
                                                  (transfer_balance from caddr amount bstate)|>)).
  assert (new_to_balance_eq : env_account_balances bstate' caddr = new_to_balance) by
   (cbn; destruct_address_eq; easy).
  assert (step : ChainStep bstate bstate').
  - eapply step_action; eauto.
    eapply eval_call with (msg0:= Some ((@serialize Msg _) msg)); eauto.
    + rewrite new_to_balance_eq.
      now apply wc_receive_to_receive in H8.
    + constructor; reflexivity.
  - exists bstate'.
    split; eauto.
    repeat split; eauto.
    cbn.
    now destruct_address_eq.
Qed.

Lemma evaluate_transfer : forall bstate from to amount acts,
  reachable bstate ->
  chain_state_queue bstate = {| act_from := from;
                                act_body := act_transfer to amount |} :: acts ->
  amount >= 0 ->
  env_account_balances bstate from >= amount ->
  address_is_contract to = false ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        (transfer_balance from to amount bstate)).
Proof.
  intros.
  apply Z.ge_le in H2.
  pose (bstate' := (bstate<|chain_state_queue := acts|>
                          <|chain_state_env := (transfer_balance from to amount bstate)|>)).
  assert (step : ChainStep bstate bstate').
  - eapply step_action with (new_acts := []); eauto.
    eapply eval_transfer; eauto.
    constructor; reflexivity.
  - eexists bstate'.
    split; eauto.
    repeat split; eauto.
Qed.

Lemma discard_invalid_action : forall bstate act acts,
  reachable bstate ->
  chain_state_queue bstate = act :: acts ->
  act_is_from_account act ->
  (forall (bstate0 : Environment) (new_acts : list Action), ActionEvaluation bstate act bstate0 new_acts -> False) ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        bstate).
Proof.
  intros.
  pose (bstate' := (bstate<|chain_state_queue := acts|>)).
  assert (step : ChainStep bstate bstate').
  - eapply step_action_invalid; eauto.
    constructor; reflexivity.
  - eexists bstate'.
    split; eauto.
    repeat split; eauto.
Qed.
Close Scope Z_scope.

Lemma step_reachable_through_exists : forall from mid (P : ChainState -> Prop),
  reachable_through from mid ->
  (exists to : ChainState, reachable_through mid to /\ P to) ->
  (exists to : ChainState, reachable_through from to /\ P to).
Proof.
  intros from mid P reach [to [reach_ HP]].
  now exists to.
Qed.

End BuildUtils.

Global Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

Global Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

Local Ltac update_fix term1 term2 H H_orig H' :=
  match H with
  | context G [ term1 ] =>
    let x := context G [ term2 ] in
      update_fix term1 term2 x H_orig H'
  | _ =>
    let h := fresh "H" in
      assert H; [H' | clear H_orig; rename h into H_orig]
  end.

Local Ltac update_ term1 term2 H H' :=
  match type of H with
  | context G [ term1 ] =>
    let x := context G [ term2 ] in
      update_fix term1 term2 x H H'
  end.

Tactic Notation "update" constr(t1) "with" constr(t2) "in" hyp(H) := update_ t1 t2 H ltac:(try (cbn; easy)).
Tactic Notation "update" constr(t1) "with" constr(t2) "in" hyp(H) "by" tactic(G) := update_ t1 t2 H G.
Tactic Notation "update" constr(t2) "in" hyp(H) := let t1 := type of H in update_ t1 t2 H ltac:(try (cbn; easy)).
Tactic Notation "update" constr(t2) "in" hyp(H) "by" tactic(G) := let t1 := type of H in update_ t1 t2 H G.

Local Ltac only_on_match tac :=
  match goal with
  | |- exists bstate', reachable_through ?bstate bstate' /\ _ => tac
  | |- _ => idtac
  end.

Local Ltac update_chainstate bstate1 bstate2 :=
  match goal with
  | H : reachable bstate1 |- _ => clear H
  | H : chain_state_queue bstate1 = _ |- _ => clear H
  | H : reachable_through bstate1 bstate2 |- _ =>
      update (reachable bstate2) in H
  | H : env_contracts bstate1.(chain_state_env) _ = Some _ |- _ =>
      update bstate1 with bstate2 in H by (now rewrite_environment_equiv)
  | H : env_contract_states bstate1.(chain_state_env) _ = Some _ |- _ =>
      update bstate1 with bstate2 in H by (now rewrite_environment_equiv)
  | H : context [ bstate1 ] |- _ =>
    match type of H with
    | EnvironmentEquiv _ _ => fail 1
    | _ => update bstate1 with bstate2 in H by (try (rewrite_environment_equiv;cbn; easy))
    end
  end;
  only_on_match ltac:(progress update_chainstate bstate1 bstate2).

Ltac update_all :=
  match goal with
  | Hreach : reachable_through ?bstate1 ?bstate2,
    Henv_eq : EnvironmentEquiv ?bstate2.(chain_state_env) (add_new_block_to_env ?header ?bstate1.(chain_state_env)) |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update_chainstate bstate1 bstate2;
      only_on_match ltac:(
        clear Henv_eq;
        try clear header;
        clear dependent bstate1)
  | Hreach : reachable_through ?bstate1 ?bstate2,
    Henv_eq : EnvironmentEquiv ?bstate2.(chain_state_env) _ |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update_chainstate bstate1 bstate2;
      only_on_match ltac:(
        clear Henv_eq;
        clear dependent bstate1)
  | Hreach : reachable_through ?bstate1 ?bstate2 |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update (reachable bstate2) in Hreach;
      only_on_match ltac:(clear dependent bstate1)
  end.

Ltac forward_time slot_ :=
  let new_bstate := fresh "bstate" in
  let new_header := fresh "header" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_slot_hit := fresh "slot_hit" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (forward_time bstate) with (slot := slot_)
        as [new_bstate [new_header [new_reach [new_slot_hit [new_queue new_env_eq]]]]]
  end.

Ltac add_block acts_ slot_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize add_block with (acts:=acts_) (slot_incr:=slot_)
        as [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | apply Hqueue| | | | |]
  end.

Ltac evaluate_action contract_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_deployed_state := fresh "deployed_state" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (evaluate_action contract_) as
        [new_bstate [new_reach [new_deployed_state [new_queue new_env_eq]]]];
      [apply Hreach | rewrite Hqueue | | | | | | ]
  end.

Ltac evaluate_transfer :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize evaluate_transfer as
        [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | rewrite Hqueue | | | | ]
  end.

Ltac discard_invalid_action :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize discard_invalid_action as
        [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | rewrite Hqueue | | | ]
  end.

Ltac empty_queue H :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let temp_H := fresh "H" in
   match goal with
  | Hempty : emptyable (chain_state_queue ?bstate),
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      pattern (bstate) in H;
      match type of H with
      | ?f bstate =>
        specialize (empty_queue bstate f) as
          [new_bstate [new_reach [temp_H new_queue]]];
        [apply Hreach | apply Hempty | apply H |
        clear H;
        intros ?bstate_from ?bstate_to ?act ?acts ?reach_from ?reach_to
          H ?queue_from ?queue_to [[?action_eval] | ?env_eq];
          only 1: destruct_action_eval |
        clear H; rename temp_H into H]
      end
  end.
