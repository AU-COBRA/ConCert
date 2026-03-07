From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Psatz.
From Stdlib Require Import Permutation.
From Stdlib Require Import Morphisms.
From Stdlib Require Import String.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import BlockchainBase.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.



Section ActionEvaluationFacts.
  Context {Base : ChainBase}
          {origin : Address}
          {pre : Environment}
          {post : Environment}
          {act : Action}
          {new_acts : list Action}
          (eval : ActionEvaluation pre act post new_acts).
  Local Open Scope Z.

  Lemma account_balance_post (addr : Address) :
    env_account_balances post addr =
    env_account_balances pre addr
    + (if (addr =? eval_to eval)%address then eval_amount eval else 0)
    - (if (addr =? eval_from eval)%address then eval_amount eval else 0).
  Proof.
    destruct eval; cbn; rewrite_environment_equiv; cbn;
      destruct_address_eq; lia.
  Qed. (* TODO: slow *)

  Lemma account_balance_post_to :
    eval_from eval <> eval_to eval ->
    env_account_balances post (eval_to eval) =
    env_account_balances pre (eval_to eval) + eval_amount eval.
  Proof.
    intros neq.
    rewrite account_balance_post.
    rewrite address_eq_refl, address_eq_ne by auto.
    lia.
  Qed.

  Lemma account_balance_post_from :
    eval_from eval <> eval_to eval ->
    env_account_balances post (eval_from eval) =
    env_account_balances pre (eval_from eval) - eval_amount eval.
  Proof.
    intros neq.
    rewrite account_balance_post.
    rewrite address_eq_refl, address_eq_ne by auto.
    lia.
  Qed.

  Lemma account_balance_post_irrelevant (addr : Address) :
    addr <> eval_from eval ->
    addr <> eval_to eval ->
    env_account_balances post addr = env_account_balances pre addr.
  Proof.
    intros neq_from neq_to.
    rewrite account_balance_post.
    repeat rewrite address_eq_ne by auto.
    lia.
  Qed.

  Lemma chain_height_post_action :
    chain_height post = chain_height pre.
  Proof.
    destruct eval; rewrite_environment_equiv; auto.
  Qed.
  (* TODO: slow *)

  Lemma current_slot_post_action :
    current_slot post = current_slot pre.
  Proof.
    destruct eval; rewrite_environment_equiv; auto.
  Qed.
  (* TODO: slow *)

  Lemma finalized_height_post_action :
    finalized_height post = finalized_height pre.
  Proof.
    destruct eval; rewrite_environment_equiv; auto.
  Qed.
  (* TODO: slow *)

  Lemma contracts_post_pre_none contract :
    env_contracts post contract = None ->
    env_contracts pre contract = None.
  Proof.
    intros H.
    destruct eval; rewrite_environment_equiv; auto.
    (* TODO: slow *)
    cbn in *.
    destruct_address_eq; congruence.
  Qed.

  Lemma eval_amount_nonnegative :
    eval_amount eval >= 0.
  Proof.
    now destruct eval.
  Qed.

  Lemma eval_amount_le_account_balance :
    eval_amount eval <= env_account_balances pre (eval_from eval).
  Proof.
    now destruct eval.
  Qed.
End ActionEvaluationFacts.


Section InitRecieveFacts.
  Context {Base : ChainBase}.

  Lemma wc_init_strong {Setup Msg State Error : Type}
                      `{Serializable Setup}
                      `{Serializable Msg}
                      `{Serializable State}
                      `{Serializable Error}
                       {contract : Contract Setup Msg State Error}
                       {chain ctx setup result} :
    wc_init (contract : WeakContract) chain ctx setup = Ok result ->
    exists setup_strong result_strong,
      deserialize setup = Some setup_strong /\
      serialize result_strong = result /\
      BlockchainBase.init contract chain ctx setup_strong = Ok result_strong.
  Proof.
    intros init.
    cbn in *.
    destruct (deserialize setup) as [setup_strong|] eqn:deser_setup;
      cbn in *; try congruence.
    exists setup_strong.
    destruct (BlockchainBase.init _ _ _ _) as [result_strong|] eqn:result_eq;
      cbn in *; try congruence.
    exists result_strong.
    repeat split; auto with congruence.
  Qed.

  Lemma wc_receive_strong {Setup Msg State Error : Type}
                         `{Serializable Setup}
                         `{Serializable Msg}
                         `{Serializable State}
                         `{Serializable Error}
                          {contract : Contract Setup Msg State Error}
                          {chain ctx prev_state msg new_state new_acts} :
    wc_receive (contract : WeakContract) chain ctx prev_state msg =
    Ok (new_state, new_acts) ->
    exists prev_state_strong msg_strong new_state_strong,
      deserialize prev_state = Some prev_state_strong /\
      match msg_strong with
      | Some msg_strong => msg >>= deserialize = Some msg_strong
      | None => msg = None
      end /\
      serialize new_state_strong = new_state /\
      BlockchainBase.receive contract chain ctx prev_state_strong msg_strong =
      Ok (new_state_strong, new_acts).
  Proof.
    intros receive.
    cbn in *.
    destruct (deserialize prev_state) as [prev_state_strong|] eqn:deser_state;
      cbn in *; try congruence.
    exists prev_state_strong.
    exists (msg >>= deserialize).
    destruct msg as [msg|]; cbn in *.
    1: destruct (deserialize msg) as [msg_strong|];
      cbn in *; try congruence.
    all: destruct (BlockchainBase.receive _ _ _ _ _)
      as [[resp_state_strong resp_acts_strong]|] eqn:result_eq;
      cbn in *; try congruence.
    all: exists resp_state_strong.
    all: inversion_clear receive; auto.
  Qed.

  (* wc_receive and contract receive are equivalent *)
  Lemma wc_receive_to_receive : forall {Setup Msg State Error : Type}
                                      `{Serializable Setup}
                                      `{Serializable Msg}
                                      `{Serializable State}
                                      `{Serializable Error}
                                      (contract : Contract Setup Msg State Error)
                                      chain cctx cstate msg new_cstate new_acts,
    contract.(receive) chain cctx cstate (Some msg) = Ok (new_cstate, new_acts) <->
    wc_receive contract chain cctx ((@serialize State _) cstate) (Some ((@serialize Msg _) msg)) = Ok ((@serialize State _) new_cstate, new_acts).
  Proof.
    split; intros receive_some.
    - cbn.
      rewrite !deserialize_serialize.
      cbn.
      now rewrite receive_some.
    - apply wc_receive_strong in receive_some as
        (prev_state' & msg' & new_state' & prev_state_eq & msg_eq & new_state_eq & receive_some).
      apply serialize_injective in new_state_eq. subst.
      rewrite deserialize_serialize in prev_state_eq.
      inversion prev_state_eq. subst.
      destruct msg' eqn:Hmsg.
      + cbn in msg_eq.
        now rewrite deserialize_serialize in msg_eq.
      + inversion msg_eq.
  Qed.

  (* wc_init and contract init are equivalent *)
  Lemma wc_init_to_init : forall {Setup Msg State Error : Type}
                                `{Serializable Setup}
                                `{Serializable Msg}
                                `{Serializable State}
                                `{Serializable Error}
                                (contract : Contract Setup Msg State Error)
                                chain cctx cstate setup,
    contract.(init) chain cctx setup = Ok cstate <->
    wc_init contract chain cctx ((@serialize Setup _) setup) = Ok ((@serialize State _) cstate).
  Proof.
    split; intros init_some.
    - cbn.
      rewrite deserialize_serialize.
      cbn.
      now rewrite init_some.
    - apply wc_init_strong in init_some as
        (setup_strong & result_strong & serialize_setup & serialize_result & init_some).
      apply serialize_injective in serialize_result. subst.
      rewrite deserialize_serialize in serialize_setup.
      now inversion serialize_setup.
  Qed.
End InitRecieveFacts.



Section ReachableFacts.
  Context {Base : ChainBase}.

  Lemma trace_reachable : forall {to},
    ChainTrace empty_state to ->
      reachable to.
  Proof.
    constructor.
    assumption.
  Qed.

  (* The empty state is always reachable *)
  Lemma reachable_empty_state :
    reachable empty_state.
  Proof.
    repeat constructor.
  Qed.

  (* Transitivity property of reachable and ChainTrace *)
  Lemma reachable_trans from to :
    reachable from ->
      ChainTrace from to ->
        reachable to.
  Proof.
    intros [].
    constructor.
    eapply ChainedList.clist_app; eauto.
  Qed.

  (* Transitivity property of reachable and ChainStep *)
  Lemma reachable_step from to :
    reachable from ->
      ChainStep from to ->
        reachable to.
  Proof.
    intros [].
    do 2 econstructor; eauto.
  Qed.

  (* A state is always reachable through itself *)
  Lemma reachable_through_refl : forall bstate,
    reachable bstate ->
      reachable_through bstate bstate.
  Proof.
    intros bstate reach.
    split; auto.
    do 2 constructor.
  Qed.

  (* Transitivity property of reachable_through and ChainStep *)
  Lemma reachable_through_trans' : forall from mid to,
    reachable_through from mid ->
      ChainStep mid to ->
        reachable_through from to.
  Proof.
    intros * [reach [trace]] step.
    repeat (econstructor; eauto).
  Qed.

  (* Transitivity property of reachable_through *)
  Lemma reachable_through_trans : forall from mid to,
    reachable_through from mid ->
      reachable_through mid to ->
        reachable_through from to.
  Proof.
    intros * [[trace_from] [trace_mid]] [_ [trace_to]].
    do 2 constructor.
    assumption.
    eapply ChainedList.clist_app; eauto.
  Qed.

  (* Reachable_through can also be constructed from ChainStep instead of a
    ChainTrace since a ChainTrace can be constructed from a ChainStep *)
  Lemma reachable_through_step : forall from to,
    reachable from ->
      ChainStep from to ->
        reachable_through from to.
  Proof.
    intros * reach_from step.
    apply reachable_through_refl in reach_from.
    eapply reachable_through_trans'; eauto.
  Qed.

  (* Any ChainState that is reachable through another ChainState is reachable *)
  Lemma reachable_through_reachable : forall from to,
    reachable_through from to ->
      reachable to.
  Proof.
    intros * [[trace_from] [trace_to]].
    constructor.
    eapply ChainedList.clist_app; eauto.
  Qed.

  Lemma step_reachable_through_exists : forall from mid (P : ChainState -> Prop),
    reachable_through from mid ->
    (exists to : ChainState, reachable_through mid to /\ P to) ->
    (exists to : ChainState, reachable_through from to /\ P to).
  Proof.
    intros * reach [to [reach_ HP]].
    exists to.
    split; auto.
    eapply reachable_through_trans; eauto.
  Qed.

End ReachableFacts.

Hint Resolve trace_reachable
              reachable_trans
              reachable_step : core.

Hint Resolve reachable_through_refl
              reachable_through_trans'
              reachable_through_trans
              reachable_through_step
              reachable_through_reachable : core.



Section TraceFacts.
  Context {Base : ChainBase}.

  Lemma contract_addr_format {to : ChainState}
                             (addr : Address)
                             (wc : WeakContract) :
    reachable to ->
    env_contracts to addr = Some wc ->
    address_is_contract addr = true.
  Proof.
    intros [trace] contract_at_addr.
    remember empty_state eqn:eq.
    induction trace; rewrite eq in *; clear eq.
    - cbn in *; congruence.
    - destruct_chain_step;
        try now rewrite_environment_equiv.
      + destruct_action_eval; rewrite_environment_equiv; cbn in *;
          destruct_address_eq; subst; auto.
  Qed.

  Lemma new_acts_no_out_queue (orig addr1 addr2 : Address)
                              (new_acts : list Action)
                              (resp_acts : (list ActionBody)) :
    addr1 <> addr2 ->
    new_acts = map (build_act orig addr2) resp_acts ->
    Forall (fun a => (act_from a =? addr1)%address = false) new_acts.
  Proof.
    intros neq ?; subst.
    induction resp_acts; cbn; auto.
    constructor; destruct_address_eq; cbn in *; congruence.
  Qed.

  Local Open Scope address.
  (* This next lemma shows that any for a full chain trace,
  the ending state will not have any queued actions from
  undeployed contracts. *)
  Lemma undeployed_contract_no_out_queue contract state :
    reachable state ->
    address_is_contract contract = true ->
    env_contracts state contract = None ->
    Forall (fun act => (act_from act =? contract) = false) (chain_state_queue state).
  Proof.
    intros [trace] is_contract.
    remember empty_state eqn:eq.
    induction trace;
      intros undeployed; rewrite eq in *; clear eq; cbn; auto.
    destruct_chain_step; [|destruct_action_eval| |];
      try rewrite_environment_equiv;
      repeat
        match goal with
        | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
        end;
      subst;
      cbn in *.
    - (* New block *)
      match goal with
      | [H: Forall act_is_from_account _ |- _] => induction H
      end;
      match goal with
      | [H: Forall act_origin_is_eq_from _ |- _] => inversion H
      end; constructor; auto; destruct_address_eq; congruence.
    - (* Transfer step, just use IH *)
      eapply list_relations.list.Forall_cons; eauto.
    - (* Deploy step. First show that it is not to contract and then use IH. *)
      destruct_address_eq; try congruence.
      eapply list_relations.list.Forall_cons; eauto.
    - (* Call. Show that it holds for new actions as it is from *)
      (* another contract, and use IH for remaining. *)
      apply list_relations.list.Forall_app.
      assert (contract <> to_addr) by congruence.
      split; [eapply new_acts_no_out_queue|eapply list_relations.list.Forall_cons]; eauto.
    - (* Invalid User Action *)
      now apply Forall_inv_tail in IHtrace.
    - (* Permutation *)
      specialize_hypotheses.
      now rewrite <- perm.
  Qed.

  Local Hint Resolve contracts_post_pre_none : core.
  Local Hint Unfold reachable : core.

  (* With this lemma proven, we can show that the (perhaps seemingly stronger)
  fact, that an undeployed contract has no outgoing txs, holds. *)
  Lemma undeployed_contract_no_out_txs (contract : Address)
                                       (state : ChainState)
                                       (trace : ChainTrace empty_state state) :
    address_is_contract contract = true ->
    env_contracts state contract = None ->
    outgoing_txs trace contract = [].
  Proof.
    intros is_contract undeployed.
    remember empty_state; induction trace; subst; cbn; auto.
    destruct_chain_step; try now rewrite_environment_equiv.
    - (* In these steps we will use that the queue did not contain txs to the contract. *)
      subst.
      cbn.
      pose proof
          (undeployed_contract_no_out_queue
              contract mid
              ltac:(auto) ltac:(auto) ltac:(eauto)) as Hqueue.
      repeat
        match goal with
        | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
        end.
      inversion_clear Hqueue.
      destruct act;
      destruct_action_eval; rewrite_environment_equiv;
        subst;
        cbn in *;
        destruct_address_eq;
        try tauto; try congruence.
  Qed.

  Lemma undeployed_contract_no_in_txs (contract : Address)
                                      (state : ChainState)
                                      (trace : ChainTrace empty_state state) :
    address_is_contract contract = true ->
    env_contracts state contract = None ->
    incoming_txs trace contract = [].
  Proof.
    intros is_contract undeployed.
    remember empty_state; induction trace; subst; cbn; auto.
    destruct_chain_step; try now rewrite_environment_equiv.
    - destruct_action_eval; rewrite_environment_equiv;
        cbn in *;
        destruct_address_eq; auto; subst; congruence.
  Qed.

  Lemma deployment_info_some (Setup : Type)
                            `{Serializable Setup}
                            {to : ChainState}
                            (trace : ChainTrace empty_state to)
                            (caddr : Address) :
    deployment_info Setup trace caddr <> None ->
    env_contracts to caddr <> None.
  Proof.
    remember empty_state; induction trace as [|? ? ? ? IH]; subst; cbn in *; try tauto.
    destruct_chain_step; try now rewrite_environment_equiv.
    - destruct_action_eval; rewrite_environment_equiv; auto.
      (* Deploy *)
      cbn in *.
      rewrite (address_eq_sym caddr).
      destruct_address_eq; try discriminate.
      auto.
  Qed.

  Lemma deployment_info_addr_format (Setup : Type)
                                   `{Serializable Setup}
                                    {to : ChainState}
                                    (trace : ChainTrace empty_state to)
                                    (caddr : Address) :
    deployment_info Setup trace caddr <> None ->
    address_is_contract caddr = true.
  Proof.
    intros has_deployment_info.
    pose proof (deployment_info_some _ _ _ has_deployment_info).
    destruct (env_contracts to caddr) as [wc|] eqn:?; try congruence.
    apply contract_addr_format in Heqo; auto.
  Qed.

  Lemma incoming_txs_contract (caddr : Address)
                              (bstate : ChainState)
                              (trace : ChainTrace empty_state bstate)
                              (Setup : Type)
                             `{Serializable Setup}
                              (depinfo : DeploymentInfo Setup)
                              (Msg : Type)
                             `{Serializable Msg}
                              (msgs : list (ContractCallInfo Msg)) :
    deployment_info Setup trace caddr = Some depinfo ->
    incoming_calls Msg trace caddr = Some msgs ->
    map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) (incoming_txs trace caddr) =
    map (fun call => (call_from call, caddr, call_amount call)) msgs ++
        [(deployment_from depinfo, caddr, deployment_amount depinfo)].
  Proof.
    intros depinfo_eq calls_eq.
    enough ((env_contracts bstate caddr = None ->
            incoming_txs trace caddr = [] /\
            deployment_info Setup trace caddr = None /\
            incoming_calls Msg trace caddr = Some []) /\
            (env_contracts bstate caddr <> None ->
            deployment_info Setup trace caddr <> None ->
            incoming_calls Msg trace caddr <> None ->
            exists (depinfo : DeploymentInfo Setup)
                    (inc_calls : list (ContractCallInfo Msg))
                    (call_txs : list Tx) (dep_tx : Tx),
              deployment_info Setup trace caddr = Some depinfo /\
              incoming_calls Msg trace caddr = Some inc_calls /\
              incoming_txs trace caddr = call_txs ++ [dep_tx] /\
              map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) call_txs =
              map (fun call => (call_from call, caddr, call_amount call)) inc_calls /\
              (tx_from dep_tx, tx_to dep_tx, tx_amount dep_tx) =
              (deployment_from depinfo, caddr, deployment_amount depinfo))) as generalized.
    {
      rewrite depinfo_eq, calls_eq in *.
      destruct (env_contracts bstate caddr).
      - destruct generalized as [_ generalized].
        specialize (generalized ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
        destruct generalized as [? [? [? [? [? [? [-> [? ?]]]]]]]].
        rewrite map_app.
        cbn.
        congruence.
      - destruct generalized as [generalized _].
        specialize (generalized eq_refl).
        destruct generalized as [_ [? _]]; congruence.
    }

    assert (is_contract: address_is_contract caddr = true).
    { assert (deployment_info Setup trace caddr <> None) by congruence.
      eapply (deployment_info_addr_format Setup); eassumption. }

    clear depinfo_eq calls_eq depinfo msgs.

    remember empty_state; induction trace as [|? ? ? ? IH]; subst; cbn in *;
      try tauto.
    destruct_chain_step; cbn in *; try now rewrite_environment_equiv.
    - (* Evaluation *)
      destruct_action_eval; cbn in *; rewrite_environment_equiv.
      + (* Transfer *)
        destruct_address_eq; auto.
        subst.
        cbn.
        congruence.
      + (* Deploy *)
        cbn in *.
        rewrite (address_eq_sym caddr) in *.
        destruct_address_eq; auto.
        split; try discriminate.
        intros _ depinfo_ne_none calls_ne_none.
        subst.
        cbn in *.
        destruct (deserialize setup); cbn in *; try congruence.
        remember (build_deployment_info _ _ _ _) as depinfo.
        remember (build_tx _ _ _ _ _) as deptx.
        destruct IH as [IH _]; auto.
        specialize (IH ltac:(auto)).
        fold (incoming_txs trace caddr).
        destruct IH as [-> [? ->]].
        exists depinfo, [], [], deptx; subst; cbn in *.
        tauto.
      + (* Call *)
        destruct_address_eq; subst; auto.
        cbn in *.
        split; [intros; congruence|].
        destruct IH as [_ IH]; auto.
        intros _ deploy_info calls.
        destruct (match msg with | Some _ => _ | _ => Some None end);
          cbn in *; try congruence.
        destruct (incoming_calls _ _) as [inc_calls|]; cbn in *; try congruence.
        unshelve epose proof (IH _ _ _) as IH; auto; try congruence.
        destruct IH as
            [depinfo [prev_calls
                        [prev_call_txs [dep_tx
                                          [depinfo_eq [inc_calls_eq
                                                        [inc_txs_eq [map_eq ?]]]]]]]].
        remember (build_tx _ _ _ _ _) as new_tx.
        remember (build_call_info _ _ _ _) as new_call.
        exists depinfo, (new_call :: inc_calls), (new_tx :: prev_call_txs), dep_tx.
        split; auto.
        split; auto.
        fold (incoming_txs trace caddr).
        rewrite inc_txs_eq.
        split; [now rewrite app_comm_cons|].
        inversion_clear inc_calls_eq.
        cbn.
        rewrite map_eq.
        subst; tauto.
  Qed.

  Lemma undeployed_contract_no_in_calls {Msg : Type}
                                       `{Serializable Msg}
                                        (contract : Address)
                                        (state : ChainState)
                                        (trace : ChainTrace empty_state state) :
    env_contracts state contract = None ->
    incoming_calls Msg trace contract = Some [].
  Proof.
    unfold incoming_calls.
    intros undeployed.
    remember empty_state; induction trace; subst; cbn in *; auto.
    destruct_chain_step; try now rewrite_environment_equiv.
    - destruct_action_eval; rewrite_environment_equiv;
        cbn in *;
        destruct_address_eq; auto; subst; congruence.
  Qed.

  Local Open Scope Z.
  Lemma account_balance_trace (state : ChainState)
                              (trace : ChainTrace empty_state state)
                              (addr : Address) :
    env_account_balances state addr =
    sumZ tx_amount (incoming_txs trace addr) +
    sumZ block_reward (created_blocks trace addr) -
    sumZ tx_amount (outgoing_txs trace addr).
  Proof.
    unfold incoming_txs, outgoing_txs.
    remember empty_state as from_state.
    induction trace; [|destruct_chain_step].
    - subst. cbn. lia.
    - (* Block *)
      rewrite_environment_equiv.
      cbn.
      fold (created_blocks trace addr).
      rewrite IHtrace by auto.
      destruct_address_eq; subst; cbn; lia.
    - (* Step *)
      cbn.
      destruct_action_eval; cbn; rewrite_environment_equiv; cbn.
      all: fold (created_blocks trace addr); rewrite IHtrace by auto.
      all: destruct_address_eq; cbn; lia.
    - (* Invalid User Action *)
      now rewrite_environment_equiv.
    - (* Permutation *)
      now rewrite_environment_equiv.
  Qed.

  Lemma contract_no_created_blocks (state : ChainState)
                                   (trace : ChainTrace empty_state state)
                                   (addr : Address) :
    address_is_contract addr = true ->
    created_blocks trace addr = [].
  Proof.
    intros is_contract.
    remember empty_state eqn:eq.
    induction trace; auto.
    destruct_chain_step; auto.
    cbn.
    subst.
    inversion valid_header.
    destruct (address_eqb_spec (block_creator header) addr); auto.
    congruence.
  Qed.

  Lemma undeployed_contract_balance_0 state addr :
    reachable state ->
    address_is_contract addr = true ->
    env_contracts state addr = None ->
    env_account_balances state addr = 0.
  Proof.
    intros [trace] is_contract no_contract.
    rewrite (account_balance_trace _ trace); auto.
    rewrite undeployed_contract_no_out_txs, undeployed_contract_no_in_txs,
            contract_no_created_blocks; auto.
  Qed.

  Lemma account_balance_nonnegative state addr :
    reachable state ->
    env_account_balances state addr >= 0.
  Proof.
    intros [trace].
    remember empty_state eqn:eq.
    induction trace; subst; cbn; try lia.
    specialize (IHtrace eq_refl).
    destruct_chain_step.
    - (* New block *)
      rewrite_environment_equiv.
      cbn.
      inversion valid_header.
      destruct_address_eq; lia.
    - (* Action evaluation *)
      rewrite (account_balance_post eval addr).
      pose proof (eval_amount_nonnegative eval).
      pose proof (eval_amount_le_account_balance eval).
      destruct_address_eq; subst; cbn in *; lia.
    - (* Invalid User Action *)
      now rewrite_environment_equiv.
    - (* Permutation *)
      now rewrite_environment_equiv.
  Qed.

  Lemma deployed_contract_state_typed {Setup Msg State Error : Type}
                                     `{Serializable Setup}
                                     `{Serializable Msg}
                                     `{Serializable State}
                                     `{Serializable Error}
                                      {contract : Contract Setup Msg State Error}
                                      {bstate : ChainState}
                                      {caddr} :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    reachable bstate ->
    exists (cstate : State),
      contract_state bstate caddr = Some cstate.
  Proof.
    intros contract_deployed [trace].
    destruct (contract_state bstate caddr) as [cstate|] eqn:eq;
      [exists cstate; auto|].
    unfold contract_state in *.
    (* Show that eq is a contradiction. *)
    remember empty_state; induction trace; subst; cbn in *; try congruence.
    destruct_chain_step; try now rewrite_environment_equiv.
    - (* Action evaluation *)
      destruct_action_eval; subst; rewrite_environment_equiv; cbn in *.
      + (* Transfer, use IH *)
        auto.
      + (* Deployment *)
        destruct_address_eq; subst; auto.
        (* To this contract, show that deserialization would not fail. *)
        replace wc with (contract : WeakContract) in * by congruence.
        destruct (wc_init_strong ltac:(eassumption))
          as [setup_strong [result_strong [? [<- init]]]].
        cbn in eq.
        rewrite deserialize_serialize in eq; congruence.
      + (* Call *)
        destruct (address_eqb_spec caddr to_addr); subst; auto.
        (* To this contract, show that deserialization would not fail. *)
        replace wc with (contract : WeakContract) in * by congruence.
        destruct (wc_receive_strong ltac:(eassumption))
          as [state_strong [msg_strong [resp_state_strong [? [? [<- receive]]]]]].
        cbn in eq.
        rewrite deserialize_serialize in eq; congruence.
  Qed.

  Lemma origin_is_always_account {bstate : ChainState} :
    reachable bstate ->
    Forall act_origin_is_account (chain_state_queue bstate).
  Proof.
    intros [trace].
    remember empty_state; induction trace; subst; cbn in *; try constructor.
    destruct_chain_step.
    - (* New block, use the fact that [act_origin] is the same as [act_from]
        and [act_from] is an account address*)
      now apply origin_is_account.
    - (* Action evaluation *)
      destruct_action_eval; subst;
        rewrite queue_new in *;
        rewrite queue_prev in *;
        cbn in *;
        specialize_hypotheses;
        inversion IHtrace; subst; try easy.
      apply Forall_app. split.
      * apply All_Forall.Forall_map.
        apply Forall_forall; easy.
      * auto.
    - (* Invalid User Action *)
      rewrite queue_new in *; rewrite queue_prev in *; cbn in *.
      specialize_hypotheses; inversion IHtrace; subst; easy.
    - (* Permutation *)
      eapply forall_respects_permutation; eauto.
  Qed.

  Local Open Scope nat_scope.
  (* If a state is reachable then the finalized_height cannot be larger than the chain_height *)
  Lemma finalized_heigh_chain_height bstate :
    reachable bstate ->
    finalized_height bstate < S (chain_height bstate).
  Proof.
    intros [trace].
    remember empty_state.
    induction trace as [ | Heq from to trace IH step ]; subst.
    - auto.
    - destruct_chain_step;
      try destruct_action_eval;
      rewrite_environment_equiv;
      auto.
      now inversion valid_header.
  Qed.

  (* If a state is reachable and contract state is stored on an address
      then that address must also have some contract deployed to it *)
  Lemma contract_states_deployed (to : ChainState)
                                 (addr : Address)
                                 (state : SerializedValue) :
    reachable to ->
    env_contract_states to addr = Some state ->
    exists wc, env_contracts to addr = Some wc.
  Proof.
    intros [trace].
    remember empty_state.
    induction trace as [ | Heq from to trace IH step ];
      subst; intros.
    - discriminate.
    - destruct_chain_step;
        only 2: destruct_action_eval;
        rewrite_environment_equiv;
        setoid_rewrite env_eq; cbn in *;
        destruct_address_eq; now subst.
  Qed.

  (* If a state is reachable and contract state is stored on an address
      then that address must be a contract address *)
  Lemma contract_states_addr_format (to : ChainState)
                                    (addr : Address)
                                    (state : SerializedValue) :
    reachable to ->
    env_contract_states to addr = Some state ->
    address_is_contract addr = true.
  Proof.
    intros ? deployed_state.
    apply contract_states_deployed in deployed_state as []; auto.
    now eapply contract_addr_format.
  Qed.

  (* Initial contract balance will always be positive in reachable states *)
  Lemma deployment_amount_nonnegative : forall {Setup : Type} `{Serializable Setup}
                                        bstate caddr dep_info
                                        (trace : ChainTrace empty_state bstate),
    deployment_info Setup trace caddr = Some dep_info ->
    (0 <= dep_info.(deployment_amount))%Z.
  Proof.
    intros * deployment_info_some.
    remember empty_state.
    induction trace; subst.
    - discriminate.
    - destruct_chain_step; auto.
      destruct_action_eval; auto.
      cbn in deployment_info_some.
      destruct_address_eq; auto.
      destruct_match in deployment_info_some;
        try congruence.
      inversion_clear deployment_info_some.
      now apply Z.ge_le.
  Qed.

  Theorem origin_user_address : forall bstate,
    reachable bstate ->
    List.Forall (fun act => address_is_contract act.(act_origin) = false) (chain_state_queue bstate).
  Proof.
    intros * [trace].
    remember empty_state.
    induction trace; subst; try auto.
    destruct_chain_step.
    - clear env_eq.
      apply List.Forall_forall.
      rewrite List.Forall_forall in origin_correct.
      rewrite List.Forall_forall in acts_from_accs.
      intros x Hin.
      specialize (origin_correct x Hin).
      specialize (acts_from_accs x Hin).
      unfold act_is_from_account, act_origin_is_eq_from in *.
      destruct_address_eq; try discriminate.
      now rewrite e.
    - rewrite queue_prev in *.
      rewrite queue_new in *.
      specialize (IHtrace eq_refl).
      apply list_relations.list.Forall_cons in IHtrace as [Hact IHtrace].
      apply All_Forall.app_Forall; auto.
      destruct_action_eval; try (subst; apply List.Forall_nil).
      + subst.
        apply All_Forall.Forall_map.
        cbn in *.
        rewrite Hact.
        apply List.Forall_forall.
        reflexivity.
    - rewrite queue_prev in *.
      rewrite queue_new in *.
      specialize (IHtrace eq_refl).
      apply list_relations.list.Forall_cons in IHtrace as [Hact IHtrace].
      assumption.
    - eapply Extras.forall_respects_permutation; eauto.
  Qed.

  Lemma current_slot_chain_height bstate :
    reachable bstate ->
    (bstate.(chain_height) <= bstate.(current_slot))%nat.
  Proof.
    intros [trace].
    remember empty_state.
    induction trace as [ | Heq from to trace IH step ]; subst.
    - auto.
    - destruct_chain_step;
      try destruct_action_eval;
      rewrite_environment_equiv;
      auto.
      + inversion valid_header. cbn.
        rewrite valid_height.
        specialize (IH eq_refl).
        lia.
  Qed.

  Definition context_valid' {from to : ChainState} (trace : ChainTrace from to) : Prop.
  Proof.
    induction trace.
    - exact True.
    - destruct_chain_step.
      + apply IHtrace.
      + destruct_action_eval.
        * exact True.
        * match goal with
          | H : wc_init _ _ ?ctx _ = Ok _ |- _ =>
            exact (ValidContext ctx)
          end.
        * match goal with
          | H : wc_receive _ _ ?ctx _ _ = Ok _ |- _ =>
            exact (ValidContext ctx)
          end.
      + apply IHtrace.
      + apply IHtrace.
  Defined.

  Lemma context_valid : forall bstate (trace : ChainTrace empty_state bstate),
    context_valid' trace.
  Proof.
    intros.
    remember empty_state as e.
    induction trace; try apply I.
    destruct_chain_step; try now apply IHtrace.
    destruct_action_eval; try apply I.
    - (* init case *)
      cbn.
      constructor.
      + subst.
        specialize (origin_user_address mid) as H.
        rewrite queue_prev in *.
        apply list_relations.list.Forall_cons in H as [Hact _].
        * assumption.
        * now apply trace_reachable.
      + assumption.
      + cbn. lia.
      + cbn. lia.
    - (* receive case *)
      cbn.
      constructor.
      + subst.
        specialize (origin_user_address mid) as H.
        rewrite queue_prev in *.
        apply list_relations.list.Forall_cons in H as [Hact _].
        * assumption.
        * now apply trace_reachable.
      + apply contract_addr_format in deployed.
        assumption.
        subst. now apply trace_reachable.
      + subst.
        rewrite_environment_equiv. cbn.
        destruct_address_eq; subst; try contradiction.
        lia.
        specialize (account_balance_nonnegative _ to_addr (trace_reachable trace)).
        lia.
      + cbn. lia.
  Qed.

  Definition chain_valid' {from to : ChainState} (trace : ChainTrace from to) : Prop.
  Proof.
    induction trace.
    - exact True.
    - destruct_chain_step.
      + apply IHtrace.
      + destruct_action_eval.
        * exact True.
        * match goal with
          | H : wc_init _ ?chain _ _ = Ok _ |- _ =>
            exact (ValidChain chain)
          end.
        * match goal with
          | H : wc_receive _ ?chain _ _ _ = Ok _ |- _ =>
            exact (ValidChain chain)
          end.
      + apply IHtrace.
      + apply IHtrace.
  Defined.

  Lemma chain_valid : forall bstate (trace : ChainTrace empty_state bstate),
    chain_valid' trace.
  Proof.
    intros.
    remember empty_state.
    induction trace; try apply I.
    destruct_chain_step; try now apply IHtrace.
    destruct_action_eval; try apply I.
    - (* init case *)
      cbn. subst.
      constructor.
      + apply current_slot_chain_height.
        now apply trace_reachable.
      + apply finalized_heigh_chain_height.
        now apply trace_reachable.
    - (* receive case *)
      cbn. subst.
      constructor.
      + apply current_slot_chain_height.
        now apply trace_reachable.
      + apply finalized_heigh_chain_height.
        now apply trace_reachable.
  Qed.

End TraceFacts.



Section ReachableThroughFacts.
  Context {Base : ChainBase}.

  (* If a state has a contract deployed to some addr then any other state
      reachable through the first state must also have the same contract
      deployed to the same addr *)
  Lemma reachable_through_contract_deployed : forall from to addr wc,
    reachable_through from to ->
    env_contracts from addr = Some wc ->
      env_contracts to addr = Some wc.
  Proof.
    intros * [reach [trace]] deployed.
    induction trace as [ | from mid to trace IH step ].
    - assumption.
    - destruct_chain_step;
        only 2: destruct_action_eval;
        rewrite_environment_equiv; cbn;
        destruct_address_eq; subst; try easy.
      now rewrite IH in not_deployed by assumption.
  Qed.

  (* If a state has a contract state on some addr then any other state
      reachable through the first state must also have the some contract
      state on the same addr *)
  Lemma reachable_through_contract_state : forall from to addr cstate,
    reachable_through from to ->
    env_contract_states from addr = Some cstate ->
      exists new_cstate, env_contract_states to addr = Some new_cstate.
  Proof.
    intros * [reachable [trace]] deployed_state.
    generalize dependent cstate.
    induction trace as [ | from mid to trace IH step ];
      intros cstate deployed_state.
    - now eexists.
    - destruct_chain_step;
        only 2: destruct_action_eval;
        try rewrite_environment_equiv;
        try setoid_rewrite env_eq;
        cbn in *;
        destruct_address_eq; now subst.
  Qed.

  (* If a state is reachable through another state then it cannot have a lower chain height *)
  Lemma reachable_through_chain_height : forall from to,
    reachable_through from to ->
      from.(chain_height) <= to.(chain_height).
  Proof.
    intros * [reachable [trace]].
    induction trace as [ | from mid to trace IH step ].
    - apply Nat.le_refl.
    - destruct_chain_step;
      try destruct_action_eval;
      rewrite_environment_equiv; cbn; auto.
      + now inversion valid_header.
  Qed.

  (* If a state is reachable through another state then it cannot have a lower current slot *)
  Lemma reachable_through_current_slot : forall from to,
    reachable_through from to ->
      from.(current_slot) <= to.(current_slot).
  Proof.
    intros * [reachable [trace]].
    induction trace as [ | from mid to trace IH step ].
    - apply Nat.le_refl.
    - destruct_chain_step;
      try destruct_action_eval;
      rewrite_environment_equiv; cbn; auto.
      + now inversion valid_header.
  Qed.

  (* If a state is reachable through another state then it cannot have a lower finalized height *)
  Lemma reachable_through_finalized_height : forall from to,
    reachable_through from to ->
      from.(finalized_height) <= to.(finalized_height).
  Proof.
    intros * [reachable [trace]].
    induction trace as [ | from mid to trace IH step ].
    - apply Nat.le_refl.
    - destruct_chain_step;
      try destruct_action_eval;
      rewrite_environment_equiv; cbn; auto.
      + now inversion valid_header.
  Qed.

End ReachableThroughFacts.



Section Theories.
  Context {Base : ChainBase}.

  Lemma outgoing_acts_after_block_nil bstate addr :
    Forall act_is_from_account (chain_state_queue bstate) ->
    address_is_contract addr = true ->
    outgoing_acts bstate addr = [].
  Proof.
    intros all is_contract.
    unfold outgoing_acts.
    induction (chain_state_queue bstate); auto.
    cbn.
    inversion_clear all.
    destruct_address_eq; subst; auto.
    unfold act_is_from_account in *.
    congruence.
  Qed.

  Lemma outgoing_acts_after_deploy_nil bstate addr :
    Forall (fun act => (act_from act =? addr)%address = false) (chain_state_queue bstate) ->
    outgoing_acts bstate addr = [].
  Proof.
    intros all.
    unfold outgoing_acts.
    induction (chain_state_queue bstate) as [|hd tl IH]; auto.
    cbn in *.
    inversion_clear all.
    rewrite H.
    auto.
  Qed.

End Theories.
