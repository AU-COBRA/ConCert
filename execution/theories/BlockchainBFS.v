From ConCert.Execution Require Import BlockchainBase.
From ConCert.Execution Require Import BlockchainTheories.
From ConCert.Execution Require Import BlockchainInduction.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import SerializableBase.
From Stdlib Require Import Permutation.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Import ListNotations.



Section DepthFirst.
  Context `{Base : ChainBase}.

  Definition NoPermutations {from to : ChainState} (trace : ChainTrace from to) : Prop.
  Proof.
    induction trace.
    - exact True.
    - destruct_chain_step.
      + apply IHtrace.
      + apply IHtrace.
      + apply IHtrace.
      + exact False.
  Defined.

  Fixpoint NoPermutations' {from to : ChainState} (trace : ChainTrace from to) : Prop :=
    match trace with
    | clnil => True
    | snoc trace' step =>
      match step with
      | step_permute _ _ _ _ => False
      | _ => NoPermutations' trace'
      end
    end.

  Inductive StepNotPermute : forall {from to : ChainState}, ChainStep from to -> Prop :=
  | snp_block : forall {from to : ChainState} h h1 h2 h3 h4 h5,
              StepNotPermute (step_block from to h h1 h2 h3 h4 h5)
  | snp_action : forall {from to : ChainState} h h1 h2 h3 h4 h5,
              StepNotPermute (step_action from to h h1 h2 h3 h4 h5)
  | snp_action_invalid : forall {from to : ChainState} h h1 h2 h3 h4 h5,
              StepNotPermute (step_action from to h h1 h2 h3 h4 h5).

  Inductive NoPermutations'' : forall {from to : ChainState}, ChainTrace from to -> Prop :=
  | trace_nil : forall {x : ChainState},
                        NoPermutations'' (@clnil ChainState ChainStep x)
  | trace_step : forall {from mid to : ChainState}
                        (trace : ChainTrace from mid)
                        (step : ChainStep mid to),
                        NoPermutations'' trace ->
                        StepNotPermute step ->
                        NoPermutations'' (snoc trace step).

  Definition DFSChainTrace (from to : ChainState) :=
    {trace : ChainTrace from to | NoPermutations'' trace}.

  Definition DFSChainTrace_to_ChainTrace {from to : ChainState}
                                         (trace : @DFSChainTrace from to)
                                         : ChainTrace from to :=
    proj1_sig trace.

  Coercion DFSChainTrace_to_ChainTrace : DFSChainTrace >-> ChainTrace.

  Open Scope Z_scope.

  Lemma DFS_weaken
      {Setup Msg State Error : Type}
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      `{Serializable Error}
      (contract : Contract Setup Msg State Error)
      (P : forall (chain_height : nat)
            (current_slot : nat)
            (finalized_height : nat)
            (caddr : Address)
            (deployment_info : DeploymentInfo Setup)
            (cstate : State)
            (balance : Amount)
            (outgoing_actions_queued : list ActionBody)
            (incoming_calls_seen : list (ContractCallInfo Msg))
            (outgoing_txs_seen : list Tx), Prop) :
      (forall bstate caddr (trace : ChainTrace empty_state bstate),
      env_contracts bstate caddr = Some (contract : WeakContract) ->
      exists dep cstate inc_calls,
        deployment_info Setup trace caddr = Some dep /\
        contract_state bstate caddr = Some cstate /\
        incoming_calls Msg trace caddr = Some inc_calls /\
        P (chain_height bstate)
          (current_slot bstate)
          (finalized_height bstate)
          caddr
          dep
          cstate
          (env_account_balances bstate caddr)
          (outgoing_acts bstate caddr)
          inc_calls
          (outgoing_txs trace caddr)) ->
      (forall bstate caddr (trace : DFSChainTrace empty_state bstate),
      env_contracts bstate caddr = Some (contract : WeakContract) ->
      exists dep cstate inc_calls,
        deployment_info Setup trace caddr = Some dep /\
        contract_state bstate caddr = Some cstate /\
        incoming_calls Msg trace caddr = Some inc_calls /\
        P (chain_height bstate)
          (current_slot bstate)
          (finalized_height bstate)
          caddr
          dep
          cstate
          (env_account_balances bstate caddr)
          (outgoing_acts bstate caddr)
          inc_calls
          (outgoing_txs trace caddr)).
  Proof.
    intros.
    specialize (H3 bstate caddr trace H4).
    destruct H3 as (dep & cstate & inc_calls & (? & ? & ? & ?)).
    do 3 eexists.
    eauto.
  Qed.


  Hint Resolve trace_reachable DFSChainTrace_to_ChainTrace : core.
  Lemma dfs_contract_induction
        {Setup Msg State Error : Type}
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      `{Serializable Error}
        (contract : Contract Setup Msg State Error)
        (AddBlockFacts :
          forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                  (new_height : nat) (new_slot : nat) (new_finalized_height : nat), Prop)
        (DeployFacts : forall (chain : Chain) (ctx : ContractCallContext), Prop)
        (CallFacts :
          forall (chain : Chain)
                  (ctx : ContractCallContext)
                  (cstate : State)
                  (outgoing_actions : list ActionBody)
                  (inc_calls : option (list (ContractCallInfo Msg))), Prop)
        (P : forall (chain_height : nat)
                    (current_slot : nat)
                    (finalized_height : nat)
                    (caddr : Address)
                    (deployment_info : DeploymentInfo Setup)
                    (cstate : State)
                    (balance : Amount)
                    (outgoing_actions_queued : list ActionBody)
                    (incoming_calls_seen : list (ContractCallInfo Msg))
                    (outgoing_txs_seen : list Tx), Prop) :

    (* Facts *)
    (forall (bstate_from bstate_to : ChainState) (step : ChainStep bstate_from bstate_to)
            (from_reachable : ChainTrace empty_state bstate_from)
            (tag : TagFacts),
        match step with
        | step_block _ _ header _ _ _ _ _ =>
          AddBlockFacts (chain_height bstate_from)
                        (current_slot bstate_from)
                        (finalized_height bstate_from)
                        (block_height header)
                        (block_slot header)
                        (block_finalized_height header)
        | step_action _ _ act _ _ _ (eval_deploy origin from to amount _ _ _ _ _ _ _ _ _ _ _) _ =>
          DeployFacts
            (transfer_balance from to amount bstate_from)
            (build_ctx origin from to amount amount)
        | step_action _ _ act _ _ _ (eval_call origin from to amount _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
          let new_state := transfer_balance from to amount bstate_from in
          forall (cstate : State),
            env_contracts bstate_from to = Some (contract : WeakContract) ->
            contract_state bstate_from to = Some cstate ->
            CallFacts
              new_state
              (build_ctx origin from to (env_account_balances new_state to) amount) cstate
              (outgoing_acts bstate_from to)
              (incoming_calls Msg from_reachable to)
        | _ => Logic.True
        end) ->

    (* Add block *)
    (forall old_chain_height old_cur_slot old_fin_height
            new_chain_height new_cur_slot new_fin_height
            caddr dep_info state balance inc_calls out_txs
            (facts : AddBlockFacts old_chain_height old_cur_slot old_fin_height
                                  new_chain_height new_cur_slot new_fin_height)
            (IH : P old_chain_height old_cur_slot old_fin_height
                    caddr dep_info state balance [] inc_calls out_txs)
            (tag : TagAddBlock),
        P new_chain_height new_cur_slot new_fin_height
          caddr dep_info state balance [] inc_calls out_txs) ->

    (* Deploy contract *)
    (forall chain ctx setup result
            (facts : DeployFacts chain ctx)
            (init_some : init contract chain ctx setup = Ok result)
            (tag : TagDeployment),
        P (chain_height chain)
          (current_slot chain)
          (finalized_height chain)
          (ctx_contract_address ctx)
          (build_deployment_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) setup)
          result
          (ctx_amount ctx)
          []
          []
          []) ->

    (* Transfer/call/deploy to someone else *)
    (forall height slot fin_height caddr dep_info cstate
            balance out_act out_acts inc_calls prev_out_txs tx
            (IH : P height slot fin_height caddr dep_info cstate balance
                    (out_act :: out_acts) inc_calls prev_out_txs)
            (tx_from_caddr : tx_from tx = caddr)
            (tx_amount_eq : tx_amount tx = act_body_amount out_act)
            (tx_act_match :
              match out_act with
              | act_transfer to amount =>
                tx_to tx = to /\ tx_amount tx = amount /\
                (tx_body tx = tx_empty \/ tx_body tx = tx_call None)
              | act_deploy amount wc setup =>
                tx_amount tx = amount /\ tx_body tx = tx_deploy wc setup
              | act_call to amount msg =>
                tx_to tx = to /\ tx_amount tx = amount /\ tx_body tx = tx_call (Some msg)
              end)
            (tag : TagOutgoingAct),
        P height slot fin_height caddr dep_info cstate (balance - act_body_amount out_act)
          out_acts inc_calls (tx :: prev_out_txs)) ->

    (* Non-recursive call *)
    (forall chain ctx dep_info prev_state msg
            prev_out_queue prev_inc_calls prev_out_txs
            new_state new_acts
            (from_other : ctx_from ctx <> ctx_contract_address ctx)
            (facts : CallFacts chain ctx prev_state prev_out_queue (Some prev_inc_calls))
            (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                    (ctx_contract_address ctx) dep_info prev_state
                    (ctx_contract_balance ctx - ctx_amount ctx)
                    prev_out_queue prev_inc_calls prev_out_txs)
            (receive_some : receive contract chain ctx prev_state msg =
                            Ok (new_state, new_acts))
            (tag : TagNonrecursiveCall),
        P (chain_height chain)
          (current_slot chain)
          (finalized_height chain)
          (ctx_contract_address ctx)
          dep_info
          new_state
          (ctx_contract_balance ctx)
          (new_acts ++ prev_out_queue)
          (build_call_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: prev_inc_calls)
          prev_out_txs) ->

    (* Recursive call *)
    (forall chain ctx dep_info prev_state msg
            head prev_out_queue prev_inc_calls prev_out_txs
            new_state new_acts
            (from_self : ctx_from ctx = ctx_contract_address ctx)
            (facts : CallFacts chain ctx prev_state (head :: prev_out_queue) (Some prev_inc_calls))
            (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                    (ctx_contract_address ctx) dep_info prev_state
                    (ctx_contract_balance ctx)
                    (head :: prev_out_queue) prev_inc_calls prev_out_txs)
            (action_facts :
              match head with
              | act_transfer to amount => to = ctx_contract_address ctx /\
                                          amount = ctx_amount ctx /\
                                          msg = None
              | act_call to amount msg_ser => to = ctx_contract_address ctx /\
                                              amount = ctx_amount ctx /\
                                              msg <> None /\
                                              deserialize msg_ser = msg
              | _ => False
              end)
            (receive_some : receive contract chain ctx prev_state msg =
                            Ok (new_state, new_acts))
            (tag : TagRecursiveCall),
        P (chain_height chain)
          (current_slot chain)
          (finalized_height chain)
          (ctx_contract_address ctx)
          dep_info
          new_state
          (ctx_contract_balance ctx)
          (new_acts ++ prev_out_queue)
          (build_call_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: prev_inc_calls)
          (build_tx (ctx_origin ctx)
                    (ctx_from ctx)
                    (ctx_contract_address ctx)
                    (ctx_amount ctx)
                    (tx_call (match head with
                              | act_call _ _ msg => Some msg
                              | _ => None
                              end)) :: prev_out_txs)) ->

    forall bstate caddr (trace : ChainTrace empty_state bstate),
      env_contracts bstate caddr = Some (contract : WeakContract) ->
      (NoPermutations'' trace) ->
      exists dep cstate inc_calls,
        deployment_info Setup trace caddr = Some dep /\
        contract_state bstate caddr = Some cstate /\
        incoming_calls Msg trace caddr = Some inc_calls /\
        P (chain_height bstate)
          (current_slot bstate)
          (finalized_height bstate)
          caddr
          dep
          cstate
          (env_account_balances bstate caddr)
          (outgoing_acts bstate caddr)
          inc_calls
          (outgoing_txs trace caddr).
  Proof.
  Admitted.

End DepthFirst.
