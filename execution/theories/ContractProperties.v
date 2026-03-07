(** Common properties for smart contracts *)
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import BlockchainBase.
From ConCert.Execution Require Import BlockchainTheories.
From ConCert.Execution Require Import BlockchainInduction.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import SerializableBase.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Permutation.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.



Section NonRecursive.
  Context {Base : ChainBase}.
  (** A non-recursive smart contract is a contract that never calls itself,
      i.e. does not emit transfers or calls to itself from its receive function.
      This does not mean that the contract cannot enter a loop as indirect self calls
      are still allowed.

      A non-recursive smart contract can use the [nonrecursive_contract_induction]
      custom induction tactic which works like [contract_induction] but without a
      recursive call case.
  *)

  Definition NonRecursiveStrong  {Setup Msg State Error : Type}
                                `{Serializable Setup}
                                `{Serializable Msg}
                                `{Serializable State}
                                `{Serializable Error}
                                (contract : Contract Setup Msg State Error)
                                : Prop :=
    forall chain ctx prev_state msg new_state new_acts,
      contract.(receive) chain ctx prev_state msg = Ok (new_state, new_acts) ->
      Forall (fun act_body =>
        match act_body with
        | act_transfer to _ => (to =? ctx.(ctx_contract_address))%address = false
        | act_call to _ _ => (to =? ctx.(ctx_contract_address))%address = false
        | _ => True
        end) new_acts.

  Definition NonRecursive  {Setup Msg State Error : Type}
                          `{Serializable Setup}
                          `{Serializable Msg}
                          `{Serializable State}
                          `{Serializable Error}
                          (contract : Contract Setup Msg State Error)
                          : Prop :=
    forall bstate caddr,
      reachable bstate ->
      env_contracts bstate caddr = Some (contract : WeakContract) ->
        Forall (fun act_body =>
          match act_body with
          | act_transfer to _ => (to =? caddr)%address = false
          | act_call to _ _ => (to =? caddr)%address = false
          | _ => True
          end) (outgoing_acts bstate caddr).


  Lemma nonrecursive_strong_nonrecursive {Setup Msg State Error : Type}
                                        `{Serializable Setup}
                                        `{Serializable Msg}
                                        `{Serializable State}
                                        `{Serializable Error}
                                         (contract : Contract Setup Msg State Error) :
    NonRecursiveStrong contract ->
    NonRecursive contract.
  Proof.
    intros nonrecursive.
    unfold NonRecursive.
    contract_induction; intros.
    - apply Forall_nil.
    - apply Forall_nil.
    - now apply Forall_inv_tail in IH.
    - apply Forall_app.
      split; auto.
      apply nonrecursive in receive_some.
      assumption.
    - apply Forall_inv_tail in IH.
      apply Forall_app.
      split; auto.
      apply nonrecursive in receive_some.
      assumption.
    - eapply forall_respects_permutation; eauto.
    - solve_facts.
  Qed.

  Local Open Scope Z_scope.

  Lemma nonrecursive_contract_induction
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

    (NonRecursive contract) ->
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

    (* Queue permutation *)
    (forall height slot fin_height
            caddr dep_info cstate balance
            out_queue inc_calls out_txs
            out_queue'
            (IH : P height slot fin_height caddr dep_info cstate balance
                    out_queue inc_calls out_txs)
            (perm : Permutation out_queue out_queue')
            (tag : TagPermuteQueue),
        P height slot fin_height
          caddr dep_info cstate balance out_queue' inc_calls out_txs) ->

    forall bstate caddr (trace : ChainTrace empty_state bstate),
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
          (outgoing_txs trace caddr).
  Proof.
    intros nonrecursive facts_case block_case init_case outact_case receive_case perm_case.
    contract_induction; auto.
    instantiate (AddBlockFacts0 := AddBlockFacts).
    instantiate (DeployFacts0 := DeployFacts).
    instantiate (CallFacts0 :=
      fun chain ctx state out_queue in_queue =>
        CallFacts chain ctx state out_queue in_queue /\
        ctx_from ctx <> ctx_contract_address ctx).
    all: auto.
    - intros.
      clear facts_case block_case init_case outact_case perm_case.
      clear AddBlockFacts DeployFacts.
      now destruct facts as [? _].
    - intros.
      clear facts_case block_case init_case outact_case perm_case.
      clear AddBlockFacts DeployFacts.
      now destruct facts as [_ ?].
    - clear block_case init_case outact_case receive_case perm_case.
      intros.
      specialize (facts_case bstate_from bstate_to step from_reachable tag).
      solve_facts.
      split.
      + now apply facts_case.
      + apply trace_reachable in from_reachable as reachable.
        specialize (nonrecursive bstate_from to_addr reachable deployed0).
        unfold outgoing_acts in nonrecursive.
        rewrite queue_prev in nonrecursive.
        cbn in nonrecursive.
        destruct_address_eq; auto.
        inversion_clear nonrecursive as [|? ? hd _].
        destruct msg; now rewrite address_eq_refl in hd.
  Qed.

End NonRecursive.



Ltac nonrecursive_contract_induction :=
  generalize_contract_statement_with_post
    ltac:(fun bstate caddr _ is_deployed Setup Msg State Error P =>
      revert is_deployed;
      let AddBlockFacts := fresh "AddBlockFacts" in
      let DeployFacts := fresh "DeployFacts" in
      let CallFacts := fresh "CallFacts" in
      evar (AddBlockFacts :
              forall (chain_height : nat) (current_slot : nat)
                      (finalized_height : nat) (new_height : nat)
                      (new_slot : nat) (new_finalized_height : nat), Prop);
      evar (DeployFacts : forall (chain : Chain)
                                  (ctx : ContractCallContext), Prop);
      evar (CallFacts : forall (chain : Chain) (ctx : ContractCallContext)
                                (cstate : State) (outgoing_actions : list ActionBody)
                                (inc_calls : option (list (ContractCallInfo Msg))), Prop);
      apply (nonrecursive_contract_induction _ AddBlockFacts DeployFacts CallFacts);
      cbv [P]; clear P; cycle 2; clear dependent bstate; clear dependent caddr).



Section NonPayable.
  Context {Base : ChainBase}.
  Open Scope Z_scope.

  Definition NonPayable  {Setup Msg State Error : Type}
                        `{Serializable Setup}
                        `{Serializable Msg}
                        `{Serializable State}
                        `{Serializable Error}
                         (contract : Contract Setup Msg State Error)
                         : Prop :=
  (forall chain ctx prev_state msg,
    ctx.(ctx_amount) > 0 ->
    isErr (contract.(receive) chain ctx prev_state msg) = true
    ) /\
  (forall chain ctx setup,
    ctx.(ctx_amount) > 0 ->
    isErr (contract.(init) chain ctx setup) = true
    ).

  Definition NonPayableWeak  {Setup Msg State Error : Type}
                            `{Serializable Setup}
                            `{Serializable Msg}
                            `{Serializable State}
                            `{Serializable Error}
                             (contract : Contract Setup Msg State Error)
                             : Prop :=
  (forall chain ctx prev_state msg,
    ctx.(ctx_amount) > 0 ->
    isErr (contract.(receive) chain ctx prev_state msg) = true
    ).

  Lemma NonPayable_weaken  {Setup Msg State Error : Type}
                          `{Serializable Setup}
                          `{Serializable Msg}
                          `{Serializable State}
                          `{Serializable Error}
                           (contract : Contract Setup Msg State Error) :
    NonPayable contract ->
    NonPayableWeak contract.
  Proof.
    unfold NonPayableWeak, NonPayable.
    intros [? _].
    assumption.
  Qed.

  Lemma NonPayable_balance_zero  {Setup Msg State Error : Type}
                                `{Serializable Setup}
                                `{Serializable Msg}
                                `{Serializable State}
                                `{Serializable Error}
                                 (contract : Contract Setup Msg State Error) :
    NonPayable contract ->
    forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some (cstate : State) /\
      env_account_balances bstate caddr = 0.
  Proof.
    intros nonpayable.
    contract_induction; auto.
    instantiate (DeployFacts :=
      fun chain ctx => ctx.(ctx_amount) = 0).
    instantiate (CallFacts :=
      fun chain ctx state out_queue in_queue =>
        ctx.(ctx_amount) = 0).
    all: auto.
    - intros.
      rewrite IH.
      admit.
    - intros.
      rewrite facts in IH.
      lia.
    - intros.
      solve_facts.
      + (* apply trace_reachable in from_reachable as reachable.
        destruct nonpayable as [_ nonpayable].
        specialize (nonpayable bstate_from {|
                ctx_origin := origin;
                ctx_from := from_addr;
                ctx_contract_address := to_addr;
                ctx_contract_balance := amount;
                ctx_amount := amount
              |}).
        unfold outgoing_acts in nonrecursive.
        rewrite queue_prev in nonrecursive.
        cbn in nonrecursive.
        destruct_address_eq; auto.
        inversion_clear nonrecursive as [|? ? hd _].
        destruct msg; now rewrite address_eq_refl in hd. *)

        (* unfold NonPayable in nonpayable.
        destruct nonpayable as [_ nonpayable].
        cbn.
        apply Z.ge_le in amount_nonnegative.
        apply Zle_lt_or_eq in amount_nonnegative as [amount_nonnegative | amount_nonnegative]; auto.

        specialize (@wc_init_strong Base Setup Msg State Error H H0 H1 H2 contract (transfer_balance from_addr to_addr amount bstate_from)). intros H'.

        apply wc_init_strong in init_some as H.
        specialize (nonpayable (transfer_balance from_addr to_addr amount bstate_from) _ setup).
    *)
      admit.
      + (* apply wc_receive_strong in receive_some. *)
        admit.
  Admitted.

End NonPayable.



Section Payable.
  Context {Base : ChainBase}.

  Definition Payable  {Setup Msg State Error : Type}
                     `{Serializable Setup}
                     `{Serializable Msg}
                     `{Serializable State}
                     `{Serializable Error}
                      (contract : Contract Setup Msg State Error)
                      : Prop :=
    ~ NonPayable (contract : Contract Setup Msg State Error).
End Payable.



Section ConstantField.
  Context {Base : ChainBase}.

  Definition ConstantField  {Setup Msg State Error : Type}
                           `{Serializable Setup}
                           `{Serializable Msg}
                           `{Serializable State}
                           `{Serializable Error}
                            {A : Type}
                            (contract : Contract Setup Msg State Error)
                            (proj : State -> A)
                            : Prop :=
    forall chain ctx prev_state msg new_state new_acts,
      contract.(receive) chain ctx prev_state msg = Ok (new_state, new_acts) ->
        proj prev_state = proj new_state.
End ConstantField.



Section LocalBalance.
  Context {Base : ChainBase}.
  Open Scope Z_scope.

  Definition sum_acts acts :=
    sumZ (fun act => act_body_amount act) (acts).

  Definition LocalBalance  {Setup Msg State Error : Type}
                          `{Serializable Setup}
                          `{Serializable Msg}
                          `{Serializable State}
                          `{Serializable Error}
                           (contract : Contract Setup Msg State Error)
                           (proj : State -> Z)
                           : Prop :=
    (forall chain ctx prev_state msg new_state new_acts,
      contract.(receive) chain ctx prev_state msg = Ok (new_state, new_acts) ->
        proj prev_state = proj new_state - ctx.(ctx_amount) + sum_acts new_acts)
    /\
    (forall chain ctx setup new_state,
      contract.(init) chain ctx setup = Ok (new_state) ->
        proj new_state = ctx.(ctx_amount)).

  Definition LocalBalanceWeak  {Setup Msg State Error : Type}
                              `{Serializable Setup}
                              `{Serializable Msg}
                              `{Serializable State}
                              `{Serializable Error}
                               (contract : Contract Setup Msg State Error)
                               (proj : State -> Z)
                               : Prop :=
    (forall chain ctx prev_state msg new_state new_acts,
      contract.(receive) chain ctx prev_state msg = Ok (new_state, new_acts) ->
        proj prev_state = proj new_state - ctx.(ctx_amount) + sum_acts new_acts).

  Lemma LocalBalance_weaken  {Setup Msg State Error : Type}
                            `{Serializable Setup}
                            `{Serializable Msg}
                            `{Serializable State}
                            `{Serializable Error}
                             (contract : Contract Setup Msg State Error)
                             (proj : State -> Z) :
    LocalBalance contract proj ->
    LocalBalanceWeak contract proj.
  Proof.
    unfold LocalBalanceWeak, LocalBalance.
    intros [? _].
    assumption.
  Qed.
End LocalBalance.



Section Emptyable.
  Context {Base : ChainBase}.
  Open Scope Z_scope.

  Definition EmptyableStrong  {Setup Msg State Error : Type}
                             `{Serializable Setup}
                             `{Serializable Msg}
                             `{Serializable State}
                             `{Serializable Error}
                              (contract : Contract Setup Msg State Error)
                              : Prop :=
  forall chain ctx prev_state,
    ctx.(ctx_contract_balance) = 0 \/
    exists msg new_state new_acts,
      contract.(receive) chain ctx prev_state msg = Ok (new_state, new_acts) /\
      sum_acts new_acts > 0.
End Emptyable.
