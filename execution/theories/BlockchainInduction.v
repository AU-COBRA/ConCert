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
From ConCert.Execution Require Import BlockchainTheories.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.



Section ContractInduction.
  Context {Base : ChainBase}.

  Inductive TagFacts := tag_facts.
  Inductive TagAddBlock := tag_add_block.
  Inductive TagDeployment := tag_deployment.
  Inductive TagOutgoingAct := tag_outgoing_act.
  Inductive TagNonrecursiveCall := tag_nonrecursive_call.
  Inductive TagRecursiveCall := tag_recursive_call.
  Inductive TagPermuteQueue := tag_permute_queue.

  Hint Constructors
    TagFacts TagAddBlock TagDeployment TagOutgoingAct
    TagNonrecursiveCall TagRecursiveCall TagPermuteQueue : core.

  Local Open Scope Z_scope.

  Lemma contract_induction
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
    intros establish_facts
          add_block_case
          init_case
          transfer_case
          nonrecursive_call_case
          recursive_call_case
          permute_queue_case
          bstate caddr trace contract_deployed.
    assert (address_is_contract caddr = true) as is_contract
        by (eapply contract_addr_format; eauto).
    unfold contract_state in *.
    remember empty_state; induction trace as [|? ? ? ? IH];
      intros; subst; try solve [cbn in *; congruence].
    specialize (IH ltac:(auto) ltac:(auto)).
    specialize (establish_facts mid to ltac:(auto) ltac:(auto) tag_facts).
    destruct_chain_step;
      [|clear add_block_case; destruct_action_eval; rewrite_environment_equiv in *; cbn in *| |].
    - (* New block *)
      clear init_case recursive_call_case nonrecursive_call_case permute_queue_case.
      rewrite_environment_equiv in *.
      specialize_hypotheses.
      cbn in *.
      destruct IH as (depinfo' & cstate' & inc_calls' & -> & ? & -> & ?).
      exists depinfo', cstate', inc_calls'.
      rewrite_environment_equiv in *.
      repeat split; auto.
      inversion valid_header.
      cbn in *.
      destruct_address_eq; try congruence.
      rewrite outgoing_acts_after_block_nil by auto.
      unfold outgoing_acts in *; rewrite queue_prev in *; cbn in *.
      eapply add_block_case; try constructor.
      + apply establish_facts.
      + assumption.
    - (* Evaluation: transfer *)
      clear init_case recursive_call_case nonrecursive_call_case permute_queue_case.
      specialize_hypotheses.
      destruct IH as (depinfo' & cstate' & inc_calls' & -> & ? & -> & ?).
      exists depinfo', cstate', inc_calls'.
      rewrite_environment_equiv in *.
      repeat split; auto.
      rewrite (address_eq_sym from_addr) in *.
      cbn in *.
      (* Transfer cannot be to contract as that would be a
      call. Resolve this now. *)
      destruct (address_eqb_spec caddr to_addr) as [->|];
        cbn in *; try congruence.

      unfold outgoing_acts in *.
      rewrite queue_prev, queue_new in *.
      match goal with
      | [ H : act = _ |- _ ] => rewrite H in *
      end.
      subst.
      cbn in *.
      rewrite (address_eq_sym from_addr) in *.
      destruct (address_eqb_spec caddr from_addr) as [<-|];
        cbn in *.
      + (* Transfer from contract *)
        remember (act_transfer _ _) as out_act.
        replace (-amount + env_account_balances mid caddr) with
            (env_account_balances mid caddr - act_body_amount out_act) by
            (subst; cbn; lia).
        subst.
        apply transfer_case; auto.
      + (* Irrelevant transfer *)
        auto.
    - (* Evaluation: Deploy *)
      clear recursive_call_case nonrecursive_call_case permute_queue_case.
      rewrite (address_eq_sym to_addr caddr) in *.
      destruct (address_eqb_spec caddr to_addr) as [<-|]; cbn in *.
      + (* Deployment of this contract *)
        replace wc with (contract : WeakContract) in * by congruence.
        match goal with
        | [ H : wc_init _ _ _ _ = Ok _ |- _ ] =>
          destruct (wc_init_strong H) as (setup_strong & result_strong & deser_setup_eq & <- & init)
        end.
        rewrite deser_setup_eq in *.
        exists (build_deployment_info origin from_addr amount setup_strong),
              result_strong,
              [].
        rewrite_environment_equiv in *; cbn.

        rewrite address_eq_refl.
        cbn.
        rewrite deserialize_serialize.
        assert (incoming_calls Msg trace caddr = Some [])
          by (apply undeployed_contract_no_in_calls; auto).
        unfold incoming_calls in *; rewrite is_contract in *.
        repeat split; cbn in *; subst; auto.
        unfold outgoing_acts.
        rewrite queue_new.
        cbn.
        rewrite (address_eq_sym caddr) in *.
        fold (outgoing_txs trace caddr).
        pose proof (undeployed_contract_no_out_queue
                      caddr mid ltac:(auto) ltac:(auto) ltac:(auto)) as queue_ne_to.
        rewrite queue_prev in queue_ne_to.
        inversion_clear queue_ne_to as [|? ? from_ne_to rest_ne_to].
        cbn in from_ne_to.
        cbn in *.
        rewrite (address_eq_ne from_addr caddr) by (destruct_address_eq; auto).
        rewrite Forall_false_filter_nil by assumption.
        rewrite undeployed_contract_no_out_txs, undeployed_contract_balance_0 by auto.
        remember (build_ctx _ _ _ _ _) as ctx.
        replace origin with (ctx_origin ctx) by (subst; auto).
        replace from_addr with (ctx_from ctx) by (subst; auto).
        replace caddr with (ctx_contract_address ctx) by (subst; auto).
        replace amount with (ctx_amount ctx) by (subst; auto).
        rewrite Z.add_0_r.
        apply init_case; auto.
      + (* Deployment of other contract, might be by this contract. *)
        specialize_hypotheses.
        destruct IH as (depinfo & cstate & inc_calls & -> & ? & -> & ?).
        exists depinfo, cstate, inc_calls.
        rewrite_environment_equiv in *; cbn.
        rewrite address_eq_ne by auto.
        repeat split; auto.
        rewrite (address_eq_sym caddr).
        unfold outgoing_acts in *.
        rewrite queue_prev, queue_new in *.
        match goal with
        | [ H : act = _ |- _ ] => rewrite H in *
        end.
        subst new_acts.
        cbn in *.
        fold (outgoing_txs trace caddr).
        destruct_address_eq; subst; cbn in *; auto.
        (* This contract deploys other contract *)
        remember (act_deploy _ _ _) as abody.
        replace (-amount + env_account_balances mid caddr)
          with (env_account_balances mid caddr - act_body_amount abody)
          by (subst; cbn; lia).
        subst.
        apply transfer_case; auto.
    - (* Evaluation: Call *)
      clear init_case permute_queue_case.
      specialize_hypotheses.
      match goal with
        | [ H : act = _ |- _ ] => rewrite H in *
      end.
      subst new_acts.
      destruct IH as (depinfo & cstate & inc_calls & -> & ? & inc_calls_eq & IH).
      (* rewrite inc_calls_eq in *. *)
      unfold outgoing_acts in *.
      rewrite queue_prev, queue_new in *.
      cbn in *.
      rewrite filter_app, filter_map, map_app, map_map; cbn in *.
      destruct (address_eqb_spec to_addr caddr) as [->|].
      + (* Call to contract *)
        rewrite inc_calls_eq in *.
        replace wc with (contract : WeakContract) in * by congruence.
        destruct (wc_receive_strong ltac:(eassumption))
          as (prev_state_strong & msg_strong & resp_state_strong &
              deser_state & deser_msg & <- & receive).
        replace (env_contract_states mid caddr) with (Some prev_state) in * by auto.
        cbn in *.
        replace prev_state_strong with cstate in * by congruence; clear prev_state_strong.
        exists depinfo, resp_state_strong.
        exists (build_call_info origin from_addr amount msg_strong :: inc_calls).
        rewrite_environment_equiv in *.
        cbn.
        rewrite address_eq_refl.
        cbn.
        rewrite deserialize_serialize.
        repeat split; auto.
        {
          destruct msg_strong as [msg_strong|], msg as [msg|];
            try solve [cbn in *; congruence].
          now replace (deserialize msg) with (Some msg_strong) by auto.
        }

        rewrite (address_eq_sym caddr), filter_true, map_id.

        destruct (address_eqb_spec from_addr caddr) as [->|?]; cbn in *.
        all: rewrite (address_eq_refl caddr) in *.
        * (* Recursive call *)
          remember (build_ctx _ _ _ _ _) as ctx.
          pose proof
              (recursive_call_case
                (transfer_balance caddr caddr amount mid)
                ctx depinfo cstate msg_strong
                (match msg with
                  | Some msg => act_call caddr amount msg
                  | None => act_transfer caddr amount
                  end)) as case.
          subst ctx.
          cbn in case.
          replace (-amount + (amount + env_account_balances mid caddr))
            with (env_account_balances mid caddr)
            in * by lia.
          destruct msg_strong as [msg_strong|], msg as [msg|];
            cbn in *; try congruence; auto.
        * (* Someone else calls contract *)
          remember (build_ctx _ _ _ _ _) as ctx.
          pose proof
              (nonrecursive_call_case
                (transfer_balance from_addr caddr amount mid)
                ctx depinfo cstate msg_strong) as case.
          subst ctx.
          cbn in case.
          rewrite (address_eq_ne caddr from_addr) in * by (subst; auto).
          replace (amount + env_account_balances mid caddr - amount)
            with (env_account_balances mid caddr) in case
            by lia.
          fold (outgoing_txs trace caddr).
          apply case; auto.
      + (* Call to other contract *)
        exists depinfo, cstate, inc_calls.
        rewrite_environment_equiv in *.
        rewrite filter_false.
        cbn.
        rewrite address_eq_ne by auto.
        rewrite (address_eq_sym caddr).
        destruct (address_eqb_spec from_addr caddr) as [->|?].
        * (* Call from us to other contract *)
          repeat split; auto.
          fold (outgoing_txs trace caddr).
          cbn in *.
          destruct msg as [msg|].
          1: remember (act_call _ _ _) as abody.
          2: remember (act_transfer _ _) as abody.
          1, 2: replace (-amount + env_account_balances mid caddr)
            with (env_account_balances mid caddr - act_body_amount abody)
            by (subst; cbn; lia).
          1, 2: subst; apply transfer_case; auto.
        * (* Irrelevant call. *)
          fold (outgoing_txs trace caddr).
          auto.
    - (* Invalid User Action *)
      rewrite_environment_equiv in *.
      destruct IH as (depinfo & cstate & inc_calls & ? & ? & ? & IH); auto.
      exists depinfo, cstate, inc_calls.
      repeat split; try rewrite_environment_equiv in *; auto.
      assert (outgoing_acts_eq : outgoing_acts mid caddr = outgoing_acts to caddr).
      { unfold outgoing_acts.
        setoid_rewrite queue_new.
        setoid_rewrite queue_prev.
        f_equal.
        cbn.
        unfold act_is_from_account in act_from_acc.
        destruct_address_eq; easy.
      }
      rewrite outgoing_acts_eq in IH.
      cbn.
      now fold (outgoing_txs trace caddr).
    - (* Permutation *)
      rewrite_environment_equiv in *.
      specialize_hypotheses.
      destruct IH as (depinfo & cstate & inc_calls & ? & ? & ? & IH).
      exists depinfo, cstate, inc_calls.
      rewrite_environment_equiv in *.
      cbn.
      repeat split; auto.
      unfold outgoing_acts in *.
      fold (outgoing_txs trace caddr).
      apply permute_queue_case with
          (out_queue := map act_body
                            (filter (fun a => (act_from a =? caddr)%address)
                                    (chain_state_queue mid))); auto.
      now apply Permutation_map, Permutation_filter.
  Qed.

End ContractInduction.



Local Ltac generalize_contract_statement_aux
      bstate caddr trace is_deployed Setup Msg State Error post :=
  let P := fresh "P" in
  evar (P : forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                   (caddr : Address) (deployment_info : DeploymentInfo Setup)
                   (cstate : State) (balance : Amount)
                   (outgoing_actions_queued : list ActionBody)
                   (incoming_calls_seen : list (ContractCallInfo Msg))
                   (outgoing_txs_seen : list Tx),
           Prop);
  let H := fresh "H" in
  enough (H: exists (dep : DeploymentInfo Setup)
                    (cstate : State)
                    (inc_calls : list (ContractCallInfo Msg)),
             deployment_info Setup trace caddr = Some dep /\
             contract_state bstate caddr = Some cstate /\
             incoming_calls Msg trace caddr = Some inc_calls /\
             P (chain_height bstate)
               (current_slot bstate)
               (finalized_height bstate)
               caddr dep cstate
               (env_account_balances bstate caddr)
               (outgoing_acts bstate caddr)
               inc_calls (outgoing_txs trace caddr));
  [let depinfo := fresh "depinfo" in
   let cstate := fresh "cstate" in
   let inc_calls := fresh "inc_calls" in
   let depinfo_strong := fresh "depinfo_strong" in
   let cstate_strong := fresh "cstate_strong" in
   let inc_calls_strong := fresh "inc_calls_strong" in
   let provenP := fresh "provenP" in
   destruct H as (depinfo & cstate & inc_calls &
                  depinfo_strong & cstate_strong & inc_calls_strong & provenP);
   repeat
     match goal with
     | [|- exists _ : DeploymentInfo Setup, _] => exists depinfo
     | [|- exists _ : State, _] => exists cstate
     | [|- exists _ : list (ContractCallInfo Msg), _] => exists inc_calls
     | [|- ?a /\ ?b] => refine (conj depinfo_strong _)
     | [|- ?a /\ ?b] => refine (conj cstate_strong _)
     | [|- ?a /\ ?b] => refine (conj inc_calls_strong _)
     end;
   pattern (chain_height bstate), (current_slot bstate), (finalized_height bstate),
           caddr, depinfo, cstate, (env_account_balances bstate caddr),
           (outgoing_acts bstate caddr), inc_calls, (outgoing_txs trace caddr);
   match goal with
   | [|- ?f _ _ _ _ _ _ _ _ _ _] => instantiate (P := f); exact provenP
   end
  | post bstate caddr trace is_deployed Setup Msg State Error P ].

Ltac generalize_contract_statement_with_post post :=
  intros;
  match goal with
  | [bstate : ChainState, caddr : Address |- _] =>
    try
      match goal with
      | [is_reachable : reachable bstate |- _] =>
        let trace := fresh "trace" in
        destruct is_reachable as [trace]
      end;
    match goal with
      [trace : ChainTrace empty_state bstate,
               is_deployed : env_contracts (_ bstate) caddr =
                             Some (contract_to_weak_contract ?c) |- _] =>
      match type of c with
      | Contract ?Setup ?Msg ?State ?Error =>
        generalize_contract_statement_aux bstate caddr trace
                                          is_deployed Setup Msg State Error post
      end
    end
  end.

Ltac generalize_contract_statement :=
  generalize_contract_statement_with_post
    ltac:(fun _ _ _ is_deployed _ _ _ _ => revert is_deployed).

Ltac contract_induction :=
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
       apply (contract_induction _ AddBlockFacts DeployFacts CallFacts);
       [|clear DeployFacts CallFacts
        |clear AddBlockFacts CallFacts
        |clear AddBlockFacts DeployFacts CallFacts
        |clear AddBlockFacts DeployFacts
        |clear AddBlockFacts DeployFacts
        |clear AddBlockFacts DeployFacts CallFacts];
       cbv [P]; clear P; cycle 1; clear dependent bstate; clear dependent caddr).

Global Notation "'Please' 'prove' 'your' 'facts'" :=
  TagFacts (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'addition' 'of' 'a' 'block'" :=
  TagAddBlock (at level 100, only printing).
Global Notation "'Please' 'establish' 'the' 'invariant' 'after' 'deployment' 'of' 'the' 'contract'" :=
  TagDeployment (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'an' 'outgoing' 'action'" :=
  TagOutgoingAct (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'a' 'nonrecursive' 'call'" :=
  TagNonrecursiveCall (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'a' 'recursive' 'call'" :=
  TagRecursiveCall (at level 100, only printing).
Global Notation
       "'Please' 'reestablish' 'the' 'invariant' 'after' 'permutation' 'of' 'the' 'action' 'queue'" :=
  TagPermuteQueue (at level 100, only printing).


Tactic Notation "set_block_facts" uconstr(g) :=
  let x := type_term (g : nat -> nat -> nat -> nat -> nat -> nat -> Prop) in
  match goal with
  | H := ?f : nat -> nat -> nat -> nat -> nat -> nat -> Prop |- _ =>
      is_evar f; instantiate (H := g); subst H;
      match goal with
      | H : ((fun (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) => _) _ _ _ _ _ _) |- _ =>
        cbn in H
      end
  | _ => fail "Could not instantiate AddBlockFacts"
  end.

Tactic Notation "set_block_facts" uconstr(g) "as" simple_intropattern(L) :=
  let x := type_term (g : nat -> nat -> nat -> nat -> nat -> nat -> Prop) in
  match goal with
  | H := ?f : nat -> nat -> nat -> nat -> nat -> nat -> Prop |- _ =>
      is_evar f; instantiate (H := g); subst H;
      match goal with
      | H : ((fun (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) => _) _ _ _ _ _ _) |- _ =>
        cbn in H; destruct H as L
      end
  | _ => fail "Could not instantiate AddBlockFacts"
  end.

Tactic Notation "set_deploy_facts" uconstr(g) :=
  let x := type_term (g : Chain -> ContractCallContext -> Prop) in
  match goal with
  | H := ?f : Chain -> ContractCallContext -> Prop |- _ =>
      is_evar f; instantiate (H := g); subst H;
      match goal with
      | H : ((fun (_ : Chain) (_ : ContractCallContext) => _) _ _) |- _ =>
        cbn in H
      end
  | _ => fail "Could not instantiate DeployFacts"
  end.

Tactic Notation "set_deploy_facts" uconstr(g) "as" simple_intropattern(L) :=
  let x := type_term (g : Chain -> ContractCallContext -> Prop) in
  match goal with
  | H := ?f : Chain -> ContractCallContext -> Prop |- _ =>
      is_evar f; instantiate (H := g); subst H;
      match goal with
      | H : ((fun (_ : Chain) (_ : ContractCallContext) => _) _ _) |- _ =>
        cbn in H; destruct H as L
      end
  | _ => fail "Could not instantiate DeployFacts"
  end.

Tactic Notation "set_call_facts" uconstr(g) :=
  match goal with
  | H := ?f : Chain -> ContractCallContext -> _ -> list ActionBody -> option (list (ContractCallInfo _)) -> Prop |- _ =>
      is_evar f; instantiate (H := g); subst H;
      match goal with
      | H : ((fun (_ : Chain) (_ : ContractCallContext) _ (_ : list ActionBody) (_ : option (list (ContractCallInfo _))) => _) _ _ _ _ _) |- _ =>
        cbn in H
      end
  | _ => fail "Could not instantiate CallFacts"
  end.

Tactic Notation "set_call_facts" uconstr(g) "as" simple_intropattern(L) :=
  match goal with
  | H := ?f : Chain -> ContractCallContext -> _ -> list ActionBody -> option (list (ContractCallInfo _)) -> Prop |- _ =>
      is_evar f; instantiate (H := g); subst H;
      match goal with
      | H : ((fun (_ : Chain) (_ : ContractCallContext) _ (_ : list ActionBody) (_ : option (list (ContractCallInfo _))) => _) _ _ _ _ _) |- _ =>
        cbn in H; destruct H as L
      end
  | _ => fail "Could not instantiate CallFacts"
  end.

Ltac split_facts_aux H :=
  match goal with
  | [H': _ /\ _ |- _] =>
    match H' with H =>
      let x := fresh "fact" in
      let y := fresh "fact" in
      destruct H as [x y];
      try split_facts_aux y
    end
  end.

Tactic Notation "split_facts" "in" hyp(H) :=
  split_facts_aux H.
Tactic Notation "split_facts" "in" hyp(H) "as" simple_intropattern(L) :=
  match goal with
  | [H': _ /\ _ |- _] =>
    match H' with H =>
      destruct H as L
    end
  end.


Ltac solve_facts :=
  repeat match goal with
    | H := ?f : nat -> nat -> nat -> nat -> nat -> nat -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ _ => Logic.True)
    | H := ?f : _ -> ContractCallContext -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ => Logic.True)
    | H := ?f : Chain -> ContractCallContext -> _ ->
    list ActionBody -> option (list (ContractCallInfo _)) -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ => Logic.True)
    end;
    unset_all; subst;
    destruct_chain_step; [
       auto
     | destruct_action_eval; [
         auto
       | auto
       | auto; intros ?cstate ?deployed ?deployed_state;
          cbn; subst
       ]
     | auto
     | auto
    ].



Section LiftTransactionProp.
  Context {BaseTypes : ChainBase}
          {Setup Msg State Error : Type}
         `{Serializable Setup}
         `{Serializable Msg}
         `{Serializable State}
         `{Serializable Error}.

  (** If some property [P] holds for all actions in the output of the receive function,
      the property can be lifted to all outgoing actions for all reachable states. *)
  Lemma lift_outgoing_acts_prop
          {P : ActionBody -> Prop}
          (contract : Contract Setup Msg State Error)
          (bstate : ChainState)
          (addr : Address) :
    reachable bstate ->
    (forall chain ctx cstate msg new_cstate acts,
        contract.(receive) chain ctx cstate msg = Ok (new_cstate, acts) ->
        Forall P acts) ->
    env_contracts bstate addr = Some (contract : WeakContract) ->
    Forall P (outgoing_acts bstate addr).
  Proof.
    intros Hr Hc.
    contract_induction; intros; cbn in *; auto.
    - inversion_clear IH; auto.
    - apply Forall_app.
      split; auto.
      eauto.
    - apply Forall_app.
      inversion_clear IH.
      split; auto.
      eauto.
    - now rewrite <- perm.
    - solve_facts.
  Qed.

  (** If the receive function always returns an empty list of actions,
  the same holds for all reachable states *)
  Lemma lift_outgoing_acts_nil
          (contract : Contract Setup Msg State Error)
          (bstate : ChainState)
          (addr : Address) :
    reachable bstate ->
    (forall chain ctx cstate msg new_cstate acts,
        contract.(receive) chain ctx cstate msg = Ok (new_cstate, acts) ->
        acts = []) ->
    env_contracts bstate addr = Some (contract : WeakContract) ->
    outgoing_acts bstate addr = [].
  Proof.
    intros.
    enough (all_false: Forall (fun _ => False) (outgoing_acts bstate addr)) by (now destruct all_false).
    apply (lift_outgoing_acts_prop contract); auto.
    intros.
    erewrite (H4 _ _ _ _ _ acts); [constructor|eassumption].
  Qed.

  (** If some property [P] holds for all contract states in the output of the receive function,
    the property can be lifted to all contract states for all reachable states. *)
  Lemma lift_contract_state_prop
          {P : State -> Prop}
          (contract : Contract Setup Msg State Error)
          (bstate : ChainState)
          (addr : Address) :
    (forall chain ctx setup result,
        contract.(init) chain ctx setup = Ok result ->
        P result) ->
    (forall chain ctx cstate msg new_cstate acts,
        P cstate ->
        contract.(receive) chain ctx cstate msg = Ok (new_cstate, acts) ->
        P new_cstate) ->
    reachable bstate ->
    env_contracts bstate addr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate addr = Some cstate
      /\ P cstate.
  Proof.
    intros Hinit Hreceive Hreach.
    contract_induction; intros; cbn in *; auto.
    - now eapply Hinit.
    - now eapply Hreceive.
    - now eapply Hreceive.
    - solve_facts.
  Qed.

  Lemma lift_dep_info_contract_state_prop
          {P : DeploymentInfo Setup -> State -> Prop}
          (contract : Contract Setup Msg State Error)
          (bstate : ChainState)
          (addr : Address)
          (trace : ChainTrace empty_state bstate) :
    (forall chain ctx setup result,
        contract.(init) chain ctx setup = Ok result ->
        P (build_deployment_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) setup)
          result) ->
    (forall chain ctx cstate msg new_cstate acts dep,
        P dep cstate ->
        contract.(receive) chain ctx cstate msg = Ok (new_cstate, acts) ->
        P dep new_cstate) ->
    env_contracts bstate addr = Some (contract : WeakContract) ->
    exists dep cstate,
        deployment_info Setup trace addr = Some dep /\
        contract_state bstate addr = Some cstate /\
        P dep cstate.
  Proof.
    intros Hinit Hreceive.
    contract_induction; intros; cbn in *; auto.
    - now eapply Hinit.
    - now eapply Hreceive.
    - now eapply Hreceive.
    - solve_facts.
  Qed.

End LiftTransactionProp.
