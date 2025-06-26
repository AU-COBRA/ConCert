(* In this file we implement a Congress and prove it correct up to a
specification. The Congress is a simplified version of the DAO in
which members vote on proposals. We implement the contract in Gallina
and then show that it does not send out more transactions than
expected from the number of created proposals. *)

From Stdlib Require Import Psatz.
From Stdlib Require Import List. Import ListNotations.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Examples.Congress Require Import Congress.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.



Section Theories.
  Context {BaseTypes : ChainBase}.
  Local Open Scope nat.

  (* The rules stored in the blockchain's state are always valid *)
  Lemma rules_valid bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Congress.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      validate_rules cstate.(state_rules) = true.
  Proof.
    intros.
    apply (lift_contract_state_prop contract); intros *; auto.
    - intros init_some.
      cbn in init_some.
      unfold Congress.init in init_some.
      destruct_match eqn:validate_succeeds in init_some; try congruence.
      now inversion_clear init_some.
    - intros valid_prev receive.
      destruct msg as [[]|]; cbn in *;
        try solve [
              repeat
                match goal with
                | [H: Ok ?x = Ok ?y |- _] => inversion_clear H; auto
                | _ => try congruence; let H := fresh in destruct_match eqn:H in *
                end].
      + destruct_match in receive; try congruence.
        unfold vote_on_proposal in receive.
        destruct (FMap.find _ _); cbn in *; try congruence.
        now inversion_clear receive.
      + destruct_match in receive; try congruence.
        unfold vote_on_proposal in receive.
        destruct (FMap.find _ _); cbn in *; try congruence.
        now inversion_clear receive.
      + destruct_match in receive; try congruence.
        unfold do_retract_vote in receive.
        destruct (FMap.find _ _); cbn in *; try congruence.
        destruct (FMap.find _ _); cbn in *; try congruence.
        now inversion_clear receive.
      + now inversion receive; subst.
  Qed.

  Definition num_acts_created_in_proposals (calls : list (ContractCallInfo Congress.Msg)) :=
    let count call :=
        match call_msg call with
        | Some (create_proposal acts) => length acts
        | _ => 0
        end in
    sumnat count calls.

  Definition num_cacts_in_state state :=
    sumnat (fun '(k, v) => length (actions v)) (FMap.elements (proposals state)).

  Lemma num_cacts_in_state_deployment chain ctx setup state :
    init chain ctx setup = Ok state ->
    num_cacts_in_state state = 0.
  Proof.
    intros init.
    unfold Congress.init in init.
    destruct (validate_rules _); try congruence.
    now inversion init.
  Qed.

  Ltac remember_new_proposal :=
    match goal with
    | [|- context[FMap.add _ ?p]] => remember p as new_proposal
    end.

  Hint Resolve FMap.find_remove : core.

  Lemma add_proposal_cacts cacts chain state :
    num_cacts_in_state (add_proposal cacts chain state) <=
    num_cacts_in_state state + length cacts.
  Proof.
    unfold add_proposal, num_cacts_in_state.
    cbn.
    destruct (FMap.find (next_proposal_id state) (proposals state)) as [proposal|] eqn:find.
    - remember_new_proposal.
      rewrite <- (FMap.add_remove (next_proposal_id state) new_proposal).
      rewrite <- (FMap.add_id _ _ _ find) at 1.
      rewrite <- (FMap.add_remove (next_proposal_id state) proposal).
      repeat rewrite FMap.elements_add; auto.
      subst.
      cbn.
      lia.
    - rewrite FMap.elements_add; auto.
      cbn.
      lia.
  Qed.

  Lemma vote_on_proposal_cacts_preserved addr pid vote_val state new_state :
    vote_on_proposal addr pid vote_val state = Ok new_state ->
    num_cacts_in_state new_state = num_cacts_in_state state.
  Proof.
    intros vote.
    unfold vote_on_proposal in vote.
    destruct (FMap.find _ _) eqn:found; cbn in *; try congruence.
    inversion vote.
    unfold num_cacts_in_state.
    cbn.
    remember_new_proposal.
    rewrite <- (FMap.add_id pid p (proposals state)) at 1; auto.
    rewrite <- (FMap.add_remove pid p).
    rewrite <- (FMap.add_remove pid new_proposal).
    repeat rewrite FMap.elements_add; try apply FMap.find_remove.
    subst; reflexivity.
  Qed.

  Hint Resolve FMap.find_remove : core.

  Lemma do_retract_vote_cacts_preserved addr pid state new_state :
    do_retract_vote addr pid state = Ok new_state ->
    num_cacts_in_state new_state = num_cacts_in_state state.
  Proof.
    intros retract.
    unfold do_retract_vote in retract.
    destruct (FMap.find _ _) eqn:found; cbn in *; try congruence.
    destruct (FMap.find addr _); cbn in *; try congruence.
    inversion retract.
    unfold num_cacts_in_state.
    cbn.
    remember_new_proposal.
    rewrite <- (FMap.add_id pid p (proposals state)) at 1; auto.
    rewrite <- (FMap.add_remove pid p).
    rewrite <- (FMap.add_remove pid new_proposal).
    repeat rewrite FMap.elements_add; auto.
    subst; reflexivity.
  Qed.

  Lemma remove_proposal_cacts pid state proposal :
    FMap.find pid (proposals state) = Some proposal ->
    num_cacts_in_state (state <|proposals ::= FMap.remove pid|>) +
    length (actions proposal) = num_cacts_in_state state.
  Proof.
    intros find.
    unfold num_cacts_in_state.
    cbn.
    rewrite <- (FMap.add_id pid proposal (proposals state)) at 1; auto.
    rewrite <- FMap.add_remove.
    rewrite FMap.elements_add; auto.
    cbn.
    lia.
  Qed.

  (* The next lemma shows that when we send out transactions, the
  state change will make up for number of outgoing actions queued. *)
  Lemma receive_state_well_behaved
        chain ctx state msg new_state resp_acts :
    receive chain ctx state msg = Ok (new_state, resp_acts) ->
    num_cacts_in_state new_state + length resp_acts <=
    num_cacts_in_state state +
    match msg with
    | Some (create_proposal ls) => length ls
    | _ => 0
    end.
  Proof.
    intros receive.
    destruct msg as [[]|];
      cbn -[vote_on_proposal do_retract_vote do_finish_proposal] in *.
    - (* transfer_ownership *)
      destruct_address_eq; try congruence.
      inversion receive; auto.
    - (* change_rules *)
      destruct_address_eq; cbn in *; destruct (validate_rules r); inversion receive; auto.
    - (* add_member *)
      destruct_address_eq; cbn in *; inversion receive; auto.
    - (* remove_member *)
      destruct_address_eq; cbn in *; inversion receive; auto.
    - (* create_proposal *)
      destruct (FMap.mem _ _); inversion receive.
      cbn.
      rewrite <- plus_n_O.
      apply add_proposal_cacts.
    - (* vote_for_proposal *)
      destruct (FMap.mem _ _); try congruence.
      destruct (vote_on_proposal _ _ _ _) eqn:vote; cbn -[vote_on_proposal] in *; try congruence.
      inversion receive; subst.
      erewrite vote_on_proposal_cacts_preserved; eauto.
    - (* vote_against_proposal *)
      destruct (FMap.mem _ _); try congruence.
      destruct (vote_on_proposal _ _ _ _) eqn:vote; cbn -[vote_on_proposal] in *; try congruence.
      inversion receive; subst.
      erewrite vote_on_proposal_cacts_preserved; eauto.
    - (* retract_vote *)
      destruct (FMap.mem _ _); try congruence.
      destruct (do_retract_vote _ _ _) eqn:retract; cbn -[do_retract_vote] in *; try congruence.
      inversion receive; subst.
      erewrite do_retract_vote_cacts_preserved; eauto.
    - (* finish_proposal *)
      unfold do_finish_proposal in receive.
      destruct (FMap.find _ _) eqn:found; cbn in *; try congruence.
      match goal with
      | [H: (if ?a then _ else _) = Ok _ |- _] => destruct a
      end; cbn in *; try congruence.
      inversion receive.
      rewrite <- (remove_proposal_cacts _ _ _ found), length_map.
      destruct (proposal_passed _ _); cbn.
      + (* I wonder why these asserts are necessary... *)
        assert (forall a b, a + b <= a + b + 0) by (intros; lia); auto.
      + assert (forall a b, a + 0 <= a + b + 0) by (intros; lia); auto.
    - inversion receive; subst; cbn; lia.
  Qed.

  Theorem congress_correct bstate caddr (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (Congress.contract : WeakContract) ->
    exists (cstate : Congress.State) (inc_calls : list (ContractCallInfo Congress.Msg)),
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      num_cacts_in_state cstate +
      length (outgoing_txs trace caddr) +
      length (outgoing_acts bstate caddr) <=
      num_acts_created_in_proposals inc_calls.
  Proof.
    contract_induction; intros; cbn in *; auto; try lia.
    - erewrite num_cacts_in_state_deployment by eassumption.
      lia.
    - pose proof (receive_state_well_behaved _ _ _ _ _ _ receive_some) as fcorrect.
      fold (num_acts_created_in_proposals prev_inc_calls).
      rewrite length_app.
      lia.
    - pose proof (receive_state_well_behaved _ _ _ _ _ _ receive_some) as fcorrect.
      fold (num_acts_created_in_proposals prev_inc_calls).
      rewrite length_app.
      lia.
    - intros.
      now rewrite <- perm.
    - solve_facts.
  Qed.

  Theorem congress_correct_after_block
            {ChainBuilder : ChainBuilderType}
            prev new header acts :
    builder_add_block prev header acts = Ok new ->
    forall caddr,
      env_contracts new caddr = Some (Congress.contract : WeakContract) ->
      exists inc_calls,
        incoming_calls Msg (builder_trace new) caddr = Some inc_calls /\
        length (outgoing_txs (builder_trace new) caddr) <=
        num_acts_created_in_proposals inc_calls.
  Proof.
    intros add_block contract congress_at_addr.
    pose proof (congress_correct _ _ (builder_trace new) congress_at_addr)
        as general.
    destruct general as [? [inc_calls [? [? ?]]]].
    exists inc_calls.
    split; auto.
    cbn in *.
    lia.
  Qed.
End Theories.
