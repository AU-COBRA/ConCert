(* In this file we introduce a reentrancy problem in the Congress
contract described in Congress.v. We then use one of our blockchain
implementations (the depth first local blockchain) to prove that this
version can send out too many transactions. This is done by
constructing a contract that actually exploits this version of the
Congress and then just asking Coq to compute. *)

From Coq Require Import ZArith.
From Coq Require Import Psatz.
From Coq Require Import List.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution.Test Require LocalBlockchain.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.


Section CongressBuggy.
  Context {BaseTypes : ChainBase}.

  Local Open Scope Z.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  Definition ProposalId := nat.

  Inductive CongressAction :=
  | cact_transfer (to : Address) (amount : Amount)
  | cact_call (to : Address) (amount : Amount) (msg : SerializedValue).

  Record Proposal :=
    build_proposal {
      actions : list CongressAction;
      votes : FMap Address Z;
      vote_result : Z;
      proposed_in : nat;
    }.

  MetaCoq Run (make_setters Proposal).

  Record Rules :=
    build_rules {
      min_vote_count_permille : Z;
      margin_needed_permille : Z;
      debating_period_in_blocks : nat;
    }.

  Record Setup :=
    build_setup {
      setup_rules : Rules;
    }.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Inductive Msg :=
  | transfer_ownership : Address -> Msg
  | change_rules : Rules -> Msg
  | add_member : Address -> Msg
  | remove_member : Address -> Msg
  | create_proposal : list CongressAction -> Msg
  | vote_for_proposal : ProposalId -> Msg
  | vote_against_proposal : ProposalId -> Msg
  | retract_vote : ProposalId -> Msg
  | finish_proposal : ProposalId -> Msg
  | finish_proposal_remove : ProposalId -> Msg.

  Record State :=
    build_state {
      owner : Address;
      state_rules : Rules;
      proposals : FMap nat Proposal;
      next_proposal_id : ProposalId;
      members : FMap Address unit;
    }.

  (* begin hide *)
  MetaCoq Run (make_setters State).
  (* end hide *)

  Section Serialization.

    Global Instance rules_serializable : Serializable Rules :=
      Derive Serializable Rules_rect <build_rules>.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance congress_action_serializable : Serializable CongressAction :=
      Derive Serializable CongressAction_rect <cact_transfer, cact_call>.

    Global Instance proposal_serializable : Serializable Proposal :=
      Derive Serializable Proposal_rect <build_proposal>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <transfer_ownership, change_rules, add_member, remove_member,
                                    create_proposal, vote_for_proposal, vote_against_proposal,
                                    retract_vote, finish_proposal, finish_proposal_remove>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.

  Definition validate_rules (rules : Rules) : bool :=
    (rules.(min_vote_count_permille) >=? 0)
    && (rules.(min_vote_count_permille) <=? 1000)
    && (rules.(margin_needed_permille) >=? 0)
    && (rules.(margin_needed_permille) <=? 1000)
    && (0 <=? rules.(debating_period_in_blocks))%nat.

  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : Setup)
                  : result State Error :=
    if validate_rules setup.(setup_rules) then
      Ok {|
        owner := ctx.(ctx_from);
        state_rules := setup.(setup_rules);
        proposals := FMap.empty;
        next_proposal_id := 1%nat;
        members := FMap.empty
      |}
    else
      Err default_error.

  Definition add_proposal (actions : list CongressAction)
                          (chain : Chain)
                          (state : State)
                          : State :=
    let id := state.(next_proposal_id) in
    let slot_num := chain.(current_slot) in
    let proposal := {| actions := actions;
                      votes := FMap.empty;
                      vote_result := 0;
                      proposed_in := slot_num |} in
    state<|proposals ::= FMap.add id proposal|>
        <|next_proposal_id ::= S|>.

  Definition vote_on_proposal (voter : Address)
                              (pid : ProposalId)
                              (vote : Z)
                              (state : State)
                              : result State Error :=
    do proposal <- result_of_option (FMap.find pid state.(proposals)) default_error;
    let old_vote := match FMap.find voter proposal.(votes) with
                  | Some old => old
                  | None => 0
                  end in
    let new_votes := FMap.add voter vote proposal.(votes) in
    let new_vote_result := proposal.(vote_result) - old_vote + vote in
    let new_proposal :=
        proposal<|votes := new_votes|>
                <|vote_result := new_vote_result|> in
    Ok (state<|proposals ::= FMap.add pid new_proposal|>).

  Definition do_retract_vote (voter : Address)
                             (pid : ProposalId)
                             (state : State)
                             : result State Error :=
    do proposal <- result_of_option (FMap.find pid state.(proposals)) default_error;
    do old_vote <- result_of_option (FMap.find voter proposal.(votes)) default_error;
    let new_votes := FMap.remove voter proposal.(votes) in
    let new_vote_result := proposal.(vote_result) - old_vote in
    let new_proposal :=
        proposal<|votes := new_votes|>
                <|vote_result := new_vote_result|> in
    Ok (state<|proposals ::= FMap.add pid new_proposal|>).

  Definition congress_action_to_chain_action (act : CongressAction) : ActionBody :=
    match act with
    | cact_transfer to amt => act_transfer to amt
    | cact_call to amt msg => act_call to amt msg
    end.

  Definition proposal_passed (proposal : Proposal)
                             (state : State)
                             : bool :=
    let rules := state.(state_rules) in
    let total_votes_for_proposal := Z.of_nat (FMap.size proposal.(votes)) in
    let total_members := Z.of_nat (FMap.size state.(members)) in
    let aye_votes := (proposal.(vote_result) + total_votes_for_proposal) / 2 in
    let vote_count_permille := total_votes_for_proposal * 1000 / total_members in
    let aye_permille := aye_votes * 1000 / total_votes_for_proposal in
    let enough_voters := vote_count_permille >=? rules.(min_vote_count_permille) in
    let enough_ayes := aye_permille >=? rules.(margin_needed_permille) in
    enough_voters && enough_ayes.

  Definition do_finish_proposal (ctx : ContractCallContext)
                                (pid : ProposalId)
                                (state : State)
                                (chain : Chain)
                                : result (State * list ActionBody) Error :=
    do proposal <- result_of_option (FMap.find pid state.(proposals)) default_error;
    let rules := state.(state_rules) in
    let debate_end := (proposal.(proposed_in) + rules.(debating_period_in_blocks))%nat in
    let cur_slot := chain.(current_slot) in
    if (cur_slot <? debate_end)%nat then
      Err default_error
    else
      let response_acts :=
          if proposal_passed proposal state
          then proposal.(actions)
          else [] in
      let response_chain_acts := map congress_action_to_chain_action response_acts in
      let self_call_msg := serialize (finish_proposal_remove pid) in
      let self_call := act_call (ctx_contract_address ctx) 0 self_call_msg in
        Ok (state, response_chain_acts ++ [self_call]).

  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (state : State)
                     (maybe_msg : option Msg)
                     : result (State * list ActionBody) Error :=
    let sender := ctx.(ctx_from) in
    let is_from_owner := (sender =? state.(owner))%address in
    let is_from_member := FMap.mem sender state.(members) in
    match maybe_msg, is_from_owner, is_from_member with
    | Some (transfer_ownership new_owner), true, _ =>
      Ok (state<|owner := new_owner|>, [])

    | Some (change_rules new_rules), true, _ =>
      if validate_rules new_rules then
        Ok (state<|state_rules := new_rules|>, [])
      else
        Err default_error

    | Some (add_member new_member), true, _ =>
      Ok (state<|members ::= FMap.add new_member tt|>, [])

    | Some (remove_member old_member), true, _ =>
      Ok (state<|members ::= FMap.remove old_member|>, [])

    | Some (create_proposal actions), _, true =>
      Ok (add_proposal actions chain state, [])

    | Some (vote_for_proposal pid), _, true =>
      without_actions (vote_on_proposal sender pid 1 state)

    | Some (vote_against_proposal pid), _, true =>
      without_actions (vote_on_proposal sender pid (-1) state)

    | Some (retract_vote pid), _, true =>
      without_actions (do_retract_vote sender pid state)

    | Some (finish_proposal pid), _, _ =>
      do_finish_proposal ctx pid state chain

    | Some (finish_proposal_remove pid), _, _ =>
      if (sender =? ctx_contract_address ctx)%address then
        Ok (state<|proposals ::= FMap.remove pid|>, [])
      else
        Err default_error

    | _, _, _ =>
          Err default_error
    end.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End CongressBuggy.
(* We will show that this contract is buggy and does not satisfy the
   property we proved for the other version of the Congress. We do
   this with a counterexample, where we exploit reentrancy similar to
   the DAO hack. We first define a contract that does this
   exploitation. *)

Section ExploitContract.
  Context {Base : ChainBase}.

  Definition ExploitSetup := unit.
  Definition ExploitState := nat. (* how many times have we called ourselves *)
  Definition ExploitMsg := unit.
  Definition ExploitError := nat.
  Definition exploit_init (chain : Chain)
                          (ctx : ContractCallContext)
                          (setup : ExploitSetup)
                          : result ExploitState ExploitError :=
    Ok 0.

  Definition exploit_receive
              (chain : Chain)
              (ctx : ContractCallContext)
              (state : ExploitState)
              (msg : option ExploitMsg)
              : result (ExploitState * list ActionBody) ExploitError :=
    if 25 <? state then
      Ok (state, [])
    else
      let again := finish_proposal 1 in
      Ok (S state, [act_call (ctx_from ctx) 0 (serialize again)]).

  Definition exploit_contract : Contract ExploitSetup ExploitMsg ExploitState ExploitError :=
    build_contract exploit_init exploit_receive.

End ExploitContract.

(* With this defined we can give the counterexample with relative ease. We use a
concrete implementation of a blockchain for this. *)
Section Theories.
  Import LocalBlockchain.

  Let AddrSize := (2^128)%N.
  Instance Base : ChainBase := LocalChainBase AddrSize.
  Instance Builder : ChainBuilderType := LocalChainBuilderImpl AddrSize true.

  Open Scope nat.
  Definition exploit_example : option (Address * Builder) :=
    let chain := builder_initial in
    let creator := BoundedN.of_Z_const AddrSize 10 in
    let add_block (chain : Builder) act_bodies :=
        let next_header :=
            {| block_height := S (chain_height chain);
               block_slot := S (current_slot chain);
               block_finalized_height := finalized_height chain;
               block_creator := creator;
               block_reward := 50; |} in
        let acts := map (build_act creator creator) act_bodies in
        option_of_result (builder_add_block chain next_header acts) in
    (* Get some money on the creator *)
    do chain <- add_block chain [];
    (* Deploy congress and exploit contracts *)
    let rules :=
        {| min_vote_count_permille := 200;
           margin_needed_permille := 501;
           debating_period_in_blocks := 0; |} in
    let dep_congress := create_deployment 50 contract {| setup_rules := rules |} in
    let dep_exploit := create_deployment 0 exploit_contract tt in
    do chain <- add_block chain [dep_congress; dep_exploit];
    let contracts := map fst (FMap.elements (lc_contracts (lcb_lc chain))) in
    let exploit := nth 0 contracts creator in
    let congress := nth 1 contracts creator in
    (* Add creator to congress, create a proposal to transfer *)
    (* some money to exploit contract, vote for the proposal, and execute the proposal *)
    let add_creator := add_member creator in
    let create_proposal := create_proposal [cact_transfer exploit 1] in
    let vote_proposal := vote_for_proposal 1 in
    let exec_proposal := finish_proposal 1 in
    let act_bodies :=
        map (fun m => act_call congress 0 (serialize m))
            [add_creator; create_proposal; vote_proposal; exec_proposal] in
    do chain <- add_block chain act_bodies;
    Some (congress, chain).

  Definition unpacked_exploit_example : Address * Builder :=
    unpack_option exploit_example.

  Definition num_acts_created_in_proposals (calls : list (ContractCallInfo Msg)) :=
    let count call :=
        match call_msg call with
        | Some (create_proposal acts) => length acts
        | _ => 0
        end in
    sumnat count calls.

  (* Now we prove that this version of the contract is buggy, i.e. it does not satisfy the
     property we proved for the other version of the Congress. We filter out transactions
     from the congress to the congress as we have those now (due to self calls). *)
  Theorem congress_buggy :
    exists bstate caddr (trace : ChainTrace empty_state bstate)
           (inc_calls : list (ContractCallInfo Msg)),
      env_contracts bstate caddr = Some (contract : WeakContract) /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      length (filter (fun tx => negb (tx_to tx =? caddr)%address)
                     (outgoing_txs trace caddr)) >
      num_acts_created_in_proposals inc_calls.
  Proof.
    exists (build_chain_state (snd unpacked_exploit_example) []).
    exists (fst unpacked_exploit_example).
    exists (builder_trace (snd unpacked_exploit_example)).
    set (inc_calls := unpack_option
                        (incoming_calls Msg
                                        (builder_trace (snd unpacked_exploit_example))
                                        (fst unpacked_exploit_example))).
    vm_compute in inc_calls.
    exists inc_calls.
    split; [|split].
    - reflexivity.
    - reflexivity.
    - vm_compute.
      clear inc_calls.
      lia.
  Qed.
End Theories.
