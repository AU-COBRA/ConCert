(* This file computes with the Congress and an actual blockchain
implementation, showing that everything computes from within Coq. It
also contains specializations of the results proven in Congress.v to
our particular implementations of blockchains. *)

Require Import Monads.
Require Import Blockchain.
Require Import LocalBlockchain.
Require Import Congress.
Require Import Containers.
Require Import BoundedN.
Require Import Extras.
Require Import Serializable.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.

Section LocalBlockchainTests.
  Let AddrSize := (2^128)%N.
  Instance Base : ChainBase := LocalChainBase AddrSize.
  Instance ChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.

  (* Addresses *)
  Definition creator : Address :=
    BoundedN.of_Z_const AddrSize 10.

  Definition person_1 : Address :=
    BoundedN.of_Z_const AddrSize 11.

  Definition person_2 : Address :=
    BoundedN.of_Z_const AddrSize 12.

  Definition person_3 : Address :=
    BoundedN.of_Z_const AddrSize 13.

  Definition chain1 : ChainBuilder := builder_initial.

  Definition add_block (chain : ChainBuilder) acts : option ChainBuilder :=
    let header :=
        {| block_height := S (chain_height chain);
           block_slot := S (current_slot chain);
           block_finalized_height := finalized_height chain;
           block_creator := creator;
           block_reward := 50; |} in
    builder_add_block chain header acts.

  (* Creator created an empty block (and gets some coins) *)
  Definition chain2 : ChainBuilder :=
    unpack_option (add_block chain1 []).

  Compute (account_balance chain2 person_1).
  Compute (account_balance chain2 creator).

  (* Creator transfers 10 coins to person_1 *)
  Definition chain3 : ChainBuilder :=
    unpack_option (add_block chain2 [build_act creator (act_transfer person_1 10)]).

  Compute (account_balance chain3 person_1).
  Compute (account_balance chain3 creator).

  (* person_1 deploys a Congress contract *)
  Definition setup_rules :=
    {| min_vote_count_permille := 200; (* 20% of congress needs to vote *)
       margin_needed_permille := 501;
       debating_period_in_blocks := 0; |}.

  Definition setup := Congress.build_setup setup_rules.

  Definition deploy_congress : ActionBody :=
    create_deployment 5 Congress.contract setup.

  Definition chain4 : ChainBuilder :=
    unpack_option (add_block chain3 [build_act person_1 deploy_congress]).

  Definition congress_1 : Address :=
    match outgoing_txs (builder_trace chain4) person_1 with
    | tx :: _ => tx_to tx
    | _ => person_1
    end.

  Compute (account_balance chain4 person_1).
  Compute (account_balance chain4 creator).
  Compute (account_balance chain4 congress_1).

  Definition congress_ifc : ContractInterface Congress.Msg :=
    match get_contract_interface chain4 congress_1 Congress.Msg with
    | Some x => x
    (* Using unpack_option here is extremely slow *)
    | None =>
      @build_contract_interface
        _ _
        creator
        (fun a m => deploy_congress)
    end.

  Definition congress_state lc : Congress.State :=
    match env_contract_states lc congress_1 >>= deserialize with
    | Some s => s
    (* And also here *)
    | None => {| owner := creator;
                 state_rules := setup_rules;
                 proposals := FMap.empty;
                 next_proposal_id := 0;
                 members := FMap.empty |}
    end.

  Compute (congress_state chain4).
  Compute (FMap.elements (congress_state chain4).(members)).

  (* person_1 adds person_1 and person_2 as members of congress *)
  Definition add_person p :=
    congress_ifc.(send) 0 (Some (add_member p)).

  Definition chain5 : ChainBuilder :=
    let acts := [build_act person_1 (add_person person_1);
                 build_act person_1 (add_person person_2)] in
    unpack_option (add_block chain4 acts).

  Compute (FMap.elements (congress_state chain5).(members)).
  Compute (account_balance chain5 congress_1).

  (* person_1 creates a proposal to send 3 coins to person_3 using funds
     of the contract *)
  Definition create_proposal_call :=
    congress_ifc.(send) 0 (Some (create_proposal [cact_transfer person_3 3])).

  Definition chain6 : ChainBuilder :=
    unpack_option (add_block chain5 [build_act person_1 create_proposal_call]).

  Compute (FMap.elements (congress_state chain6).(proposals)).

  (* person_1 and person_2 vote for the proposal *)
  Definition vote_proposal :=
    congress_ifc.(send) 0 (Some (vote_for_proposal 1)).

  Definition chain7 : ChainBuilder :=
    let acts := [build_act person_1 vote_proposal; build_act person_2 vote_proposal] in
    unpack_option (add_block chain6 acts).

  Compute (FMap.elements (congress_state chain7).(proposals)).

  (* Person 3 finishes the proposal (anyone can finish it after voting) *)
  Definition finish_proposal :=
    congress_ifc.(send) 0 (Some (finish_proposal 1)).

  Definition chain8 : ChainBuilder :=
    unpack_option (add_block chain7 [build_act person_3 finish_proposal]).

  Compute (FMap.elements (congress_state chain8).(proposals)).
  (* Balances before: *)
  Compute (account_balance chain7 congress_1).
  Compute (account_balance chain7 person_3).
  (* Balances after: *)
  Compute (account_balance chain8 congress_1).
  Compute (account_balance chain8 person_3).
  Print Assumptions chain8.

  Hint Resolve congress_txs_after_block : core.
  Definition BuilderDF := LocalChainBuilderDepthFirst AddrSize.
  (* The congress satisfies a property specialized to the local blockchain DFS: *)
  Lemma congress_txs_after_local_chain_block
        (prev new : BuilderDF) header acts :
    builder_add_block prev header acts = Some new ->
    forall caddr,
      env_contracts new caddr = Some (Congress.contract : WeakContract) ->
      exists inc_calls,
        incoming_calls Congress.Msg (builder_trace new) caddr = Some inc_calls /\
        length (outgoing_txs (builder_trace new) caddr) <=
        num_acts_created_in_proposals inc_calls.
  Proof. eauto. Qed.
  (* And of course, it is satisfied for the breadth first chain as well. *)
  Definition BuilderBF := LocalChainBuilderBreadthFirst AddrSize.
  Lemma congress_txs_after_local_chain_bf_block
        (prev new : BuilderBF) header acts :
    builder_add_block prev header acts = Some new ->
    forall caddr,
      env_contracts new caddr = Some (Congress.contract : WeakContract) ->
      exists inc_calls,
        incoming_calls Congress.Msg (builder_trace new) caddr = Some inc_calls /\
        length (outgoing_txs (builder_trace new) caddr) <=
        num_acts_created_in_proposals inc_calls.
  Proof. eauto. Qed.
End LocalBlockchainTests.
