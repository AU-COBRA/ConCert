From SmartContracts Require Import Monads.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import LocalBlockchain.
From SmartContracts Require Import Congress.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Containers.
From SmartContracts Require Import BoundedN.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.

Section LocalBlockchainTests.
  (* Addresses *)
  Definition baker : Address :=
    BoundedN.of_Z_const AddrSize 10.

  Definition person_1 : Address :=
    BoundedN.of_Z_const AddrSize 11.

  Definition person_2 : Address :=
    BoundedN.of_Z_const AddrSize 12.

  Definition person_3 : Address :=
    BoundedN.of_Z_const AddrSize 13.

  Definition ChainBuilder := LocalChainBuilderDepthFirst.

  Definition chain1 : ChainBuilder := builder_initial.

  Definition unpack_option {A : Type} (a : option A) :=
    match a return match a with
                   | Some _ => A
                   | None => unit
                   end with
    | Some x => x
    | None => tt
    end.

  Compute (block_header chain1).

  (* Baker mines an empty block (and gets some coins) *)
  Definition chain2 : ChainBuilder :=
    unpack_option (chain1.(builder_add_block) baker [] 2 0).

  Compute (account_balance chain2 person_1).
  Compute (account_balance chain2 baker).

  (* Baker transfers 10 coins to person_1 *)
  Definition chain3 : ChainBuilder :=
    unpack_option (
        chain2.(builder_add_block)
                 baker
                 [build_act baker (act_transfer person_1 10)]
                 3 0).

  Compute (account_balance chain3 person_1).
  Compute (account_balance chain3 baker).

  (* person_1 deploys a Congress contract *)
  Definition setup_rules :=
    {| min_vote_count_permille := 200; (* 20% of congress needs to vote *)
       margin_needed_permille := 501;
       debating_period_in_blocks := 0; |}.

  Definition setup := Congress.build_setup setup_rules.

  Definition deploy_congress : ActionBody :=
    create_deployment 5 Congress.contract setup.

  Definition chain4 : ChainBuilder :=
    unpack_option (
        chain3.(builder_add_block)
                 baker
                 [build_act person_1 deploy_congress]
                 4 0).

  Definition congress_1 : Address :=
    match outgoing_txs (builder_trace chain4) person_1 with
    | tx :: _ => tx_to tx
    | _ => person_1
    end.

  Compute (account_balance chain4 person_1).
  Compute (account_balance chain4 baker).
  Compute (account_balance chain4 congress_1).

  Definition congress_ifc
    : ContractInterface Congress.Msg Congress.State :=
    match get_contract_interface
            chain4 congress_1
            Congress.Msg Congress.State with
    | Some x => x
    (* Using unpack_option here is extremely slow *)
    | None =>
      @build_contract_interface
        _ _ _
        baker
        (fun c => None)
        (fun a m => deploy_congress)
    end.

  Definition congress_state chain : Congress.State :=
    match congress_ifc.(get_state) chain with
    | Some s => s
    (* And also here *)
    | None => {| owner := baker;
                 state_rules := setup_rules;
                 proposals := FMap.empty;
                 next_proposal_id := 0;
                 members := FMap.empty |}
    end.

  Compute (congress_ifc.(get_state) chain4).
  Compute (FMap.elements (congress_state chain4).(members)).

  (* person_1 adds person_1 and person_2 as members of congress *)
  Definition add_person p :=
    congress_ifc.(send) 0 (Some (add_member p)).

  Definition chain5 : ChainBuilder :=
    unpack_option
      (chain4.(builder_add_block)
                baker
                [build_act person_1 (add_person person_1); build_act person_1 (add_person person_2)]
                5 0).

  Compute (FMap.elements (congress_state chain5).(members)).
  Compute (account_balance chain5 congress_1).

  (* person_1 creates a proposal to send 3 coins to person_3 using funds
     of the contract *)
  Definition create_proposal_call :=
    congress_ifc.(send) 0 (Some (create_proposal [cact_transfer person_3 3])).

  Definition chain6 : ChainBuilder :=
    unpack_option (
        chain5.(builder_add_block)
                 baker
                 [build_act person_1 create_proposal_call]
                 6 0).

  Compute (FMap.elements (congress_state chain6).(proposals)).

  (* person_1 and person_2 vote for the proposal *)
  Definition vote_proposal :=
    congress_ifc.(send) 0 (Some (vote_for_proposal 1)).

  Definition chain7 : ChainBuilder :=
    unpack_option (
        chain6.(builder_add_block)
                 baker
                 [build_act person_1 vote_proposal; build_act person_2 vote_proposal]
                 7 0).

  Compute (FMap.elements (congress_state chain7).(proposals)).

  (* Person 3 finishes the proposal (anyone can finish it after voting) *)
  Definition finish_proposal :=
    congress_ifc.(send) 0 (Some (finish_proposal 1)).

  Definition chain8 : ChainBuilder :=
    unpack_option (
        chain7.(builder_add_block)
                 baker
                 [build_act person_3 finish_proposal]
                 8 0).

  Compute (FMap.elements (congress_state chain8).(proposals)).
  (* Balances before: *)
  Compute (account_balance chain7 congress_1).
  Compute (account_balance chain7 person_3).
  (* Balances after: *)
  Compute (account_balance chain8 congress_1).
  Compute (account_balance chain8 person_3).
  Print Assumptions chain8.
End LocalBlockchainTests.

Hint Resolve congress_txs_after_block : core.
(* The congress satisfies a property specialized to the local blockchain DFS: *)
Lemma congress_txs_after_local_chain_block
          (prev new : LocalChainBuilderDepthFirst) baker acts slot finalization_height :
  builder_add_block prev baker acts slot finalization_height = Some new ->
  forall addr,
    env_contracts new addr = Some (Congress.contract : WeakContract) ->
    length (outgoing_txs (builder_trace new) addr) <=
    num_acts_created_in_proposals (incoming_txs (builder_trace new) addr).
Proof. eauto. Qed.
(* And of course, it is satisfied for the breadth first chain as well. *)
Lemma congress_txs_after_local_chain_bf_block
      (prev new : LocalChainBuilderBreadthFirst) baker acts slot finalization_height :
  builder_add_block prev baker acts slot finalization_height = Some new ->
  forall addr,
    env_contracts new addr = Some (Congress.contract : WeakContract) ->
    length (outgoing_txs (builder_trace new) addr) <=
    num_acts_created_in_proposals (incoming_txs (builder_trace new) addr).
Proof. eauto. Qed.
