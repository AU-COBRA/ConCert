From SmartContracts Require Import Monads.
From SmartContracts Require Import Blockchain.
From SmartContracts Require LocalBlockchain.
From SmartContracts Require Import Congress.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Containers.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.

Section LocalBlockchainTests.
  (* Addresses *)
  Let congress_1 := 1.
  Let baker := 10.
  Let person_1 := 11.
  Let person_2 := 12.
  Let person_3 := 13.

  Let chain1 :=
    initial_chain_builder LocalBlockchain.lc_builder_interface.

  Let otry x :=
    match x with
    | Some y => y
    | None => chain1
    end.

  (* Baker mines an empty block (and gets some coins) *)
  Let chain2 :=
    otry (chain1.(add_block) baker []).

  Compute (account_balance chain2 person_1).
  Compute (account_balance chain2 baker).

  (* Baker transfers 10 coins to person_1 *)
  Let chain3 :=
    otry (chain2.(add_block) baker [(baker, act_transfer person_1 10)]).

  Compute (account_balance chain3 person_1).
  Compute (account_balance chain3 baker).

  (* person_1 deploys a Congress contract *)
  Let setup_rules :=
    {| min_vote_count_permille := 200; (* 20% of congress needs to vote *)
       margin_needed_permille := 501;
       debating_period_in_blocks := 0; |}.

  Let setup := Congress.build_setup setup_rules.

  Let deploy_congress : ChainAction :=
    create_deployment 5 Congress.contract setup.

  Let chain4 :=
    otry (chain3.(add_block) baker [(person_1, deploy_congress)]).

  Compute (contract_deployment chain4 congress_1).
  Compute (account_balance chain4 person_1).
  Compute (account_balance chain4 baker).
  Compute (account_balance chain4 congress_1).

  Let congress_ifc :=
    match get_contract_interface
            chain4 congress_1
            Congress.Setup Congress.Msg Congress.State with
    | Some x => x
    (* This stuff is just to make the test example easier
       since we know it will not fail *)
    | None =>
      build_contract_interface
        0
        0
        setup
        (fun c => None)
        (fun a => deploy_congress)
        (fun a m => deploy_congress)
    end.

  Let congress_state chain : Congress.State :=
    match congress_ifc.(get_state) chain with
    | Some s => s
    | None => {| owner := 0;
                 state_rules := setup_rules;
                 proposals := FMap.empty;
                 next_proposal_id := 0;
                 members := FSet.empty |}
    end.

  Compute (congress_ifc.(get_state) chain4).
  Compute (FSet.elements (congress_state chain4).(members)).

  (* person_1 adds person_1 and person_2 as members of congress *)
  Let add_person p :=
    congress_ifc.(call) 0 (add_member p).

  Let chain5 := otry (chain4.(add_block) baker [(person_1, add_person person_1);
                                                (person_1, add_person person_2)]).

  Compute (FSet.elements (congress_state chain5).(members)).
  Compute (account_balance chain5 congress_1).

  (* person_1 creates a proposal to send 3 coins to person_3 using funds
     of the contract *)
  Let create_proposal_call :=
    congress_ifc.(call) 0 (create_proposal [cact_transfer person_3 3]).

  Let chain6 := otry (chain5.(add_block) baker [(person_1, create_proposal_call)]).
  Compute (FMap.elements (congress_state chain6).(proposals)).

  (* person_1 and person_2 vote for the proposal *)
  Let vote_proposal  :=
    congress_ifc.(call) 0 (vote_for_proposal 1).

  Let chain7 := otry (chain6.(add_block) baker [(person_1, vote_proposal);
                                                (person_2, vote_proposal)]).
  Compute (FMap.elements (congress_state chain7).(proposals)).

  (* Person 3 finishes the proposal (anyone can finish it after voting) *)
  Let finish_proposal :=
    congress_ifc.(call) 0 (finish_proposal 1).

  Let chain8 := otry (chain7.(add_block) baker [(person_3, finish_proposal)]).
  Compute (FMap.elements (congress_state chain8).(proposals)).
  (* Balances before: *)
  Compute (account_balance chain7 congress_1).
  Compute (account_balance chain7 person_3).
  (* Balances after: *)
  Compute (account_balance chain8 congress_1).
  Compute (account_balance chain8 person_3).
  Print Assumptions chain8.
End LocalBlockchainTests.
