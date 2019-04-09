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
  Definition congress_1 := 1.
  Definition baker := 10.
  Definition person_1 := 11.
  Definition person_2 := 12.
  Definition person_3 := 13.

  Definition chain1 :=
    initial_chain_builder LocalBlockchain.lc_builder_interface.

  Definition unpack_option {A : Type} (a : option A) :=
    match a return match a with
                   | Some _ => A
                   | None => unit
                   end with
    | Some x => x
    | None => tt
    end.

  (* Baker mines an empty block (and gets some coins) *)
  Definition chain2 : ChainBuilder :=
    unpack_option (chain1.(add_block) baker []).

  Compute (account_balance chain2 person_1).
  Compute (account_balance chain2 baker).

  (* Baker transfers 10 coins to person_1 *)
  Definition chain3 : ChainBuilder :=
    unpack_option (chain2.(add_block) baker [(baker, act_transfer person_1 10)]).

  Compute (account_balance chain3 person_1).
  Compute (account_balance chain3 baker).

  (* person_1 deploys a Congress contract *)
  Definition setup_rules :=
    {| min_vote_count_permille := 200; (* 20% of congress needs to vote *)
       margin_needed_permille := 501;
       debating_period_in_blocks := 0; |}.

  Definition setup := Congress.build_setup setup_rules.

  Definition deploy_congress : ChainAction :=
    create_deployment 5 Congress.contract setup.

  Definition chain4 : ChainBuilder :=
    unpack_option (chain3.(add_block) baker [(person_1, deploy_congress)]).

  Compute (contract_deployment chain4 congress_1).
  Compute (account_balance chain4 person_1).
  Compute (account_balance chain4 baker).
  Compute (account_balance chain4 congress_1).

  Definition congress_ifc :=
    unpack_option
      (get_contract_interface chain4 congress_1 Congress.Setup Congress.Msg Congress.State).

  Definition congress_state chain : Congress.State :=
    match congress_ifc.(get_state) chain with
    | Some s => s
    | None => {| owner := 0;
                 state_rules := setup_rules;
                 proposals := FMap.empty;
                 next_proposal_id := 0;
                 members := FMap.empty |}
    end.

  Compute (congress_ifc.(get_state) chain4).
  Compute (FMap.elements (congress_state chain4).(members)).

  (* person_1 adds person_1 and person_2 as members of congress *)
  Definition add_person p :=
    congress_ifc.(call) 0 (add_member p).

  Definition chain5 : ChainBuilder :=
    unpack_option
      (chain4.(add_block)
                baker
                [(person_1, add_person person_1); (person_1, add_person person_2)]).

  Compute (FMap.elements (congress_state chain5).(members)).
  Compute (account_balance chain5 congress_1).

  (* person_1 creates a proposal to send 3 coins to person_3 using funds
     of the contract *)
  Definition create_proposal_call :=
    congress_ifc.(call) 0 (create_proposal [cact_transfer person_3 3]).

  Definition chain6 : ChainBuilder :=
    unpack_option (chain5.(add_block) baker [(person_1, create_proposal_call)]).

  Compute (FMap.elements (congress_state chain6).(proposals)).

  (* person_1 and person_2 vote for the proposal *)
  Definition vote_proposal :=
    congress_ifc.(call) 0 (vote_for_proposal 1).

  Definition chain7 : ChainBuilder :=
    unpack_option
      (chain6.(add_block) baker [(person_1, vote_proposal); (person_2, vote_proposal)]).

  Compute (FMap.elements (congress_state chain7).(proposals)).

  (* Person 3 finishes the proposal (anyone can finish it after voting) *)
  Definition finish_proposal :=
    congress_ifc.(call) 0 (finish_proposal 1).

  Definition chain8 : ChainBuilder :=
    unpack_option (chain7.(add_block) baker [(person_3, finish_proposal)]).

  Compute (FMap.elements (congress_state chain8).(proposals)).
  (* Balances before: *)
  Compute (account_balance chain7 congress_1).
  Compute (account_balance chain7 person_3).
  (* Balances after: *)
  Compute (account_balance chain8 congress_1).
  Compute (account_balance chain8 person_3).
  Print Assumptions chain8.
End LocalBlockchainTests.
