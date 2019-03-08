From SmartContracts Require Import Monads.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import LocalBlockchain.
From SmartContracts Require Import Congress.
From SmartContracts Require Import Oak.
From Containers Require Import SetInterface MapInterface OrderedTypeEx.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.

Section LocalBlockchainTests.
  (* Addresses *)
  Let congress_1 := 1.
  Let congress_2 := 2.
  Let baker := 10.
  Let person_1 := 11.
  Let person_2 := 12.
  Let person_3 := 13.

  Let otry x :=
    match x with
    | Some y => y
    | None => LocalBlockchain.initial_chain
    end.
  Let lce_to_chain l := build_chain lc_interface l.(lce_lc) .
  Local Coercion lce_to_chain : LocalChainEnvironment >-> Chain.

  Let chain1 := LocalBlockchain.initial_chain.
  (* Baker mines an empty block *)
  Let chain2 := otry (LocalBlockchain.add_block baker [] chain1).
  Compute (account_balance chain2 person_1).
  Compute (account_balance chain2 baker).

  (* Baker transfers 10 coins to person_1 *)
  Let chain3 := otry (LocalBlockchain.add_block baker [(baker, act_transfer person_1 10)] chain2).
  Compute (account_balance chain3 person_1).
  Compute (account_balance chain3 baker).

  Let setup_rules :=
    {| min_vote_count_permille := 200; (* 20% of congress needs to vote *)
       margin_needed_permille := 500;
       debating_period_in_blocks := 0; |}.

  Let deploy_congress : ChainAction :=
    act_deploy 5 Congress.contract (serialize setup_rules).

  Let chain4 := otry (LocalBlockchain.add_block baker [(person_1, deploy_congress)] chain3).
  Compute (account_balance chain4 person_1).
  Compute (account_balance chain4 baker).
  Compute (account_balance chain4 congress_1).

  (* person_1 adds person_1 and person_2 as members of congress *)
  Let add_person p :=
    act_call congress_1 0 (serialize (add_member p)).

  Let chain5 := otry (LocalBlockchain.add_block baker [(person_1, add_person person_1) ;
                                                       (person_1, add_person person_2)] chain4).
  Compute (account_balance chain5 person_1).
  Compute (chain5.(lce_lc).(lc_updates)).

  Let congress_state chain  : option Congress.State :=
    deserialize =<< (contract_state chain congress_1).

  Compute (match congress_state chain5 with
           | Some x => SetInterface.elements x.(members)
           | None => []
          end).
  Compute (account_balance chain5 congress_1).

  (* person_1 creates a proposal to send 3 coins to person_3 using funds
     of the contract *)
  Let create_proposal_msg :=
    serialize (create_proposal [cact_transfer person_3 3]).

  Let create_proposal_call :=
    act_call congress_1 0 create_proposal_msg.

  Let chain6 := otry (LocalBlockchain.add_block baker [(person_1, create_proposal_call)] chain5).
  Compute (match congress_state chain6 with
           | Some x => MapInterface.elements x.(proposals)
           | None => []
           end).

  (* person_1 and person_2 votes for the proposal *)
  Let vote_proposal :=
      act_call congress_1 0 (serialize (vote_for_proposal 1)).

  Let chain7 := otry (LocalBlockchain.add_block baker [(person_1, vote_proposal);
                                                       (person_2, vote_proposal)] chain6).
  Compute (match congress_state chain7 with
           | Some x => MapInterface.elements x.(proposals)
           | None => []
           end).

  (* Finish the proposal *)
  Let finish_proposal :=
    act_call congress_1 0 (serialize (finish_proposal 1)).

  Let chain8 := otry (LocalBlockchain.add_block baker [(person_1, finish_proposal)] chain7).

  (* Balance before: *)
  Compute (account_balance chain7 person_3).
  (* Balance after: *)
  Compute (account_balance chain8 person_3).
End LocalBlockchainTests.
