Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
(* From ConCert Require Import LocalBlockchainTests. *)
From ConCert Require Import Containers.
From ConCert Require Import Congress_Buggy.
Require Import Extras.

From ConCert.Execution.QCTests Require Import 
ChainGens TestUtils ChainPrinters Congress_BuggyGens Congress_BuggyPrinters SerializablePrinters TraceGens.
Close Scope monad_scope.

From ConCert Require Import Monads.

(* From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope. *)
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List Int BinInt FunInd.

Import BoundedN.Stdpp.
Import LocalBlockchain.
Import ListNotations.

Close Scope address_scope.

(* -------------------------- Tests of the Buggy Congress Implementation -------------------------- *)
Definition AddrSize := (2^8)%N.
(* Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase. *)
Instance Base : ChainBase := LocalChainBase AddrSize.
Instance Builder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.

Let creator := BoundedN.of_Z_const AddrSize 10.

Open Scope nat.
Definition exploit_example : option (Address * Builder) :=
  let chain := builder_initial in
  let add_block (chain : Builder) act_bodies :=
      let next_header :=
          {| block_height := S (chain_height chain);
             block_slot := S (current_slot chain);
             block_finalized_height := finalized_height chain;
             block_creator := creator;
             block_reward := 50; |} in
      let acts := map (build_act creator) act_bodies in
      builder_add_block chain next_header acts in
  (* Get some money on the creator *)
  (* Deploy congress and exploit contracts *)
  do chain <- add_block chain [];
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
      map (fun m => act_call congress 0 (serialize _ _ m))
          [add_creator] in
  do chain <- add_block chain act_bodies;
  Some (congress, chain).
  
Definition unpacked_exploit_example : Address * Builder :=
  unpack_option exploit_example.

Definition total_outgoing_acts_of_trace (trace : LocalChainTraceList) := 
  let acts_per_step := map (length o acts_of_lcstep) trace in
  fold_left Nat.add acts_per_step 0.

Definition num_acts_created_in_proposals (calls : list (ContractCallInfo Msg)) :=
  let count call :=
      match call_msg call with
      | Some (create_proposal acts) => length acts
      | _ => 0
      end in
  sumnat count calls.

Local Open Scope monad_scope.
Definition gBuggyCongressChainTraceList lc length := gLocalChainTraceList_fix lc gCongressActionBuggy length 1.
Sample (gCongressActionBuggy (lcb_lc (snd unpacked_exploit_example)) 1).
Sample (gBuggyCongressChainTraceList (lcb_lc (snd unpacked_exploit_example)) 3).

Local Open Scope Z_scope.
Local Open Scope string_scope.
Definition exploit_contract_balance_le_1 (chain : @LocalChain AddrSize) := 
  let contracts := map fst (FMap.elements (lc_contracts chain)) in
  let exploit_caddr : Address := nth 0 contracts creator in
  let congress_caddr : Address := nth 1 contracts creator in
  match FMap.find exploit_caddr chain.(lc_account_balances) with
  | Some balance => 
    whenFail (nl ++ "balance:" ++ show balance)
    (balance <=? 1)
  | None => 
    whenFail ("couldn't find exploit for some reason...")
    false
  end.

Definition congress_no_reentry_on_finish_proposal := 
  let chain := (lcb_lc (snd unpacked_exploit_example)) in
  forAllTraces 3 chain gBuggyCongressChainTraceList 
    exploit_contract_balance_le_1.
Open Scope nat_scope.

Definition congress_has_proposals := 
  let chain := (lcb_lc (snd unpacked_exploit_example)) in
  let contracts := map fst (FMap.elements (lc_contracts chain)) in
  let exploit_caddr : Address := nth 0 contracts creator in
  let congress_caddr : Address := nth 1 contracts creator in
  match FMap.find congress_caddr (Congress_BuggyGens.lc_proposals' chain) with
  | Some proposals => 
    whenFail ("proposals: " ++ show proposals)
    (0 <? (FMap.size proposals)) 
  | None => checker false
  end.

Definition can_apply_finish_proposal_action := 
  let chain := (lcb_lc (snd unpacked_exploit_example)) in
  let contracts := map fst (FMap.elements (lc_contracts chain)) in
  let exploit_caddr : Address := nth 0 contracts creator in
  let congress_caddr : Address := nth 1 contracts creator in
  forAll (gCongressActionBuggy (lcb_lc (snd unpacked_exploit_example)) 1)
    (fun act =>
      isSomeCheck act (fun act => 
        whenFail ("act: " ++ show act)
        ((isSome) (mk_basic_step_action chain [act])))
    ).


Definition can_apply_finish_proposal_action_1 := 
  let chain := (lcb_lc (snd unpacked_exploit_example)) in
  let contracts := map fst (FMap.elements (lc_contracts chain)) in
  let exploit_caddr : Address := nth 0 contracts creator in
  let congress_caddr : Address := nth 1 contracts creator in
  forAll (gBuggyCongressChainTraceList chain 3)
    (fun trace => 0 <? length trace
      (* isSomeCheck acts_of_ (fun act =>
        isSome (my_add_block chain [act]) *)
      
    ).

(* QuickChick can_apply_finish_proposal_action.
QuickChick can_apply_finish_proposal_action_1.
QuickChick congress_has_proposals. *)
QuickCheck congress_no_reentry_on_finish_proposal.




