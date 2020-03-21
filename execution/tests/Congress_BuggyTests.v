Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith.
From QuickChick Require Import QuickChick. Import QcNotation.
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
  (* Add creator to congress *)
  let add_creator := add_member creator in
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
(* The '1' means we only allow nested proposal actions of level one (in particular, this generator
   never generates proposals containing proposals). *)
Definition gBuggyCongressChainTraceList lc length := gLocalChainTraceList_fix lc gCongressActionBuggy length 1.
(* Sample (gCongressActionBuggy (lcb_lc (snd unpacked_exploit_example)) 1). *)
(* Sample (gBuggyCongressChainTraceList (lcb_lc (snd unpacked_exploit_example)) 3). *)

Local Open Scope Z_scope.
Local Open Scope string_scope.
(* Asserts that the balance of the exploit contract is <= 1 *)
(* Note: whenever gCongressActionBuggy generates proposals to transfer, we have fixed the transfer amount to 1 to make it more easy to test.
   It would be perfectly possible to generalize this, but then we would have to do a lot of filtering of the trace. *)
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

(* Counts the number of potential transfers (ie. including proposals of transfers) to the given address *)
Definition nr_potential_transfers_to_exploit_contract (trace : LocalChainTraceList) exploit_caddr := 
  let all_acts : list Action := fold_left (fun acc s => List.app (acts_of_lcstep s) acc) trace [] in
  let is_potential_transfer_to_exploit act := match act.(act_body) with
      | act_call _ _ ser_msg => match deserialize Congress_Buggy.Msg _ ser_msg with
                                         | Some (create_proposal [cact_transfer to _]) =>
                                           address_eqb to exploit_caddr 
                                         | _ => false
                                         end
      | act_transfer addr _ => address_eqb addr exploit_caddr
      | _ => false
      end in
  fold_left (fun acc act => if is_potential_transfer_to_exploit act then 1 + acc else acc) all_acts 0.

Local Open Scope Z_scope.

(* A specialisation of the reentry problem; if a trace has one potential transfer (with amount=1) to the exploit contract,
   then the balance of the exploit contract after this trace has been executed must be <= 1 *)
Definition congress_no_reentry_on_finish_proposal := 
  let chain := (lcb_lc (snd unpacked_exploit_example)) in
  let contracts := map fst (FMap.elements (lc_contracts chain)) in
  let exploit_caddr : Address := nth 0 contracts creator in
  forAllTraces_traceProp 3 chain gBuggyCongressChainTraceList 
    (fun trace => 
      let last_chain := List.last (map next_lc_of_lcstep trace) chain in
      ((nr_potential_transfers_to_exploit_contract trace exploit_caddr) =? 1%Z) 
      ==> exploit_contract_balance_le_1 last_chain).

(* QuickCheck (expectFailure congress_no_reentry_on_finish_proposal). *)
(* 
coqtop-stdout:
Begin Trace: 
step_action{[Action{act_from: 10%256, act_body: (act_call 128%256, 0, create_proposal (transfer: 129%256, 1))}]};;
step_action{[Action{act_from: 10%256, act_body: (act_call 128%256, 0, vote_for_proposal 1)}]};;
step_action{[Action{act_from: 10%256, act_body: (act_call 128%256, 0, finish_proposal 1)}]}
End Trace
balance:27
+++ Failed (as expected) after 18 tests and 0 shrinks. (43 discards)
*)



