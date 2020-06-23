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
Require Import ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import TestUtils ChainPrinters Congress_BuggyGens Congress_BuggyPrinters SerializablePrinters TraceGens.
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
Instance Base : ChainBase := LocalChainBase AddrSize.
Instance Builder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.

Let creator := BoundedN.of_Z_const AddrSize 10.

Definition rules := {| 
  min_vote_count_permille := 200;
  margin_needed_permille := 501;
  debating_period_in_blocks := 0;
|}.

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
      option_of_result (builder_add_block chain next_header acts) in
  (* Get some money on the creator *)
  (* Deploy congress and exploit contracts *)
  do chain <- add_block chain [];
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

Definition gCongressChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun lc _ => 
  gCongressActionBuggy lc 2) length max_acts_per_block.

Definition forAllCongressTraces n := 
  forAllTraces n (lcb_lc (snd unpacked_exploit_example)) (gCongressChainTraceList 1).
Notation "{{ P }} c {{ Q }}" := 
  (pre_post_assertion 2 (lcb_lc (snd unpacked_exploit_example)) (gCongressChainTraceList 1) c P Q)( at level 50).
Local Close Scope Z_scope.

Definition num_cacts_in_state state :=
  sumnat (fun '(k, v) => length (actions v)) (FMap.elements (proposals state)).

Definition num_cacts_safe_P (msg : Congress_Buggy.Msg) 
                            (resp_acts : list ActionBody)
                            (old_state : Congress_Buggy.State) 
                            (new_state : Congress_Buggy.State) :=
  let nr_cacts := match msg with
                  | create_proposal ls => length ls
                  | _ => 0
                  end in 
  num_cacts_in_state new_state + length resp_acts <=?
  num_cacts_in_state old_state + nr_cacts.

Definition receive_state_well_behaved_P (cctx : ContractCallContext) 
                                        (old_state : Congress_Buggy.State) 
                                        (msg : Congress_Buggy.Msg) 
                                        (result : option (Congress_Buggy.State * list ActionBody)) := 
  match result with
  | Some (new_state, resp_acts) =>
    checker (num_cacts_safe_P msg resp_acts old_state new_state) 
  | _ => checker false
  end.

(* QuickChick (
  {{fun _ _ => true}}
  Congress_Buggy.contract
  {{receive_state_well_behaved_P}}
). *)

(* coqtop-stdout:
Begin Trace: 
step_action{
  Action{
    act_from: 10%256, 
    act_body: (act_call 128%256, 0, create_proposal (transfer: 10%256, 1))}};;
step_action{
  Action{act_from: 10%256, 
  act_body: (act_call 128%256, 0, finish_proposal 1)}}
End Trace

*** Failed after 2 tests and 0 shrinks. (0 discards) *)