From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import BoundedN ChainedList.
Require Import Extras.

From ConCert.Execution.QCTests Require Import 
  ChainGens TestUtils ChainPrinters CongressGens CongressPrinters SerializablePrinters TraceGens.

Require Import ZArith Strings.Ascii Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Require Import Containers.

Notation "f 'o' g" := (compose f g) (at level 50).

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

Definition chain_with_congress_deployed : LocalChain := lcb_lc chain6. (* chain6 is from LocalBlockchainTests.v *)
Definition congress_chain := chain_with_congress_deployed.
Definition congress_contract_base_addr := BoundedN.of_Z_const AddrSize 128%Z.

Extract Constant defNumDiscards => "(4 * defNumTests)".

Definition gCongressChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun lc _ => 
    gCongressActionNew lc 2) length max_acts_per_block.

Definition forAllCongressTraces n := 
  forAllTraces n congress_chain (gCongressChainTraceList 1).
Notation "{{ P }} c {{ Q }}" := 
  (pre_post_assertion 10 congress_chain (gCongressChainTraceList 1) c P Q)( at level 50).

Open Scope string_scope.
Definition debug_congress {A : Type} 
                         `{Checkable A} 
                          (lc : LocalChain) 
                          (acts_opt : option (list Action)) 
                          : A -> Checker := 
  whenFail (
    "LocalChain: " ++ show lc ++ nl ++
    "members: " ++ show (congressContractsMembers lc) ++ nl ++
    "active proposals: " ++ show (lc_proposals lc) ++ nl ++
    "contract owners: " ++ show (lc_contract_owners lc)
  ).
Close Scope string_scope.

Definition nr_cacts (msg : option Congress.Msg) := 
  match msg with
  | Some (create_proposal ls) => length ls
  | _ => 0
  end.

(* What this says is that the number of actions to be performed by the congress never increases 
   more than the actions that are added in proposals, ie. actions can't appear out of nowhere. *)
(* If we replace '<=' with '<' QC finds a counterexample - a proposal can contain an empty list of actions, so they are equal before/after add_proposal *)
Definition receive_state_well_behaved state msg new_state (resp_acts : list ActionBody) :=
  num_cacts_in_state new_state + length resp_acts <=
  num_cacts_in_state state + nr_cacts msg.


Instance receive_state_well_behaved_dec_ {state : Congress.State} 
                                        {msg : option Congress.Msg} 
                                        {new_state : Congress.State}
                                        {resp_acts : list ActionBody} 
                                        : Dec (receive_state_well_behaved state msg new_state resp_acts).
Proof.
  intros. 
  unfold receive_state_well_behaved. 
  constructor. 
  apply le_dec.
Qed.

(* Instance receive_state_well_behaved_checkable {state : Congress.State} 
                                              {msg : option Congress.Msg} 
                                              {new_state : Congress.State}
                                              {resp_acts : list ActionBody} 
                                              : Checkable (receive_state_well_behaved_inner state msg new_state resp_acts). 
Proof. apply testDec. Qed. *)



Definition receive_state_well_behaved_P (cctx : ContractCallContext) 
                                        (old_state : Congress.State) 
                                        (msg : Congress.Msg) 
                                        (result : option (Congress.State * list ActionBody)) := 
  match result with
  | Some (new_state, resp_acts) =>
    (receive_state_well_behaved old_state (Some msg) new_state resp_acts)?
    (* checker (num_cacts_safe_P msg resp_acts old_state new_state)  *)
  | _ => false
  end.

QuickChick (
  {{fun _ _ => true}}
  Congress.contract
  {{receive_state_well_behaved_P}}
).

(* in 39 seconds: *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)


(* A property about the way States are generated. *)
(* It says that a State generated at some time slot cannot contain proposals later than this time slot. *)
Definition state_proposals_proposed_in_valid_P (block_slot : nat) (state : Congress.State) := 
  let proposals := map snd (FMap.elements (proposals state)) in
  forallb (fun p => proposed_in p <=? block_slot) proposals.

Definition state_proposals_proposed_in_valid lc := 
  let congress_state_map := lc_contract_state_deserialized Congress.State lc in
  checker match FMap.find congress_contract_base_addr congress_state_map with
  | Some congress_state => 
    state_proposals_proposed_in_valid_P lc.(lc_slot) congress_state
  | None => false
  end.

(* QuickChick (forAllCongressTraces 10 state_proposals_proposed_in_valid). *)

(* in 37 seconds *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)


(* sanity check *)
Definition add_block_actions_succeeds_P c_opt actions_opt :=
  isSomeCheck c_opt
  (fun c => 
    (debug_congress c actions_opt) 
      (match actions_opt with
      | Some actions => (0 <? length actions) && isSome (my_add_block c actions)
      | None => false
      end)
  ).

Instance shrinkAction : Shrink Action := {| shrink a := [a] |}.

(* another sanity check *)
Definition check_add_two_blocks_succeeds := 
  (forAll3 
    (optToVector 1 (gCongressActionNew chain_with_congress_deployed 2))
    (fun actions => returnGen (my_add_block chain_with_congress_deployed actions))
    (fun _ c_opt => 
      bindGenOpt (returnGen c_opt) 
      (fun c =>
        acts <- (optToVector 1 (gCongressActionNew c 2)) ;; 
        returnGen (Some acts)))
    (fun _ c_opt actions_opt => add_block_actions_succeeds_P c_opt actions_opt)
  ).

(* QuickChick check_add_two_blocks_succeeds. *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)


Definition reachableFrom_congress (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc (fun lc _ => gCongressChainTraceList 1 lc 2) pf.

Notation "lc '~~>' pf" :=
  (reachableFrom_congress lc pf)
  (at level 88, left associativity).

Definition congress_has_votes_on_some_proposal lc :=
  let congress_state_map := lc_contract_state_deserialized Congress.State lc in
  match FMap.find congress_contract_base_addr congress_state_map with
  | Some state =>
    let proposals := map snd (FMap.elements (proposals state)) in
    existsb (fun proposal => 
      0 <? FMap.size proposal.(votes)
    ) proposals
  | None => false
  end.

(* QuickChick (congress_chain ~~> congress_has_votes_on_some_proposal o next_lc_of_lcstep). *)
(* coqtop-stdout:
Begin Trace: 
step_action{
  Action{
    act_from: 12%256, 
    act_body: (act_call 128%256, 0, vote_against_proposal 1)}};;
step_action{
  Action{
    act_from: 11%256, 
    act_body: (act_call 128%256, 5, create_proposal (call: 128%256, 4, create_proposal (call: 128%256, 4, vote_against_proposal 1)))}}
End Trace
Success - found witness satisfying the predicate!
+++ Failed (as expected) after 15 tests and 0 shrinks. (0 discards)
*)

(* This assumes that in a previous block, there was an active proposal *)
Definition congress_finished_a_vote (lc_step : @LocalChainStep AddrSize) :=
  match lc_step with
  | step_add_block _ _ _ => false
  | step_action _ _ _ acts => 
    let act_is_finish_vote (act : Action) := match act.(act_body) with 
                                             | act_call _ _ msg => match deserialize Congress.Msg _ msg with 
                                                                   | Some (Congress.finish_proposal _) => true 
                                                                   | _ => false end  
                                             | _ => false end in
    existsb act_is_finish_vote acts
  end.

(* QuickChick (congress_chain ~~> congress_finished_a_vote). *)
(* Begin Trace: 
step_action{
  Action{
    act_from: 11%256, 
    act_body: (act_call 128%256, 3, finish_proposal 1)}};;
step_action{
  Action{
    act_from: 12%256, 
    act_body: (
      act_call 128%256, 0, create_proposal (
        call: 128%256, 0, create_proposal (
          call: 128%256, 2, change_rules Rules{
            min_vote_count_permille: 450, 
            margin_needed_permille: 467, 
            debating_period_in_blocks: 2})))}}
End Trace
Success - found witness satisfying the predicate!
+++ Failed (as expected) after 3 tests and 0 shrinks. (0 discards) *)