From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Congress Require Import Congress.
From ConCert.Examples.Congress Require Export CongressGens.
From ConCert.Examples.Congress Require Export CongressPrinters.
From Coq Require Import ZArith.
From Coq Require Import List. Import ListNotations.


Definition LocalChainBase : ChainBase := TestUtils.LocalChainBase.

Definition chain1 : ChainBuilder := builder_initial.
Definition chain2 : ChainBuilder := unpack_result (add_block chain1 []).
Definition chain3 : ChainBuilder := unpack_result
  (add_block chain2 [build_transfer creator person_1 10]).

Definition setup_rules :=
  {| min_vote_count_permille := 200; (* 20% of congress needs to vote *)
      margin_needed_permille := 501;
      debating_period_in_blocks := 0; |}.

Definition setup := Congress.build_setup setup_rules.
Definition deploy_congress : ActionBody :=
  create_deployment 5 Congress.contract setup.
Definition chain4 : ChainBuilder :=
  unpack_result (add_block chain3 [build_deploy person_1 5 Congress.contract setup]).
Definition congress_1 : Address :=
  match outgoing_txs (builder_trace chain4) person_1 with
  | tx :: _ => tx_to tx
  | _ => person_1
  end.
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

(* person_1 adds person_1 and person_2 as members of congress *)
Definition add_person p :=
  congress_ifc.(send) 0 (Some (add_member p)).
Definition chain5 : ChainBuilder :=
  let acts := [build_act person_1 person_1 (add_person person_1);
               build_act person_1 person_1 (add_person person_2)] in
  unpack_result (add_block chain4 acts).
Definition create_proposal_call :=
  congress_ifc.(send) 0 (Some (create_proposal [cact_transfer person_3 3])).

Definition congress_chain := chain5.
Definition congress_caddr := addr_of_Z 128%Z.

Module NotationInfo <: TestNotationParameters.
  Definition gAction := (fun env => GCongressAction env act_depth congress_caddr).
  Definition init_cb := congress_chain.
End NotationInfo.
Module TN := TestNotations NotationInfo. Import TN.
(* Sample gChain. *)

Definition nr_cacts (msg : option Congress.Msg) :=
  match msg with
  | Some (create_proposal ls) => length ls
  | _ => 0
  end.

Definition num_cacts_in_state state :=
  sumnat (fun '(k, v) => length (actions v)) (FMap.elements (proposals state)).

(* This property states that the number of actions to be performed by the congress never increases
   more than the actions that are added in proposals, i.e. actions can't appear out of nowhere. *)
(* If we replace '<=' with '<' QC finds a counterexample - a proposal can contain an empty list of actions, so they are equal before/after add_proposal *)
Definition receive_state_well_behaved state msg new_state (resp_acts : list ActionBody) :=
  num_cacts_in_state new_state + length resp_acts <=
  num_cacts_in_state state + nr_cacts msg.

#[export]
Instance receive_state_well_behaved_dec_ {state : Congress.State}
                                         {msg : option Congress.Msg}
                                         {new_state : Congress.State}
                                         {resp_acts : list ActionBody}
                                         : Dec (receive_state_well_behaved state msg new_state resp_acts).
Proof.
  intros;
  unfold receive_state_well_behaved;
  constructor;
  apply le_dec.
Qed.

#[export]
Instance receive_state_well_behaved_checkable {state : Congress.State}
                                              {msg : option Congress.Msg}
                                              {new_state : Congress.State}
                                              {resp_acts : list ActionBody}
                                              : Checkable (receive_state_well_behaved state msg new_state resp_acts).
Proof. apply testDec. Qed.

Definition receive_state_well_behaved_P (chain : Chain)
                                        (cctx : ContractCallContext)
                                        (old_state : Congress.State)
                                        (msg : Congress.Msg)
                                        (result : option (Congress.State * list ActionBody)) :=
  checker match result with
  | Some (new_state, resp_acts) =>
    (receive_state_well_behaved old_state (Some msg) new_state resp_acts)?
  | _ => false
  end.

(* QuickChick (
  {{fun _ _ => true}}
  congress_caddr
  {{receive_state_well_behaved_P}}
). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Open Scope nat.

(* A property about the way States are generated. *)
(* It says that a State generated at some time slot cannot contain proposals later than this time slot. *)
Definition state_proposals_proposed_in_valid_P (block_slot : nat) (state : Congress.State) :=
  let proposals := map snd (FMap.elements (proposals state)) in
  forallb (fun p => proposed_in p <=? block_slot) proposals.

Definition state_proposals_proposed_in_valid (cs : ChainState) :=
  let state_opt := get_contract_state Congress.State cs congress_caddr in
  whenFail (show cs.(env_chain))
  match state_opt with
  | Some state => checker (state_proposals_proposed_in_valid_P cs.(current_slot) state)
  | None => checker true
  end.

(* QuickChick (forAllBlocks state_proposals_proposed_in_valid). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition congress_has_votes_on_some_proposal (cs : ChainState) :=
  let state_opt := get_contract_state Congress.State cs congress_caddr in
  match state_opt with
  | Some state =>
       let proposals := map snd (FMap.elements (proposals state)) in
    existsb (fun proposal =>
      0 <? FMap.size proposal.(votes)
    ) proposals
  | None => false
  end.

(* QuickChick (chain5 ~~> congress_has_votes_on_some_proposal). *)
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 7 tests and 0 shrinks. (0 discards) *)

(* This assumes that in a previous block, there was an active proposal *)
Definition congress_finished_a_vote (cs : ChainState) :=
  let acts := cs.(chain_state_queue) in
  let act_is_finish_vote (act : Action) :=
    match act.(act_body) with
    | act_call _ _ msg =>
      match deserialize Congress.Msg _ msg with
      | Some (Congress.finish_proposal _) => true
      | _ => false
      end
    | _ => false
    end in
    existsb act_is_finish_vote acts.

(* QuickChick (chain5 ~~> congress_finished_a_vote). *)
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 14 tests and 0 shrinks. (0 discards) *)
