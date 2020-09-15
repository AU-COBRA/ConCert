From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import
  TestUtils CongressGens TraceGens SerializablePrinters.

Require Import ZArith.

From QuickChick Require Import QuickChick. Import QcNotation.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Require Import Containers.

Notation "f 'o' g" := (compose f g) (at level 50).
Definition LocalChainBase : ChainBase := TestUtils.LocalChainBase.

Definition chain1 : ChainBuilder := builder_initial.
Definition chain2 : ChainBuilder := unpack_result (add_block chain1 []).
Definition chain3 : ChainBuilder := unpack_result
  (add_block chain2 [build_act creator (act_transfer person_1 10)]).

Definition setup_rules :=
  {| min_vote_count_permille := 200; (* 20% of congress needs to vote *)
      margin_needed_permille := 501;
      debating_period_in_blocks := 0; |}.

Definition setup := Congress.build_setup setup_rules.
Definition deploy_congress : ActionBody :=
  create_deployment 5 Congress.contract setup.
Definition chain4 : ChainBuilder :=
  unpack_result (add_block chain3 [build_act person_1 deploy_congress]).
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
  let acts := [build_act person_1 (add_person person_1);
                build_act person_1 (add_person person_2)] in
  unpack_result (add_block chain4 acts).
Definition create_proposal_call :=
  congress_ifc.(send) 0 (Some (create_proposal [cact_transfer person_3 3])).
Definition chain6 : ChainBuilder :=
  unpack_result (add_block chain5 [build_act person_1 create_proposal_call]).

Definition congress_chain := chain5.
Definition congress_caddr := BoundedN.of_Z_const AddrSize 128%Z.

Definition gCongressChain max_acts_per_block congress_cb max_length := 
  let act_depth := 2 in 
  gChain congress_cb
    (fun env act_depth => GCongressAction env act_depth congress_caddr) max_length act_depth max_acts_per_block.

Definition forAllCongressChainTraces n :=
  forAllChainState n congress_chain (gCongressChain 1).

Definition pre_post_assertion_congress P c Q :=
  pre_post_assertion 5 congress_chain (gCongressChain 2) Congress.contract c P Q.

Notation "{{ P }} c {{ Q }}" := (pre_post_assertion_congress P c Q) ( at level 50).

Definition nr_cacts (msg : option Congress.Msg) :=
  match msg with
  | Some (create_proposal ls) => length ls
  | _ => 0
  end.

(* This property states that the number of actions to be performed by the congress never increases
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
  intros;
  unfold receive_state_well_behaved;
  constructor;
  apply le_dec.
Qed.

Instance receive_state_well_behaved_checkable {state : Congress.State}
                                              {msg : option Congress.Msg}
                                              {new_state : Congress.State}
                                              {resp_acts : list ActionBody}
                                              : Checkable (receive_state_well_behaved state msg new_state resp_acts).
Proof. apply testDec. Qed.

Definition receive_state_well_behaved_P (cctx : ContractCallContext)
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
  
(* QuickChick (forAllCongressChainTraces 5 state_proposals_proposed_in_valid). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition reachableFrom_chaintrace_congress (cb : ChainBuilder) pf : Checker :=
  reachableFrom_chaintrace cb (gCongressChain 1) pf.

Notation "lc '~~>' pf" :=
  (reachableFrom_chaintrace_congress lc pf)
  (at level 88, left associativity).

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
  let act_is_finish_vote (act : Action) := match act.(act_body) with
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
