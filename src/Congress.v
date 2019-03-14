From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import Program.Basics.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Containers.
From RecordUpdate Require Import RecordUpdate.
(* This is included last to default things to list rather than map/set *)
From Coq Require Import List.

Import ListNotations.
Import RecordSetNotations.

Open Scope Z.
Set Primitive Projections.

Definition ProposalId := nat.

Inductive CongressAction :=
  | cact_transfer (to : Address) (amount : Amount)
  | cact_call (to : Address) (amount : Amount) (msg : OakValue).

Record Proposal :=
  build_proposal {
    actions : list CongressAction;
    votes : FMap Address Z;
    vote_result : Z;
    proposed_in : BlockId;
  }.

Instance eta_proposal : Settable _ :=
  mkSettable
    ((constructor build_proposal) <*> actions
                                  <*> votes
                                  <*> vote_result
                                  <*> proposed_in)%settable.

Record Rules :=
  build_rules {
    min_vote_count_permille : Z;
    margin_needed_permille : Z;
    debating_period_in_blocks : Z;
  }.

Record Setup :=
  build_setup {
    setup_rules : Rules;
  }.

Inductive Msg :=
  | transfer_ownership : Address -> Msg
  | change_rules : Rules -> Msg
  | add_member : Address -> Msg
  | remove_member : Address -> Msg
  | create_proposal : list CongressAction -> Msg
  | vote_for_proposal : ProposalId -> Msg
  | vote_against_proposal : ProposalId -> Msg
  | retract_vote : ProposalId -> Msg
  | finish_proposal : ProposalId -> Msg.

Record State :=
  build_state {
    owner : Address;
    state_rules : Rules;
    proposals : FMap nat Proposal;
    next_proposal_id : ProposalId;
    members : FMap Address unit;
  }.

Instance eta_state : Settable _ :=
  mkSettable
    ((constructor build_state) <*> owner
                               <*> state_rules
                               <*> proposals
                               <*> next_proposal_id
                               <*> members)%settable.

Definition version : Version := 1%nat.

Definition validate_rules (rules : Rules) : bool :=
    (rules.(min_vote_count_permille) >=? 0)
        && (rules.(min_vote_count_permille) <=? 1000)
        && (rules.(margin_needed_permille) >=? 0)
        && (rules.(margin_needed_permille) <=? 1000)
        && (rules.(debating_period_in_blocks) >=? 0).

Definition init (ctx : ContractCallContext) (setup : Setup) : option State :=
  if validate_rules setup.(setup_rules) then
    Some {| owner := ctx.(ctx_from);
            state_rules := setup.(setup_rules);
            proposals := FMap.empty;
            next_proposal_id := 1%nat;
            members := FMap.empty |}
  else
    None.

Definition add_proposal (actions : list CongressAction) (chain : Chain) (state : State) : State :=
  let id := state.(next_proposal_id) in
  let head_block := chain.(head_block) in
  let proposal := {| actions := actions;
                     votes := FMap.empty;
                     vote_result := 0;
                     proposed_in := head_block.(block_header).(block_number) |} in
  let new_proposals := FMap.add id proposal state.(proposals) in
  state[[proposals := new_proposals]][[next_proposal_id := (id + 1)%nat]].

Definition vote_on_proposal
           (voter : Address)
           (pid : ProposalId)
           (vote : Z)
           (state : State)
  : option State :=
  do proposal <- FMap.find pid state.(proposals);
  let old_vote := match FMap.find voter proposal.(votes) with
                 | Some old => old
                 | None => 0
                 end in
  let new_votes := FMap.add voter vote proposal.(votes) in
  let new_vote_result := proposal.(vote_result) - old_vote + vote in
  let new_proposal := proposal[[votes := new_votes]][[vote_result := new_vote_result]] in
  Some (state[[proposals ::= FMap.add pid new_proposal]]).

Definition do_retract_vote
           (voter : Address)
           (pid : ProposalId)
           (state : State)
  : option State :=
  do proposal <- FMap.find pid state.(proposals);
  do old_vote <- FMap.find voter proposal.(votes);
  let new_votes := FMap.remove voter proposal.(votes) in
  let new_vote_result := proposal.(vote_result) - old_vote in
  let new_proposal := proposal[[votes := new_votes]][[vote_result := new_vote_result]] in
  Some (state[[proposals ::= FMap.add pid new_proposal]]).

Definition congress_action_to_chain_action (act : CongressAction) : ChainAction :=
  match act with
  | cact_transfer to amt => act_transfer to amt
  | cact_call to amt msg => act_call to amt msg
  end.

Definition do_finish_proposal
           (pid : ProposalId)
           (state : State)
           (chain : Chain)
  : option (State * list ChainAction) :=
  do proposal <- FMap.find pid state.(proposals);
  let rules := state.(state_rules) in
  let debate_end := (Z.of_nat proposal.(proposed_in)) + rules.(debating_period_in_blocks) in
  let cur_block := chain.(head_block) in
  if (Z.of_nat cur_block.(block_header).(block_number)) <? debate_end then
    None
  else
    let new_state := state[[proposals ::= FMap.remove pid]] in
    let total_votes_for_proposal := Z.of_nat (FMap.size proposal.(votes)) in
    let total_members := Z.of_nat (FMap.size state.(members)) in
    let aye_votes := (proposal.(vote_result) + total_votes_for_proposal) / 2 in
    let vote_count_permille := total_votes_for_proposal * 1000 / total_members in
    let aye_permille := aye_votes * 1000 / total_votes_for_proposal in
    let enough_voters := vote_count_permille >=? rules.(min_vote_count_permille) in
    let enough_ayes := aye_permille >=? rules.(margin_needed_permille) in
    let response_acts :=
        if (enough_voters && enough_ayes)%bool
        then proposal.(actions)
        else [] in
    let response_chain_acts := map congress_action_to_chain_action response_acts in
    Some (new_state, response_chain_acts).

Definition receive
           (ctx : ContractCallContext)
           (state : State)
           (maybe_msg : option Msg)
  : option (State * list ChainAction) :=
  let chain := ctx.(ctx_chain) in
  let sender := ctx.(ctx_from) in
  let is_from_owner := (sender =? state.(owner))%address in
  let is_from_member := FMap.mem sender state.(members) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
  match is_from_owner, is_from_member, maybe_msg with
  | true, _, Some (transfer_ownership new_owner) =>
        Some (state[[owner := new_owner]], [])

  | true, _, Some (change_rules new_rules) =>
        if validate_rules new_rules then
            Some (state[[state_rules := new_rules]], [])
        else
            None

  | true, _, Some (add_member new_member) =>
        Some (state[[members ::= FMap.add new_member tt]], [])

  | true, _, Some (remove_member old_member) =>
        Some (state[[members ::= FMap.remove old_member]], [])

  | _, true, Some (create_proposal actions) =>
        Some (add_proposal actions chain state, [])

  | _, true, Some (vote_for_proposal pid) =>
        without_actions (vote_on_proposal sender pid 1 state)

  | _, true, Some (vote_against_proposal pid) =>
        without_actions (vote_on_proposal sender pid (-1) state)

  | _, true, Some (retract_vote pid) =>
        without_actions (do_retract_vote sender pid state)

  | _, _, Some (finish_proposal pid) =>
        do_finish_proposal pid state chain

  | _, _, _ =>
        None

  end.

Definition deserialize_rules (v : OakValue) : option Rules :=
  do '((a, b), c) <- deserialize v;
  Some (build_rules a b c).

Program Instance rules_equivalence : OakTypeEquivalence Rules :=
  {| serialize r := let (a, b, c) := r in serialize (a, b, c);
     (* Why does
     deserialize v :=
       do '((a, b), c) <- deserialize v;
       Some (build_rules a b c); |}.
       not work here? *)
     deserialize := deserialize_rules; |}.
Next Obligation.
  intros x. unfold deserialize_rules.
  rewrite deserialize_serialize.
  reflexivity.
Qed.

Program Instance setup_equivalence : OakTypeEquivalence Setup :=
  {| serialize s := serialize s.(setup_rules);
     deserialize or :=
       do rules <- deserialize or;
       Some (build_setup rules); |}.
Next Obligation.
  intros x.
  simpl.
  rewrite deserialize_serialize.
  reflexivity.
Qed.

Definition deserialize_congress_action (v : OakValue) : option CongressAction :=
  do val <- deserialize v;
  Some (match val with
  | inl (to, amount) => cact_transfer to amount
  | inr (to, amount, msg) => cact_call to amount msg
  end).

Program Instance congress_action_equivalence : OakTypeEquivalence CongressAction :=
  {| serialize ca :=
       serialize
         match ca with
         | cact_transfer to amount => inl (to, amount)
         | cact_call to amount msg => inr (to, amount, msg)
         end;
     deserialize := deserialize_congress_action; |}.
Next Obligation.
  intros ca.
  unfold deserialize_congress_action.
  rewrite deserialize_serialize.
  destruct ca; reflexivity.
Qed.

Definition deserialize_proposal (v : OakValue) : option Proposal :=
  do '(a, b, c, d) <- deserialize v;
  Some (build_proposal a b c d).

Program Instance proposal_equivalence : OakTypeEquivalence Proposal :=
  {| serialize p :=
       let (a, b, c, d) := p in
       serialize (a, b, c, d);
     deserialize := deserialize_proposal;
  |}.
Next Obligation.
  intros p.
  unfold deserialize_proposal.
  rewrite deserialize_serialize.
  destruct p; reflexivity.
Qed.

Definition serialize_msg (m : Msg) : OakValue :=
  serialize
    match m with
    | transfer_ownership a => (0, serialize a)
    | change_rules r => (1, serialize r)
    | add_member a => (2, serialize a)
    | remove_member a => (3, serialize a)
    | create_proposal l => (4, serialize l)
    | vote_for_proposal pid => (5, serialize pid)
    | vote_against_proposal pid => (6, serialize pid)
    | retract_vote pid => (7, serialize pid)
    | finish_proposal pid => (8, serialize pid)
    end.

Definition deserialize_msg (v : OakValue) : option Msg :=
  do '(tag, v) <- deserialize v;
  match tag with
  | 0 => option_map transfer_ownership (deserialize v)
  | 1 => option_map change_rules (deserialize v)
  | 2 => option_map add_member (deserialize v)
  | 3 => option_map remove_member (deserialize v)
  | 4 => option_map create_proposal (deserialize v)
  | 5 => option_map vote_for_proposal (deserialize v)
  | 6 => option_map vote_against_proposal (deserialize v)
  | 7 => option_map retract_vote (deserialize v)
  | 8 => option_map finish_proposal (deserialize v)
  | _ => None
  end.

Program Instance msg_equivalence : OakTypeEquivalence Msg :=
  {| serialize := serialize_msg; deserialize := deserialize_msg; |}.
Next Obligation.
  intros msg.
  unfold serialize_msg, deserialize_msg.
  destruct msg; repeat (simpl; rewrite deserialize_serialize); reflexivity.
Qed.

Definition serialize_state (s : State) : OakValue :=
  let (a, b, c, d, e) := s in
  serialize (a, b, c, d, e).

Definition deserialize_state (v : OakValue) : option State :=
  do '(a, b, c, d, e) <- deserialize v;
  Some (build_state a b c d e).

Program Instance state_equivalence : OakTypeEquivalence State :=
  {| serialize := serialize_state; deserialize := deserialize_state; |}.
Next Obligation.
  unfold serialize_state, deserialize_state.
  destruct x; repeat (simpl; rewrite deserialize_serialize); reflexivity.
Qed.

Definition contract : Contract Setup Msg State :=
  build_contract version init receive.


(*
(* This first property states that the Congress will only send out actions
   to be performed if there is a matching CreateProposal somewhere in the
   past. That is, no CreateProposal can lead to two batches of actions being
   sent out, and the actions correspond to the ones passed in CreateProposal. *)
Theorem congress_no_unmatched_actions
        (chain : Chain)
        (
*)
