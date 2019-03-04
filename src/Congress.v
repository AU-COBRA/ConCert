From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Program.Basics.
From Containers Require Import OrderedTypeEx.
From Containers Require Import MapInterface.
From Containers Require Import SetInterface.
From Containers Require MapAVL.
From Containers Require SetAVL.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.
From RecordUpdate Require Import RecordUpdate.

Import MapNotations.
Import ListNotations.
Import RecordSetNotations.

Open Scope Z.

Definition ProposalId := nat.

Record Proposal :=
  build_proposal {
    actions : list ChainAction;
    votes : Map[Address, Z];
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
| TransferOwnership : Address -> Msg
| ChangeRules : Rules -> Msg
| AddMember : Address -> Msg
| RemoveMember : Address -> Msg
| CreateProposal : list ChainAction -> Msg
| VoteForProposal : ProposalId -> Msg
| VoteAgainstProposal : ProposalId -> Msg
| RetractVote : ProposalId -> Msg
| FinishProposal : ProposalId -> Msg.

Record State :=
  build_state {
    owner : Address;
    state_rules : Rules;
    proposals : Map[nat, Proposal];
    next_proposal_id : ProposalId;
    members : SetInterface.set Address;
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
            proposals := []%map;
            next_proposal_id := 1%nat;
            members := {}%set |}
  else
    None.

Definition add_proposal (actions : list ChainAction) (chain : Chain) (state : State) : State :=
  let id := state.(next_proposal_id) in
  let head_block := chain.(head_block) in
  let proposal := {| actions := actions;
                     votes := []%map;
                     vote_result := 0;
                     proposed_in := head_block.(block_header).(block_number) |} in
  let new_proposals := state.(proposals)[id <- proposal]%map in
  state[[proposals := new_proposals]][[next_proposal_id := (id + 1)%nat]].

Definition vote_on_proposal
           (voter : Address)
           (pid : ProposalId)
           (vote : Z)
           (state : State)
  : option State :=
  do proposal <- state.(proposals)[pid]%map;
  let old_vote := match proposal.(votes)[voter]%map with
                 | Some old => old
                 | None => 0
                 end in
  let new_votes := proposal.(votes)[voter <- vote]%map in
  let new_vote_result := proposal.(vote_result) - old_vote + vote in
  let new_proposal := proposal[[votes := new_votes]][[vote_result := new_vote_result]] in
  Some (state[[proposals ::= MapInterface.add pid new_proposal]]).

Definition retract_vote
           (voter : Address)
           (pid : ProposalId)
           (state : State)
  : option State :=
  do proposal <- state.(proposals)[pid]%map;
  do old_vote <- proposal.(votes)[voter]%map;
  let new_votes := MapInterface.remove voter proposal.(votes) in
  let new_vote_result := proposal.(vote_result) - old_vote in
  let new_proposal := proposal[[votes := new_votes]][[vote_result := new_vote_result]] in
  Some (state[[proposals ::= MapInterface.add pid new_proposal]]).

Definition finish_proposal
           (pid : ProposalId)
           (state : State)
           (chain : Chain)
  : option (State * list ChainAction) :=
  do proposal <- state.(proposals)[pid]%map;
  let rules := state.(state_rules) in
  let debate_end := (Z.of_nat proposal.(proposed_in)) + rules.(debating_period_in_blocks) in
  let cur_block := chain.(head_block) in
  if (Z.of_nat cur_block.(block_header).(block_number)) <? debate_end then
    None
  else
    let new_state := state[[proposals ::= MapInterface.remove pid]] in
    let total_votes_for_proposal := Z.of_nat (MapInterface.cardinal proposal.(votes)) in
    let total_members := Z.of_nat (SetInterface.cardinal state.(members)) in
    let aye_votes := (proposal.(vote_result) + total_votes_for_proposal) / 2 in
    let vote_count_permille := total_votes_for_proposal * 1000 / total_members in
    let aye_permille := aye_votes * 1000 / total_votes_for_proposal in
    let enough_voters := vote_count_permille >=? rules.(min_vote_count_permille) in
    let enough_ayes := aye_permille >=? rules.(margin_needed_permille) in
    let response_acts :=
        if (enough_voters && enough_ayes)%bool
        then proposal.(actions)
        else [ ] in
    Some (new_state, response_acts).

Definition receive
           (ctx : ContractCallContext)
           (state : State)
           (maybe_msg : option Msg)
  : option (State * list ChainAction) :=
  let chain := ctx.(ctx_chain) in
  let sender := ctx.(ctx_from) in
  let is_from_owner := (sender =? state.(owner))%address in
  let is_from_member := (sender \in state.(members))%set in
  let without_actions := option_map (fun new_state => (new_state, [ ])) in
  match is_from_owner, is_from_member, maybe_msg with
  | true, _, Some (TransferOwnership new_owner) =>
        Some (state[[owner := new_owner]], [ ])

  | true, _, Some (ChangeRules new_rules) =>
        if validate_rules new_rules then
            Some (state[[state_rules := new_rules]], [ ])
        else
            None

  | true, _, Some (AddMember new_member) =>
        Some (state[[members ::= SetInterface.add new_member]], [ ])

  | true, _, Some (RemoveMember old_member) =>
        Some (state[[members ::= SetInterface.remove old_member]], [ ])

  | _, true, Some (CreateProposal actions) =>
        Some (add_proposal actions chain state, [ ])

  | _, true, Some (VoteForProposal pid) =>
        without_actions (vote_on_proposal sender pid 1 state)

  | _, true, Some (VoteAgainstProposal pid) =>
        without_actions (vote_on_proposal sender pid (-1) state)

  | _, true, Some (RetractVote pid) =>
        without_actions (retract_vote sender pid state)

  | _, _, Some (FinishProposal pid) =>
        finish_proposal pid state chain
 
  | _, _, _ =>
        None
    
  end.

Definition congress_contract : Contract Setup Msg State :=
  build_contract version init receive.