From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Program.Basics.
From Coq Require MSets FMapAVL.
From Coq Require OrderedTypeEx.
From SmartContracts Require Import Blockchain.
From RecordUpdate Require Import RecordUpdate.

Import ListNotations.
Import RecordSetNotations.

Definition TxOut := nat.
Definition ProposalId := nat.
Definition Chain := nat.

Module AddressSet := MSetAVL.Make Address.as_modern_OT.
Module NatKeyedMap := FMapAVL.Make OrderedTypeEx.Nat_as_OT.
Module AddressKeyedMap := FMapAVL.Make Address.as_old_OT.

Record Proposal :=
  {
    txs : list TxOut ;
    votes : AddressKeyedMap.t Z ;
    voteResult : Z ;
    proposedIn : block_id
  }.

Instance etaProposal : Settable _ :=
  mkSettable
    ((constructor Build_Proposal) <*> txs
                                  <*> votes
                                  <*> voteResult
                                  <*> proposedIn)%set.

Record Rules :=
  {
    minVoteCountPermille : Z ;
    marginNeededPermille : Z ;
    debatingPeriodInBlocks : Z
  }.

Record Setup :=
  {
    setupRules : Rules
  }.

Inductive Msg :=
| TransferOwnership : address -> Msg
| ChangeRules : Rules -> Msg
| AddMember : address -> Msg
| RemoveMember : address -> Msg
| CreateProposal : list TxOut -> Msg
| VoteForProposal : ProposalId -> Msg
| VoteAgainstProposal : ProposalId -> Msg
| RetractVote : ProposalId -> Msg
| FinishProposal : ProposalId -> Msg.

Record State :=
  {
    owner : address ;
    stateRules : Rules ;
    proposals : NatKeyedMap.t Proposal ;
    nextProposalId : ProposalId ;
    members : AddressSet.t
  }.

Instance etaState : Settable _ :=
  mkSettable
    ((constructor Build_State) <*> owner
                               <*> stateRules
                               <*> proposals
                               <*> nextProposalId
                               <*> members)%set.
  
Definition version : version := 1.

Definition validateRules (rules : Rules) : bool :=
    (rules.(minVoteCountPermille) >=? 0)%Z
        && (rules.(minVoteCountPermille) <=? 1000)%Z
        && (rules.(marginNeededPermille) >=? 0)%Z
        && (rules.(marginNeededPermille) <=? 1000)%Z
        && (rules.(debatingPeriodInBlocks) >=? 0)%Z.


Definition init (chain : Chain) (details : contract_call_details) (setup : Setup) : option State :=
  if validateRules setup.(setupRules) then
    Some {| owner := details.(from) ;
            stateRules := setup.(setupRules) ; 
            proposals := NatKeyedMap.empty _ ;
            nextProposalId := 1 ;
            members := AddressSet.empty |}
  else
    None.

Definition addProposal (txs : list TxOut) (chain : Chain) (state : State) : State :=
  let id := state.(nextProposalId) in
  let proposal := {| txs := txs ;
                     votes := AddressKeyedMap.empty _ ;
                     voteResult := 0 ;
                     proposedIn := 0 |} in (* todo: fixme *)
  let newProposals := NatKeyedMap.add id proposal state.(proposals) in
  state[proposals := newProposals][nextProposalId := id + 1].

Local Definition option_bind {A B : Type} (f : A -> option B) (v : option A) : option B :=
  match v with
  | Some val => f val
  | None => None
  end.

Local Notation "'do' X <- A ; B" := (option_bind (fun X => B) A)
                                      (at level 200, X ident, A at level 100, B at level 200).

Local Notation unit := Some.

Definition voteProposal
           (voter : address)
           (pid : ProposalId)
           (vote : Z)
           (state : State)
  : option State :=
  do proposal <- NatKeyedMap.find pid state.(proposals) ;
  let oldVote := match AddressKeyedMap.find voter proposal.(votes) with
                 | Some oldVote => oldVote
                 | None => 0%Z
                 end in
  let newVotes := AddressKeyedMap.add voter vote proposal.(votes) in
  let newVoteResult := (proposal.(voteResult) - oldVote + vote)%Z in
  let newProposal := proposal[votes := newVotes][voteResult := newVoteResult] in
  unit (set proposals (NatKeyedMap.add pid newProposal) state).

Definition retractVote
           (voter : address)
           (pid : ProposalId)
           (state : State)
  : option State :=
  do proposal <- NatKeyedMap.find pid state.(proposals) ;
  do oldVote <- AddressKeyedMap.find voter proposal.(votes) ;
  let newVotes := AddressKeyedMap.remove voter proposal.(votes) in
  let newVoteResult := (proposal.(voteResult) - oldVote)%Z in
  let newProposal := proposal[votes := newVotes][voteResult := newVoteResult] in
  unit (set proposals (NatKeyedMap.add pid newProposal) state).

Definition finishProposal
           (pid : ProposalId)
           (state : State)
           (chain : Chain)
  : option (State * list TxOut) :=
  do proposal <- NatKeyedMap.find pid state.(proposals) ;
  let rules := state.(stateRules) in
  let debateEnd := ((Z.of_nat proposal.(proposedIn)) + rules.(debatingPeriodInBlocks))%Z in
  let curBlock := 0%Z in (* todo: fixme *)
  if (curBlock <? debateEnd)%Z then
    None
  else
    let newState := set proposals (NatKeyedMap.remove pid) state in
    let totalVotesForProposal := Z.of_nat (AddressKeyedMap.cardinal proposal.(votes)) in
    let totalMembers := Z.of_nat (AddressSet.cardinal state.(members)) in
    let ayeVotes := ((proposal.(voteResult) + totalVotesForProposal) / 2)%Z in
    let voteCountPermille := (totalVotesForProposal * 1000 / totalMembers)%Z in
    let ayePermille := (ayeVotes * 1000 / totalVotesForProposal)%Z in
    let enoughVoters : bool := (voteCountPermille >=? rules.(minVoteCountPermille))%Z in
    let enoughAyes : bool := (ayePermille >=? rules.(marginNeededPermille))%Z in
    let responseTxs := if (enoughVoters && enoughAyes)%bool then proposal.(txs) else [] in
    unit (newState, responseTxs).

Definition receive
           (chain : Chain)
           (state : State)
           (details : contract_call_details)
           (maybeMsg : option Msg)
  : option (State * list TxOut) :=
  let sender := details.(from) in
  let isFromOwner := sender =? state.(owner) in
  let isFromMember := AddressSet.mem sender state.(members) in
  let withoutTxs := option_map (fun newState => (newState, [])) in
  match isFromOwner, isFromMember, maybeMsg with
  | true, _, Some (TransferOwnership newOwner) =>
        Some (state[owner := newOwner], [])

  | true, _, Some (ChangeRules newRules) =>
        if validateRules newRules then
        Some (state[stateRules := newRules], [])
        else
        None

  | true, _, Some (AddMember newMember) =>
        let newMembers := AddressSet.add newMember state.(members) in
        Some (state[members := newMembers], [])

  | true, _, Some (RemoveMember oldMember) =>
        let newMembers := AddressSet.remove oldMember state.(members) in
        Some (state[members := newMembers], [])

  | _, true, Some (CreateProposal txs) =>
        Some (addProposal txs chain state, [])

  | _, true, Some (VoteForProposal id) =>
        withoutTxs (voteProposal sender id 1 state)

  | _, true, Some (VoteAgainstProposal id) =>
        withoutTxs (voteProposal sender id (-1) state)
                              
  | _, true, Some (RetractVote id) =>
        withoutTxs (retractVote sender id state)

  | _, _, Some (FinishProposal id) =>
        finishProposal id state chain

  | _, _, _ =>
        None
    
  end.
                                       