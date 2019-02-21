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

Record Proposal :=
  {
    txs : list TxOut ;
    votes : list (address * Z) ;
    voteResult : Z ;
    proposedIn : block_id
  }.

Module AddressSet := MSetAVL.Make Address.as_modern_OT.
Module NatKeyedMap := FMapAVL.Make OrderedTypeEx.Nat_as_OT.

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
                     votes := [] ;
                     voteResult := 0 ;
                     proposedIn := 0 |} in
  let newProposals := NatKeyedMap.add id proposal state.(proposals) in
  state[proposals := newProposals][nextProposalId := id + 1].

Definition receive
           (chain : Chain)
           (state : State)
           (details : contract_call_details)
           (maybeMsg : option Msg)
  : option (State * list TxOut) :=
  let sender := details.(from) in
  let isFromOwner := sender =? state.(owner) in
  let isFromMember := AddressSet.mem sender state.(members) in
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

  | _, _, _ =>
        None
    
  end.
                                       

(*
module Congress exposing (Msg(..), Proposal, ProposalId, Rules, Setup, State, init, receive, version)

{-| Implements a congress contract. This is based on an example contract of the same name
in Ethereum. This is essentially a simpler version of the DAO contract that was exploited
in 2016.

The congress allows its members to vote on proposals. A proposal is a transaction that
will be sent to a specified address if the proposal passes. That means the members of
the congress vote on how the funds are used by the congress.

Initially the creator of the contract is the owner of the congress. The owner has the
capability to add or remove members of the congress but they can also transfer ownership
of the congress to someone else.

The transaction in the proposal can be any arbitrary transaction, including calls to
other contracts. This makes some very interesting interactions possible. For instance,
the congress can be set as its own owner and then members can be added or removed only
by vote, or the rules (like margin required for a proposal to pass) can be changed only
by vote.

-}

import Blockchain2 as Blockchain exposing (Address, Amount, BlockId, Chain, SerializedMsg, Tx, TxOut, Version)
import Dict exposing (Dict)
import Set exposing (Set)


type alias ProposalId =
    Int


type alias Proposal =
    { -- Transactions to make if this proposal succeeds
      txs : List TxOut

    -- What are the votes?
    , votes : Dict Address Int

    -- Vote result (aye = +1, nay = -1)
    , voteResult : Int

    -- When was this proposal made?
    , proposedIn : BlockId
    }


type alias Rules =
    { -- Minimum permille of participating members for a vote to succeed.
      -- For instance, if 500, then at least 50% of the members must participate
      -- in a vote on a proposal for it to succeed.
      minVoteCountPermille : Int

    -- What is the required permille of ayes / total (500 = 50%)
    , marginNeededPermille : Int

    -- Number of blocks to debate a proposal
    , debatingPeriodInBlocks : Int
    }


type alias Setup =
    { rules : Rules }


type Msg
    = TransferOwnership Address
    | ChangeRules Rules
    | AddMember Address
    | RemoveMember Address
    | CreateProposal (List TxOut)
    | VoteForProposal ProposalId
    | VoteAgainstProposal ProposalId
    | RetractVote ProposalId
    | FinishProposal ProposalId


type alias State =
    { owner : Address
    , rules : Rules
    , proposals : Dict ProposalId Proposal
    , nextProposalId : ProposalId
    , members : Set Address
    }


version : Version
version =
    1


init : Setup -> Chain -> Tx -> Maybe State
init { rules } chain tx =
    if validateRules rules then
        Just
            { owner = tx.from
            , rules = rules
            , proposals = Dict.empty
            , nextProposalId = 1
            , members = Set.empty
            }

    else
        Nothing


validateRules : Rules -> Bool
validateRules rules =
    (rules.minVoteCountPermille >= 0)
        && (rules.minVoteCountPermille <= 1000)
        && (rules.marginNeededPermille >= 0)
        && (rules.marginNeededPermille <= 1000)
        && (rules.debatingPeriodInBlocks > 0)


receive : Chain -> State -> Tx -> Maybe Msg -> Maybe ( State, List TxOut )
receive chain state tx maybeMsg =
    let
        sender =
            tx.from

        isFromOwner =
            sender == state.owner

        isFromMember =
            Set.member sender state.members

        withoutTxs =
            Maybe.map (\s -> ( s, [] ))
    in
    case ( isFromOwner, isFromMember, maybeMsg ) of
        ( True, _, Just (TransferOwnership newOwner) ) ->
            Just ( { state | owner = newOwner }, [] )

        ( True, _, Just (ChangeRules newRules) ) ->
            if validateRules newRules then
                Just ( { state | rules = newRules }, [] )

            else
                Nothing

        ( True, _, Just (AddMember member) ) ->
            Just ( { state | members = Set.insert member state.members }, [] )

        ( True, _, Just (RemoveMember member) ) ->
            Just ( { state | members = Set.remove member state.members }, [] )

        ( _, True, Just (CreateProposal txs) ) ->
            Just ( addProposal txs chain state, [] )

        ( _, True, Just (VoteForProposal id) ) ->
            voteProposal sender id 1 state |> withoutTxs

        ( _, True, Just (VoteAgainstProposal id) ) ->
            voteProposal sender id -1 state |> withoutTxs

        ( _, True, Just (RetractVote id) ) ->
            retractVote sender id state |> withoutTxs

        ( _, _, Just (FinishProposal id) ) ->
            finishProposal id state chain

        _ ->
            Nothing


addProposal : List TxOut -> Chain -> State -> State
addProposal proposalTxs chain state =
    let
        id =
            state.nextProposalId

        headBlock =
            Blockchain.headBlock chain

        proposal =
            { txs = proposalTxs
            , votes = Dict.empty
            , voteResult = 0
            , proposedIn = headBlock.header.blockNumber
            }
    in
    { state
        | proposals = Dict.insert id proposal state.proposals
        , nextProposalId = id + 1
    }


voteProposal : Address -> ProposalId -> Int -> State -> Maybe State
voteProposal voter id vote state =
    case Dict.get id state.proposals of
        Nothing ->
            Nothing

        Just proposal ->
            let
                addVote diff =
                    let
                        newProposal =
                            { proposal
                                | votes = Dict.insert voter vote proposal.votes
                                , voteResult = proposal.voteResult + diff
                            }

                        newState =
                            { state | proposals = Dict.insert id newProposal state.proposals }
                    in
                    Just newState
            in
            case Dict.get voter proposal.votes of
                Nothing ->
                    addVote vote

                Just oldVote ->
                    addVote (vote - oldVote)


retractVote : Address -> ProposalId -> State -> Maybe State
retractVote voter id state =
    case Dict.get id state.proposals of
        Nothing ->
            Nothing

        Just proposal ->
            case Dict.get voter proposal.votes of
                Nothing ->
                    Nothing

                Just oldVote ->
                    let
                        newProposal =
                            { proposal
                                | votes = Dict.remove voter proposal.votes
                                , voteResult = proposal.voteResult - oldVote
                            }

                        newState =
                            { state | proposals = Dict.insert id newProposal state.proposals }
                    in
                    Just newState


finishProposal : ProposalId -> State -> Chain -> Maybe ( State, List TxOut )
finishProposal id ({ rules, proposals, members } as state) chain =
    case Dict.get id proposals of
        Nothing ->
            Nothing

        Just proposal ->
            let
                headBlock =
                    Blockchain.headBlock chain

                debateEnd =
                    proposal.proposedIn + rules.debatingPeriodInBlocks
            in
            if headBlock.header.blockNumber < debateEnd then
                Nothing

            else
                let
                    newState =
                        { state | proposals = Dict.remove id proposals }

                    totalVotesForProposal =
                        Dict.size proposal.votes

                    totalMembers =
                        Set.size members

                    -- ayes - nays = voteResult
                    -- ayes + nays = totalVotesForProposal
                    -- => 2ayes = votesResult + totalVotes
                    ayeVotes =
                        (proposal.voteResult + totalVotesForProposal) // 2

                    voteCountPermille =
                        totalVotesForProposal * 1000 // totalMembers

                    ayePermille =
                        ayeVotes * 1000 // totalVotesForProposal

                    responseTxs =
                        if
                            (voteCountPermille >= rules.minVoteCountPermille)
                                && (ayePermille >= rules.marginNeededPermille)
                        then
                            proposal.txs

                        else
                            []
                in
                Just ( newState, responseTxs )
*)