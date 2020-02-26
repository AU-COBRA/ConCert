From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters.

Require Import ZArith Strings.Ascii Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Require Import Containers.
Notation "f 'o' g" := (compose f g) (at level 50).
Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.
Open Scope string_scope.


Instance showRules : Show Rules :=
{|
  show r := 
    "Rules{"
    ++ "min_vote_count_permille: " ++ show (min_vote_count_permille r) ++ sep
    ++ "margin_needed_permille: " ++ show (margin_needed_permille r) ++ sep
    ++ "debating_period_in_blocks: " ++ show (debating_period_in_blocks r) 
    ++ "}"
|}.


(* TODO: fix printing for msg of type SerializedValue such that it works whenever it is serialized from type Msg *)
Instance showCongressAction : Show CongressAction :=
{|
  show ca :=
    match ca with
    | cact_transfer to amount => "(transfer: " ++ show to ++ sep ++ show amount ++ ")"
    | cact_call to amount msg => "(call: " ++ show to ++ sep ++ show amount ++ sep ++  show msg ++ ")" 
    end
|}.

Instance showProposal : Show Proposal :=
{|
  show p :=
    "Proposal{"
    ++ "actions: " ++ show (actions p) ++ sep
    ++ "votes: " ++ show (votes p) ++ sep
    ++ "vote_result: " ++ show (vote_result p) ++ sep
    ++ "proposed_in: " ++ show (proposed_in p) ++ sep
    ++ "}" ++ newline
|}.

Instance showSetup : Show Setup :=
{|
  show := show o setup_rules
|}.


Definition string_of_Msg (m : Msg) : string :=
  match m with
    | transfer_ownership addr => "(transfer_ownership " ++  show addr ++ ")"
    | change_rules rules => "(change_rules " ++ show rules ++ ")"
    | add_member addr => "(add_member " ++ show addr ++ ")"
    | remove_member addr => "(remove_member " ++ show addr ++ ")"
    | create_proposal actions => "(create_proposal " ++ show actions ++ ")"
    (* | create_proposal actions => "(create_proposal " ++  String.concat "; " (map (@show _ (@showCongressAction showSer) ) actions) ++ ")" *)
    | vote_for_proposal proposalId => "(vote_for_proposal " ++ show proposalId ++ ")"
    | vote_against_proposal proposalId => "(vote_against_proposal " ++ show proposalId ++ ")"
    | retract_vote proposalId => "(retract_vote " ++ show proposalId ++ ")"
    | finish_proposal proposalId => "(finish_proposal " ++ show proposalId ++ ")"
  end.

Instance showMsg : Show Msg :=
{|
  show := string_of_Msg
|}.


Instance showState : Show Congress.State :=
{|
  show s := "State{" 
            ++ "owner: " ++ show (owner s) ++ sep
            ++ "rules: " ++ show (state_rules s) ++ sep
            ++ "proposals: " ++ show (proposals s) ++ sep
            ++ "next_proposal_id: " ++ show (next_proposal_id s) ++ sep
            ++ "members: " ++ show (members s) ++ "}"
|}.

Close Scope string_scope.