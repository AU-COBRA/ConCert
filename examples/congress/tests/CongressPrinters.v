From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Congress Require Import Congress.
From Coq Require Import List.
Open Scope string_scope.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

#[export]
Instance showRules : Show Rules :=
{|
  show r :=
    "Rules{"
    ++ "min_vote_count_permille: " ++ show (min_vote_count_permille r) ++ sep
    ++ "margin_needed_permille: " ++ show (margin_needed_permille r) ++ sep
    ++ "debating_period_in_blocks: " ++ show (debating_period_in_blocks r)
    ++ "}"
|}.

Definition string_of_ca (str_of_msg : Msg -> string) ca :=
  match ca with
  | cact_transfer to amount => "(transfer: " ++ show to ++ sep ++ show amount ++ ")"
  | cact_call to amount msg => "(call: " ++ show to ++ sep ++ show amount ++ sep ++
      match @deserialize Msg _ msg with
      | Some msg => str_of_msg msg
      | None => "<FAILED DESERIALIZATION>"
      end ++ ")"
  end.

#[export]
Instance showSetup : Show Setup :=
{|
  show v := show (setup_rules v)
|}.

(* Ugly fuel hack :/ *)
Fixpoint string_of_Msg (fuel : nat) (m : Msg) : string :=
  let show_acts actions :=
    match fuel with
    | 0 => String.concat "; " (map (fun _ => "Msg{...}") actions)
    | S fuel => String.concat "; " (map (string_of_ca (string_of_Msg fuel)) actions)
    end in
  match m with
  | transfer_ownership addr => "transfer_ownership " ++ show addr
  | change_rules rules => "change_rules " ++ show rules
  | add_member addr => "add_member " ++ show addr
  | remove_member addr => "remove_member " ++ show addr
  | create_proposal actions => "create_proposal " ++ show_acts actions
  | vote_for_proposal proposalId => "vote_for_proposal " ++ show proposalId
  | vote_against_proposal proposalId => "vote_against_proposal " ++ show proposalId
  | retract_vote proposalId => "retract_vote " ++ show proposalId
  | finish_proposal proposalId => "finish_proposal " ++ show proposalId
  end.

#[export]
Instance showMsg : Show Msg :=
{|
  show := string_of_Msg 20
|}.

(* TODO: fix printing for msg of type SerializedValue such that
   it works whenever it is serialized from type Msg *)
#[export]
Instance showCongressAction : Show CongressAction :=
{|
  show := string_of_ca (string_of_Msg 20)
|}.

#[export]
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

#[export]
Instance showState : Show Congress.State :=
{|
  show s := "State{"
            ++ "owner: " ++ show (owner s) ++ sep
            ++ "rules: " ++ show (state_rules s) ++ sep
            ++ "proposals: " ++ show (proposals s) ++ sep
            ++ "next_proposal_id: " ++ show (next_proposal_id s) ++ sep
            ++ "members: " ++ show (members s) ++ "}"
|}.

#[export]
Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg < Msg, Setup >.
