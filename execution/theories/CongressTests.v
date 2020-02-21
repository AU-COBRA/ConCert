From ConCert Require Import Generators Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
Require Import ZArith Strings.Ascii Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import List.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Import ListNotations.
Notation "f 'o' g" := (compose f g) (at level 50).

(* Generators for the types defined in the Congress contract *)

Let BaseTypes := LocalChainBase AddrSize.
Example ca : @CongressAction BaseTypes := cact_transfer zero_address 0%Z.
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

Instance showCongressAction `{Show SerializedValue} : Show CongressAction :=
  {|
    show ca :=
      match ca with
      | cact_transfer to amount => "(transfer: " ++ show to ++ sep ++ show amount ++ ")"
      | cact_call to amount msg => "(call: " ++ show to ++ sep ++ show amount ++ sep ++ show msg ++ ")" 
      end
  |}.

Instance showProposal : Show Proposal :=
  {|
    show p :=
      "Proposal{"
      ++ "actions: " ++ show (actions p)
      ++ "votes: " ++ "..." (*show (votes p)*)
      ++ "vote_result: " ++ show (vote_result p) 
      ++ "proposed_in: " ++ show (proposed_in p) 
      ++ "}"
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
    | vote_for_proposal proposalId => "(vote_for_proposal " ++ show proposalId ++ ")"
    | vote_against_proposal proposalId => "(vote_against_proposal " ++ show proposalId ++ ")"
    | retract_vote proposalId => "(retract_vote " ++ show proposalId ++ ")"
    | finish_proposal proposalId => "(finish_proposal " ++ show proposalId ++ ")"
  end.

Instance showMsg : Show Msg :=
{|
  show := string_of_Msg
|}.

Close Scope string_scope.

Definition gRulesSized (n : nat) : G Rules :=
  vote_count <- arbitrarySized n ;;
  margin <- liftM Z.of_nat (gIntervalNat n (2 * n)) ;;
  liftM (build_rules vote_count margin) arbitrary.  

Instance genRulesSized : GenSized Rules :=
  {|
    arbitrarySized := gRulesSized
  |}.


Definition gCongressAction {ctx : ChainContext BaseTypes}
                           (gMsg : G SerializedValue) 
                           : G CongressAction :=
  let gAddr := (gInvalidContractAddr BaseTypes ctx) in
  freq [
    (1, liftM2 cact_transfer gAddr arbitrary);
    (1, liftM3 cact_call gAddr arbitrary gMsg)
  ].

Fixpoint gMsgSized {ctx : ChainContext BaseTypes} (n : nat) : G Msg :=
  let nonrec_gens := [
      (1, liftM transfer_ownership (gInvalidContractAddr _ ctx)) ;
      (1, liftM change_rules arbitrary) ;
      (1, liftM add_member (gInvalidContractAddr _ ctx)) ;
      (1, liftM remove_member (gInvalidContractAddr _ ctx)) ;
      (1, liftM vote_for_proposal arbitrary) ;
      (1, liftM vote_against_proposal arbitrary) ;
      (1, liftM retract_vote arbitrary) ;
      (1, liftM finish_proposal arbitrary)
    ] in 
  let default := liftM transfer_ownership (gInvalidContractAddr _ ctx) in
  match n with
    | 0 => (freq_ default nonrec_gens)
    | S n' =>
    let rec_gens := 
      (1, liftM create_proposal (listOf (@gCongressAction ctx (liftM serialize (@gMsgSized ctx n')))))
      :: nonrec_gens in
    freq_ default rec_gens
  end.