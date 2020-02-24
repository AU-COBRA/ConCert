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
Definition LocalChainBase : ChainBase := Generators.LocalChainBase.
(* Let LocalBaseTypes := LocalChainBase AddrSize. *)
Example ca : @CongressAction LocalChainBase := cact_transfer zero_address 0%Z.
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

Definition string_of_Msg `{Show SerializedValue} (m : @Msg LocalChainBase) : string :=
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

Instance showMsg `{Show SerializedValue} : Show (@Msg LocalChainBase) :=
{|
  show := string_of_Msg
|}.


(* Generators *)

(* Helpers for ChainContext *)
Definition ctx_gAccountAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gInvalidContractAddr LocalChainBase ctx.
Definition ctx_gContractAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gValidContractAddr LocalChainBase ctx.
Definition ctx_gAnyAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gAddress LocalChainBase ctx.
Definition ctx_accounts (ctx : ChainContext LocalChainBase) : list Address := 
  @accounts LocalChainBase ctx.
Definition ctx_contracts (ctx : ChainContext LocalChainBase) : list Address := 
  @contracts LocalChainBase ctx.

Definition gZPositive := liftM Z.of_nat arbitrary.
Definition gZPositiveSized n := liftM Z.of_nat (arbitrarySized n).

Definition gRulesSized (n : nat) : G Rules :=
  vote_count <- gZPositiveSized n ;;
  margin <- liftM Z.of_nat (gIntervalNat n (2 * n)) ;;
  liftM (build_rules vote_count margin) arbitrary.  

Instance genRulesSized : GenSized Rules :=
  {|
    arbitrarySized := gRulesSized
  |}.

Instance genSetupSized : GenSized Setup := 
{|
  arbitrarySized n := liftM build_setup (arbitrarySized n)
|}.



Definition gCongressAction' {ctx : ChainContext LocalChainBase}
                           (gMsg : G SerializedValue) 
                           : G CongressAction :=
  (* We only want to generate positive amounts for now, but could be worth looking into *)
  freq [
    (1, liftM2 cact_transfer (ctx_gAccountAddr ctx) gZPositive);
    (1, liftM3 cact_call (ctx_gContractAddr ctx) gZPositive gMsg)
  ].
Sample (ctx <- @arbitrarySized _ genLocalBaseGens 1 ;; @gCongressAction' ctx arbitrary).



Definition gMsgSimple (ctx : ChainContext LocalChainBase) : G Msg := 
  freq [
    (1, liftM transfer_ownership (ctx_gAccountAddr ctx)) ;
    (1, liftM change_rules arbitrary) ;
    (2, liftM add_member (ctx_gAccountAddr ctx)) ;
    (2, liftM remove_member (ctx_gAccountAddr ctx)) ;
    (2, liftM vote_for_proposal arbitrary) ;
    (2, liftM vote_against_proposal arbitrary) ;
    (2, liftM retract_vote arbitrary) ;
    (2, liftM finish_proposal arbitrary)
  ].
Definition gMsg' : G Msg := 
  ctx <- arbitrary ;; gMsgSimple ctx.

Sample gMsg'.


Sample (ctx <- @arbitrarySized _ genLocalBaseGens 1 ;; @gInvalidContractAddr LocalChainBase ctx).


Fixpoint gMsgSized (ctx : ChainContext LocalChainBase) (n : nat) : G Msg :=
  let default := liftM transfer_ownership (ctx_gAccountAddr ctx) in
  match n with
    | 0 => gMsgSimple ctx
    | S n' => freq [
        (1, (* TODO: fix weight. should be roughly 1:8*)
        (* recurse. Msg is converted to a SerializedType using 'serialize' *)
        (* This makes it possible to create proposals about proposals about proposals etc... *)
        congressActions <- listOf (@gCongressAction' ctx (liftM serialize (gMsgSized ctx n'))) ;;
        returnGen (create_proposal congressActions)) ;
        (1, gMsgSimple ctx)
      ]
  end.

Sample (ctx <- arbitrary ;; @gMsgSized ctx 4).

Definition gCongressActionSized {ctx : ChainContext LocalChainBase}
                                (n : nat)
                                : G CongressAction := @gCongressAction' ctx (liftM serialize (@gMsgSized ctx n)).


Sample (ctx <- arbitrary ;; gMsgSized ctx 3).

Example ex_call_congress_action := ctx <- arbitrary ;; liftM (cact_call zero_address 0%Z) (liftM serialize (gMsgSized ctx 3) ).
Sample ex_call_congress_action.
Close Scope string_scope.