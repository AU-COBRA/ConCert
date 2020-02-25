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
Require Import Containers.
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

Definition deserialize_to_string (s : SerializedValue) : string := 
  match deserialize s with
  | Some v => show v
  | None => "?"
  end.


(* TODO: fix printing for msg of type SerializedValue such that it works whenever it is serialized from type Msg *)
Instance showCongressAction : Show CongressAction :=
  {|
    show ca :=
      match ca with
      | cact_transfer to amount => "(transfer: " ++ show to ++ sep ++ show amount ++ ")"
      | cact_call to amount msg => "(call: " ++ show to ++ sep ++ show amount ++ sep ++  show msg ++ ")" 
      end
  |}.

Definition string_of_FMap {A B : Type}
                         `{countable.Countable A}
                         `{base.EqDecision A}
                          (showA : A -> string) 
                          (showB : B -> string) 
                          (m : FMap A B) : string :=
  show (map (fun p => showA (fst p) ++ "-->" ++ showB (snd p)) (FMap.elements m)).

Instance showFMap {A B : Type}
                 `{countable.Countable A}
                 `{base.EqDecision A}
                 `{Show A} 
                 `{Show B}
                  : Show (FMap A B) :=
{|
  show := string_of_FMap show show
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

(* Generators *)


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



(* Helper generator and show instance for arbitrary FMaps *)

Fixpoint gFMapSized {A B : Type} 
                    {gA : G A} 
                    {gB : G B}
                    `{countable.Countable A}
                    `{base.EqDecision A}
                     (n : nat) : G (FMap A B) :=
  match n with
  | 0 => returnGen FMap.empty
  | S n' =>
    a <- gA ;;
    b <- gB ;;
    m <- @gFMapSized _ _ gA gB _ _ _ n' ;;
    returnGen (FMap.add a b m)  
  end.

Fixpoint gFMapFromInput {A B : Type}
                       `{countable.Countable A}
                       `{base.EqDecision A}     
                        (l1 : list A)
                        (l2 : list B)
                        : G (FMap A B) :=
  match (l1, l2) with
  | (a::l1', b::l2') => liftM (FMap.add a b) (gFMapFromInput l1' l2')
  | (_, _) => returnGen FMap.empty
  end.

Instance genFMapSized {A B : Type} 
                     `{Gen A} 
                     `{Gen B}
                     `{countable.Countable A}
                     `{base.EqDecision A}
                      : GenSized (FMap A B) :=
{|
  arbitrarySized := @gFMapSized A B arbitrary arbitrary _ _ _
|}.


Sample (@gFMapSized nat nat arbitrary arbitrary _ _ _ 2).




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


Sample (ctx <- @arbitrarySized _ genLocalBaseGens 1 ;; 
        ctx_gAccountAddr ctx).


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
        (7, gMsgSimple ctx)
      ]
  end.

Sample (ctx <- arbitrary ;; @gMsgSized ctx 4).

Example ex_simple_msg : Msg := create_proposal [cact_call zero_address 1%Z (serialize 123)].
Example ex_msg : Msg := create_proposal [cact_call zero_address 0%Z (serialize ex_simple_msg)].
Compute ((show o deserialize o serialize) ex_simple_msg).
Compute (show ex_msg). 



Definition gCongressActionSized {ctx : ChainContext LocalChainBase}
                                (n : nat)
                                : G CongressAction 
                                := @gCongressAction' ctx (liftM serialize (@gMsgSized ctx n)).


Sample (ctx <- arbitrary ;; gMsgSized ctx 3).

Example ex_call_congress_action := ctx <- arbitrary ;; 
                                   liftM (cact_call zero_address 0%Z) (liftM serialize (gMsgSized ctx 3) ).
Sample ex_call_congress_action.

Definition gProposalSized {ctx : ChainContext LocalChainBase} 
                          (n : nat)
                          : G Proposal :=
  bound <- arbitrarySized n ;;
  actions <- vectorOf bound (@gCongressActionSized ctx n) ;;
  let nr_votes := length (ctx_accounts ctx) in
  vote_vals <- vectorOf nr_votes arbitrary ;;
  votes <- gFMapFromInput (ctx_accounts ctx) vote_vals ;;
  vote_result <- gZPositive ;;
  proposed_in <- arbitrary ;;
  returnGen (build_proposal actions votes vote_result proposed_in).

Sample (ctx <- arbitrary ;; @gProposalSized ctx 1).



Fixpoint vectorOfCount {A : Type}
                      `{countable.Countable A} 
                       (default : A)
                       (n : nat) : G (list A) := 
  match n with
  | 0    => returnGen []
  | S n' => 
    match (countable.decode o Pos.of_nat) n with
    | Some a => liftM (cons a) (vectorOfCount default n')
    | None => liftM (cons default) (vectorOfCount default n')
    end
  end.



Definition gStateSized {ctx : ChainContext LocalChainBase} 
                       (n : nat) 
                       : G Congress.State :=
  let nr_accounts := length (ctx_accounts ctx) in
  default_addr <- (ctx_gAccountAddr ctx) ;;
  owner <- elems_ default_addr (ctx_accounts ctx) ;;
  rules <- arbitrarySized nr_accounts ;;
  proposalIds <- vectorOfCount 0 n ;;
  proposals <- vectorOf n (@gProposalSized ctx n) ;;
  proposals_map <- gFMapFromInput proposalIds proposals ;;
  next_proposal_id <- arbitrary ;; (* TODO: ensure valid proposal Id*)
  unit_list <- (vectorOf nr_accounts (returnGen tt)) ;;
  members <- gFMapFromInput (ctx_accounts ctx) unit_list ;;
  returnGen (build_state owner rules proposals_map next_proposal_id members).

Derive Show for unit.
(* Instance showUnit : Show unit := {| show u := "()" |}. *)

Instance showState : Show Congress.State :=
{|
  show s := "State{" 
            ++ "owner: " ++ show (owner s) ++ sep
            ++ "rules: " ++ show (state_rules s) ++ sep
            ++ "proposals: " ++ show (proposals s) ++ sep
            ++ "next_proposal_id: " ++ show (next_proposal_id s) ++ sep
            ++ "members: " ++ show (members s) ++ "}"
|}.

Sample (ctx <- arbitrary ;; @gStateSized ctx 3).


Definition init_is_valid p := 
  let ctx := fst p in
  let chain := (fst o snd) p in
  let setup := (snd o snd) p in
  match @Congress.init LocalChainBase chain ctx setup with
  | Some _ => true
  | None => false
  end.

(* QuickChick (forAll (
  ctx <- gLocalChainContext 2 ;;
  cctx <- @gContractCallContext LocalChainBase ctx ;;
  chain <- gLocalChainSized 2 ctx ;;
  setup <- @arbitrary Setup _ ;;
  returnGen (cctx, (chain, setup)))
  init_is_valid). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition num_cacts_in_state_deployment_P chain ctx setup (state : Congress.State) :=
  match init chain ctx setup with
  | Some state => (Congress.num_cacts_in_state state = 0)?
  | None => true
  end.

(* QuickChick (
  forAll
    (gLocalChainContext 2)
    (fun ctx => 
  forAll
    (gLocalChainSized 2 ctx)
    (fun chain =>
  forAll
    (@arbitrary Setup _)
    (fun setup => 
  forAll
    (@gStateSized ctx 4)
    (fun state => 
  forAll
    (@gContractCallContext LocalChainBase ctx) 
    (fun cctx => num_cacts_in_state_deployment_P chain cctx setup state)))))
  ). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

(* What this says is that the number of actions to be performed by the congress never increases 
   more than the actions that are added in proposals, ie. actions can't appear out of nowhere. *)
(* If we replace '<=' with '<' QC finds a counterexample - a proposal can contain an empty list of actions, so they are equal before/after add_proposal *)
Definition add_proposal_cacts_P cacts chain (state : Congress.State) :=
  num_cacts_in_state (add_proposal cacts chain state) <=?
  num_cacts_in_state state + length cacts.

Definition gChainActionsFromCongressActions ctx : G (list CongressAction) :=
  (listOf (@gCongressActionSized ctx 2)).

QuickChick (
  forAll
    (gLocalChainContext 2)
    (fun ctx => 
  forAll
    (gLocalChainSized 2 ctx)
    (fun chain => 
  forAll
    (@gStateSized ctx 2)
    (fun state => 
  forAll
    (gChainActionsFromCongressActions ctx)
    (fun cacts => add_proposal_cacts_P cacts chain state
    ))))
).
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)
Close Scope string_scope.
