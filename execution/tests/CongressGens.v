From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters.

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

(* ChainGens for the types defined in the Congress contract *)

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.


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

Sample (ctx <- @arbitrarySized _ genLocalChainContext 1 ;; @gCongressAction' ctx arbitrary).



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


Sample (ctx <- @arbitrarySized _ genLocalChainContext 1 ;; 
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

Sample (ctx <- arbitrary ;; @gMsgSized ctx 1).

Example ex_simple_msg : Msg := create_proposal [cact_call zero_address 1%Z (serialize 123)].
Example ex_msg : Msg := create_proposal [cact_call zero_address 0%Z (serialize ex_simple_msg)].
(* Currently kinda buggy: nested messages (with create_proposal) dont properly show the inner, serialized messages *)
(* Compute ((show o deserialize o serialize) ex_simple_msg). *)
(* Compute (show ex_msg).  *)



Definition gCongressActionSized {ctx : ChainContext LocalChainBase}
                                (n : nat)
                                : G CongressAction 
                                := @gCongressAction' ctx (liftM serialize (@gMsgSized ctx n)).


Sample (ctx <- arbitrary ;; gMsgSized ctx 2).

Example ex_call_congress_action := ctx <- arbitrary ;; 
                                   liftM (cact_call zero_address 0%Z) (liftM serialize (gMsgSized ctx 2) ).
Sample ex_call_congress_action.

Open Scope Z_scope.

Definition gProposalSized {ctx : ChainContext LocalChainBase} 
                          (proposed_in : nat) (* obtained from the Chain *)
                          (nr_votes : nat)
                          (n : nat)
                                   : G Proposal :=
  bound <- arbitrarySized n ;;
  actions <- vectorOf bound (@gCongressActionSized ctx n) ;;
  vote_vals <- vectorOf nr_votes (elems [-1%Z; 1%Z]) ;; (* -1 = vote against, 1 = vote for*) 
  votes <- gFMapFromInput (ctx_accounts ctx) vote_vals ;;
  vote_result <- arbitrary ;;
  (* vote_result <- choose (-(Z.of_nat nr_votes), Z.of_nat nr_votes);; *)
  returnGen (build_proposal actions votes vote_result proposed_in).

Sample (ctx <- arbitrary ;; @gProposalSized ctx 0 10 1).


Close Scope Z_scope.

Definition gStateSized {ctx : ChainContext LocalChainBase} 
                       (current_slot : nat) (* used to ensure that the generated proposals are never proposed at a later date *)
                       (n : nat) 
                       : G Congress.State :=
  let nr_accounts := length (ctx_accounts ctx) in
  default_addr <- (ctx_gAccountAddr ctx) ;;
  owner <- elems_ default_addr (ctx_accounts ctx) ;;
  rules <- arbitrarySized n ;;
  proposalIds <- vectorOfCount 0 n ;;
  nr_votes <- choose (1, nr_accounts) ;;
  proposals <- vectorOf n (slot <- (arbitrarySized current_slot) ;; @gProposalSized ctx slot nr_votes  (n/2)) ;;
  proposals_map <- gFMapFromInput proposalIds proposals ;;
  next_proposal_id <- arbitrary ;; (* TODO: maybe just let it be 0*)
  unit_list <- (vectorOf nr_accounts (returnGen tt)) ;;
  members <- gFMapFromInput (ctx_accounts ctx) unit_list ;;
  returnGen (build_state owner rules proposals_map next_proposal_id members).

Definition gProposalIdFromState (state : Congress.State) : G ProposalId := 
  let pelems := FMap.elements (proposals state) in
  let pids := map fst pelems in
  (* Choose one proposal id at random. If empty, choose an arbitrary one. *)
  default_pid <- arbitrary ;; elems_ default_pid  pids.

Definition gProposalFromState {ctx : ChainContext LocalChainBase} 
                              (state : Congress.State)
                              (proposed_in : nat) 
                              : G Proposal := 
  let pelems := FMap.elements (proposals state) in
  let pids := map snd pelems in
  let max_nr_votes : nat := (length o FMap.elements) (members state) in
  (* Choose one proposal id at random. If empty, choose an arbitrary one. *)
  nr_votes <- arbitrarySized max_nr_votes ;;
  default_proposal <- @gProposalSized ctx proposed_in nr_votes 3 ;; 
  elems_ default_proposal pids.

Definition gCongressContract : G (Contract Setup Msg Congress.State) :=
  returnGen Congress.contract.
  
Sample gCongressContract.

