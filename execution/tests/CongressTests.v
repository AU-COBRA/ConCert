From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressGens CongressPrinters.

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


Definition init_is_valid p := 
  let ctx := fst p in
  let chain := (fst o snd) p in
  let setup := (snd o snd) p in
  match @Congress.init LocalChainBase chain ctx setup with
  | Some _ => checker true
  | None => false ==> true (* so we can see discards in QC output... *)
  end.

QuickChick (forAll (
  ctx <- gLocalChainContext 2 ;;
  cctx <- @gContractCallContext LocalChainBase ctx ;;
  chain <- gLocalChainSized 2 ctx ;;
  setup <- @arbitrary Setup _ ;;
  returnGen (cctx, (chain, setup)))
  init_is_valid).
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)



Definition num_cacts_in_state_deployment_P chain ctx setup :=
match init chain ctx setup with
  | Some state => checker ((Congress.num_cacts_in_state state = 0)?)
  | None => (false ==> true) (* so we can see discards in QC output... *)
  end.




(* QuickChick (
  forAll4
    (gLocalChainContext 2)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun _ _ => @arbitrary Setup _)
    (fun ctx _ _ => @gContractCallContext LocalChainBase ctx)
    (fun ctx chain setup cctx => num_cacts_in_state_deployment_P chain cctx setup)
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

(* Compute (show (sample (gLocalChainContext 2))). *)


QuickChick (
  forAll4
    (gLocalChainContext 2)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun ctx chain => @gStateSized ctx (current_slot chain) 2)
    (fun ctx _ _ => gChainActionsFromCongressActions ctx)
    (fun ctx chain state cacts => add_proposal_cacts_P cacts chain state)
).
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)
Close Scope string_scope.


Definition vote_on_proposal_cacts_preserved_P addr pid vote_val state :=
  match vote_on_proposal addr pid vote_val state with
  | Some new_state => checker (num_cacts_in_state new_state =? num_cacts_in_state state)
  | None => false ==> true
  end.

Definition check_vote_on_proposal_cacts_preserved := 
  forAll5
  (gLocalChainContext 4)
  (fun ctx => ctx_gAccountAddr ctx)
  (fun ctx _ => @gStateSized ctx 0 2)
  (fun _ _ _ => arbitrary)
  (fun _ _ state _ => gProposalIdFromState state) 
  (fun _ addr state vote_val pid => vote_on_proposal_cacts_preserved_P addr pid vote_val state).

Definition isNone {A : Type} (a : option A) := match a with | Some _ => false | None => true end.
Definition isSome {A : Type} (a : option A) := negb (isNone a).


Definition do_retract_vote_cacts_preserved_P addr pid state :=
  isSomeCheck
    (do_retract_vote addr pid state)
    (* Case where the above is 'Some new_state'  *)
    (fun new_state => num_cacts_in_state new_state =? num_cacts_in_state state).


(* TODO: look into what causes discards *)
Definition check_do_retract_vote_cacts_preserved_P :=
  forAll4
  (gLocalChainContext 4)
  (fun ctx => ctx_gAccountAddr ctx)
  (fun ctx _ => @gStateSized ctx 0 2)
  (fun _ _ state => gProposalIdFromState state) 
  (fun _ addr state pid => do_retract_vote_cacts_preserved_P addr pid state).

QuickChick check_do_retract_vote_cacts_preserved_P.
(* coqtop-stdout:+++ Passed 10000 tests (5888 discards) *)


(* Note to self: Look at implementation of 'vote_on_proposal' to get an idea of which implicit 
   requirements must met on the generated data *)
(* QuickChick (check_vote_on_proposal_cacts_preserved). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)
Open Scope bool_scope.
Definition receive_state_well_behaved_P
      chain ctx state msg :=
  match receive chain ctx state msg with
  | Some (new_state, resp_acts) => 
    let cond : bool := (isSome msg) && (num_cacts_in_state new_state + length resp_acts <=?
                                  (num_cacts_in_state state +
                                  match msg with
                                  | Some (create_proposal ls) => length ls
                                  | _ => 0
                                  end)) 
    in checker cond
  | None => false ==> true
  end.

(* fix: receive does not return Some... in most cases *)
Definition check_receive_state_well_behaved :=
  forAll5
    (gLocalChainContext 4)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun ctx chain => @gStateSized ctx (current_slot chain) 2)
    (fun ctx _ _ => @gContractCallContext LocalChainBase ctx)
    (fun ctx _ _ _ => n <- arbitrary ;; liftM Some (gMsgSized ctx n))
    (fun _ chain state cctx msg => receive_state_well_behaved_P chain cctx state msg).

QuickChick check_receive_state_well_behaved.
(* coqtop-stdout:*** Gave up! Passed only 8351 tests
Discarded: 20000 *)