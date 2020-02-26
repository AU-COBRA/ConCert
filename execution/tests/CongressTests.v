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

(* ChainGens for the types defined in the Congress contract *)

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

(* ChainGens *)




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

(* Compute (show (sample (gLocalChainContext 2))). *)

Definition test1 := forAll (gLocalChainContext 1).

QuickChick (
  forAll4
    (gLocalChainContext 2)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun ctx _ => @gStateSized ctx 2)
    (fun ctx _ _ => gChainActionsFromCongressActions ctx)
    (fun ctx chain state cacts => add_proposal_cacts_P cacts chain state)
).
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)
Close Scope string_scope.

