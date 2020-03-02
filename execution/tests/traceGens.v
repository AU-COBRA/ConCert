Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.

From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters CongressGens.


(* For monad notations *)
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

From Coq Require Import List.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import MSets.MSetGenTree.
From Coq Require Import Permutation.

Import BoundedN.Stdpp.

Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.



Global Arguments ChainState _ : clear implicits.
Global Arguments Chain _ : clear implicits.
Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

(* 
  The ChainTrace datatype is defined as a ChainedList of ChainStates and ChainSteps.
  The ChainStep is an inductive relation with constructors 'step_block', 'step_action', and 'step_permute'.
  Each constructor is guarded with a number of propositions, requiring various validity conditions.
  
  This makes it hard to construct a generator for the ChainTrace type, so instead we initially construct a simpler model
  for chain traces, which is essentially just a list of chain states.
  But since we are working in the context of black-box testing, this may even be a better approach than trying to implement
  generators for the ChainTrace type, since we don't want to ensure/require that certain conditions hold, we only want
  to generate data from the given functions, and see what result we get. 
*)

Sample (
  ctx <- (gLocalChainContext 4) ;;
  c <- gLocalChainSized 8 ctx ;;
  header <- gLocalBCBlockHeaderSizedFromChainAndContext 2 c ctx ;;
  actions <- listOf (gCongressActionSizedFromLC lc_initial 0) ;;
  returnGen actions
  (* returnGen (add_block_exec true lc_initial header actions) *)
).

Sample (
  ctx <- (gLocalChainContext 4) ;;
  c <- gLocalChainSized 8 ctx ;;
  header <- gLocalBCBlockHeaderSizedFromChainAndContext 16 c ctx ;;
  lc_init <- gInitialLocalChain ;;
  actions <- listOf (gActionOfCongress ctx 10) ;;
  returnGen (add_block_exec true lc_init header actions)
).

Open Scope list_scope.
Extract Constant defNumTests => "100".
QuickChick (forAll5 
  (gLocalChainContext 4)
  (fun ctx => gLocalChainSized 8 ctx) 
  (fun ctx c => gLocalBCBlockHeaderSizedFromChainAndContext 16 c ctx)
  (fun ctx c header => gInitialLocalChain)
  (fun ctx c header lc_init => listOf (gActionOfCongress ctx 10))
  (fun ctx c header lc_init actions =>
  isSome (add_block_exec true lc_init header actions)
  )).

Inductive SimpleChainStep (prev_bstate : ChainState) :=
| step_block :
    forall (header : BlockHeader)
    ChainStep (add_new_block_to_env header prev_bstate) ->
| step_action :
    forall (act : Action)
           (acts : list Action)
           (new_acts : list Action),
      chain_state_queue prev_bstate = act :: acts ->
      ActionEvaluation prev_bstate act next_bstate new_acts ->
      chain_state_queue next_bstate = new_acts ++ acts ->
      let new_queue := act :: acts in
      let new_env := 
      ChainStep prev_bstate
| step_permute :
      chain_state_env prev_bstate = chain_state_env next_bstate ->
      Permutation (chain_state_queue prev_bstate) (chain_state_queue next_bstate) ->
      ChainStep prev_bstate next_bstate.


Definition SimpleChainTrace {BaseTypes : ChainBase}: Type := list (@ChainState BaseTypes).

Definition gNextChainState (current_state : ChainState) : G ChainState := 
  elems
.


Fixpoint GSimpleChainTraceSized (n : nat) : G SimpleChainTrace :=
  returnGen match n with
  | 0 => []
  | 1 => [empty_state]
  | S n' => 

  end.

(* Inductive SimpleChainStep (prev_bstate : ChainState) (next_bstate : ChainState) :=
  | sstep_block :
  | sstep_action :
  | sstep_permute :
.

Inductive SimpleChainTrace (init_state : ChainState) ():= *)
