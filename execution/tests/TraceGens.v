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

Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
Require Import Extras.

From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters CongressGens.

(* For monad notations *)
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

From Coq Require Import List Int BinInt FunInd.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import MSets.MSetGenTree.
From Coq Require Import Permutation.

Import BoundedN.Stdpp.

Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.
Definition AddrSize := (2^8)%N.

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.
Definition Base : ChainBase := LocalBlockchainTests.Base.
Definition c_init : ChainBuilder := builder_initial.


Definition deploy_congress : @ActionBody Base := create_deployment 5 Congress.contract setup.
(* Definition chain4 : ChainBuilder :=
  unpack_option (add_block chain3 [build_act person_1 deploy_congress]). *)
(* Compute (show chain4). *)
(* Sample (gCongressActionSizedFromLC chain1.(builder_env) 4). *)
Definition next_header (chain : ChainBuilder) :=
    {| block_height := S (chain_height chain);
       block_slot := S (current_slot chain);
       block_finalized_height := finalized_height chain;
       block_creator := creator;
       block_reward := 50; |}.

Definition next_header_lc (chain : @LocalChain AddrSize) :=
    {| block_height := S (chain_height chain);
       block_slot := S (current_slot chain);
       block_finalized_height := finalized_height chain;
       block_creator := creator;
       block_reward := 50; |}.

Definition optToVector {A : Type} (n : nat): (G (option A)) -> G (list A) :=
  fun g =>
  l <- vectorOf n g ;;
  let l' := fold_left (fun acc aopt => match aopt with
                          | Some a => a :: acc
                          | None => acc
                          end) l []
  in returnGen l'.



Sample (gCongressActionSizedFromLC (lcb_lc chain4) zero_address 0).

(* does not compute because computing the normal form of the entire chain is too complex. 
   Instead compute a projection of the chain, like the state *)
(* Compute (lcb_lc chain4). *)
(* Compute (add_block_exec true (lcb_lc chain4) (next_header chain4) []). *)

Definition c1 := unpack_option (add_block_exec true lc_initial (next_header_lc lc_initial) []).
Compute (show c1).
Definition c2 := unpack_option 
                  (add_block_exec true 
                    c1 
                      (next_header_lc c1) 
                    [build_act creator (act_transfer person_1 10)]).
Definition c3 :=  unpack_option (add_block_exec true c2 (next_header_lc c2) [build_act person_1 deploy_congress]).
Compute (show c3).

Definition my_add_block c acts := (add_block_exec true c (next_header_lc c) acts).

QuickChick (forAll 
  (optToVector 10 (gActionOfCongressFromLC c1 3))
  (fun actions => isSome (my_add_block c1 actions))).
(* woop woop - it works!:
    coqtop-stdout:+++ Passed 10000 tests (0 discards)
*)

Open Scope bool_scope.
Definition add_block_actions_succeeds_P c_opt actions_opt :=
  isSomeCheck c_opt
  (fun c => 
    whenFail (show (lc_account_balances c)) 
      (match actions_opt with
      | Some actions => (0 <? length actions) && isSome (my_add_block c actions)
      | None => false
      end)
  ).

Definition check_add_two_blocks_succeeds := 
  (forAll3 
    (optToVector 3 (gActionOfCongressFromLC c1 2))
    (fun actions => returnGen (my_add_block c1 actions))
    (fun _ c_opt => 
      match c_opt with
      | Some c => acts <- (optToVector 3 (gActionOfCongressFromLC c 2)) ;; returnGen (Some acts) 
      | None => returnGen None
      end)
    (fun _ c_opt actions_opt => add_block_actions_succeeds_P c_opt actions_opt)
  ).


Section Trees.
  Variable V : Type.
  Variable default: V.
  Definition key := N.
  Inductive tree : Type :=
   | leaf : tree
   | node : V -> tree -> tree -> tree.
  Definition empty_tree : tree := leaf.
End Trees.

Inductive LocalChainStep {AddrSize : N} : Type :=
| step_add_block : forall (prev_chain : @LocalChain AddrSize) 
                          (header : BlockHeader) 
                          (next_chain : @LocalChain AddrSize), LocalChainStep
| step_action : forall (prev_chain : @LocalChain AddrSize) 
                       (header : BlockHeader) 
                       (next_chain : @LocalChain AddrSize) 
                       (acts : list Action), LocalChainStep.

Definition mk_basic_step_add_block c : option (LocalChain * LocalChainStep) := 
  let header := (next_header_lc c) in
  let c_next_opt := add_block_exec false c header [] in
  match c_next_opt with
  | None => None
  | Some c_next => Some (c_next, step_add_block c header c_next)
  end.

Definition mk_basic_step_action c acts : option (LocalChain * LocalChainStep) := 
  let header := (next_header_lc c) in
  let c_next_opt := add_block_exec false c header acts in
  match c_next_opt with
  | Some c_next => Some (c_next, step_action c header c_next acts)
  | None => None
  end.

Arguments leaf {V}.
Arguments node {V} _ _ _.
(* Example t : tree LocalChainStep := node (mk_basic_step_add_block lc_initial) 
              (node (mk_basic_step_action c1 []) leaf leaf)
              leaf. *)

Open Scope string_scope.
Instance showLocalChainStep : Show LocalChainStep :=
{|
  show step := match step with
  | step_add_block prev header next => 
    "step_add_block{ prev_lc: " ++ show prev ++ sep ++ "header: " ++ show header ++ sep ++ "next_lc:" ++ show next ++ "}"  
  | step_action prev header next acts =>
    "step_action{ prev_lc: " ++ show prev ++ sep ++ "header: " ++ show header ++ sep ++ "next_lc:" ++ show next ++ sep ++ "acts: " ++ show acts ++ "}"
  end
|}.

Instance showLocalChainStepWithOnlyName {AddrSize : N} : Show (@LocalChainStep AddrSize) :=
{|
  show step := match step with
  | step_add_block prev header next => 
    "step_add_block"  
  | step_action prev header next acts =>
    "step_action"
  end
|}.

Definition lctracetree := tree (@LocalChainStep AddrSize).

Instance showTree {A} `{_ : Show A} : Show (tree A) :=
  {| show t := let fix aux (indent : string) t :=
       match t with
         | leaf => "Leaf"
         | node x l r =>
                      "(Node" ++ nl 
                      ++ indent ++ "(" ++ show x ++ ")" ++ nl
                      ++ indent ++ aux (indent ++ "  ") l ++ nl 
                      ++ indent ++  aux (indent ++ "  ") r ++ ")"
       end
     in nl ++ "Tree:" ++ nl ++ (aux "  " t)
  |}.

Instance showLctracetree : Show lctracetree :=
{|
  show t := @show _ (@showTree _ showLocalChainStep) t 
|}.

Fixpoint glctracetree_fix (prev_lc : LocalChain) (height : nat) : G lctracetree :=
  match height with
  | 0 | 1 => returnGen leaf
  | S height => 
    lc_opt <- freq [
      (1, liftM (mk_basic_step_action prev_lc) (optToVector 2 (gActionOfCongressFromLC prev_lc 2))) ;
      (1, returnGen (mk_basic_step_add_block prev_lc)) 
      ] ;;
    match lc_opt with
          | Some (lc, step) => liftM2 (node step) (glctracetree_fix lc height) (glctracetree_fix lc height) 
          | None => returnGen leaf
         end
  end.

Definition glctracetree (height : nat) := glctracetree_fix lc_initial height.

Sample (glctracetree 3).

Definition prev_lc_of_lcstep (state : @LocalChainStep AddrSize) :=
  match state with
  | step_add_block prev _ _ => prev
  | step_action prev _ _ _ => prev
  end.

Definition next_lc_of_lcstep (state : @LocalChainStep AddrSize) : LocalChain :=
  match state with
  | step_add_block _ _ next => next
  | step_action _ _ next _ => next
  end.
Close Scope string_scope.
Definition lc_shallow_eqb lc1 lc2 : bool := 
  (lc_height lc1 =? lc_height lc2) 
  && (lc_slot lc1 =? lc_slot lc2) 
  && (@lc_fin_height AddrSize lc1 =? @lc_fin_height AddrSize lc2).

Fixpoint next_lc_eq_child_prev_lc_P (t : lctracetree) := 
  match t with
  | leaf => true
  | node step (node step_lchild lcl lcr) (node step_rchild rcl rcr) =>
    (lc_shallow_eqb (next_lc_of_lcstep step) (prev_lc_of_lcstep step_lchild))
    && (lc_shallow_eqb (next_lc_of_lcstep step) (prev_lc_of_lcstep step_rchild))
  | _ => true 
  end.

(* QuickChick (forAll (glctracetree 4) next_lc_eq_child_prev_lc_P). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)