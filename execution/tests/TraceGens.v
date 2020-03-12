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

Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import Containers.
From ConCert Require Import EIP20Token.
Require Import Extras.

From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters CongressGens SerializablePrinters EIP20TokenPrinters EIP20TokenGens.

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



Definition c1 := unpack_option (add_block_exec true lc_initial (next_header_lc lc_initial) []).
Compute (show c1).
Definition c2 := unpack_option 
                  (add_block_exec true 
                    c1 
                      (next_header_lc c1) 
                    [build_act creator (act_transfer person_1 10)]).
Definition c3 :=  unpack_option (add_block_exec true c2 (next_header_lc c2) [build_act person_1 deploy_congress]).
Compute (show (lc_account_balances c1)).
Compute (show (lc_account_balances c2)).
Compute (show (lc_account_balances c3)).
Compute (show (map fst (FMap.elements (lc_contracts c3)))).
Compute (show (lc_contract_owners c3)).
Compute (show (lc_contract_state c3)).

Definition my_add_block c acts := (add_block_exec true c (next_header_lc c) acts).

Open Scope bool_scope.


Section Trees.
  Variable V : Type.
  Variable default: V.
  Definition key := N.
  Inductive tree : Type :=
   | leaf : tree
   | node : V -> tree -> tree -> tree.
  Definition empty_tree : tree := leaf.
End Trees.
Arguments leaf {V}.
Arguments node {V} _ _ _.

Fixpoint allPaths_fix {V : Type} (t : tree V) (acc : list (list V)) : list (list V) :=
let call_rec n v := match acc with
  | [] => allPaths_fix n [[v]]
  | _ => allPaths_fix n (map (fun l => l ++ [v]) acc) 
  end in
match t with
| leaf => acc
| node v 
       (node _ _ _ as l) 
       leaf => call_rec l v
| node v 
       leaf 
       (node _ _ _ as r) => call_rec r v
| node v 
       (node _ _ _ as l) 
       (node _ _ _ as r) => call_rec l v ++ call_rec r v
| node v leaf leaf => (map (fun l => l ++ [v]) acc) 
end.

Definition allPaths {V : Type} (t : tree V) : list (list V):= allPaths_fix t [[]].

Example ex_tree : tree nat := node 1 (node 2 leaf leaf) (node 3 (node 4 leaf leaf) (node 5 leaf leaf)).
(* Compute (show (allPaths ex_tree)). *)

Derive Arbitrary for tree.

Open Scope string_scope.

Instance showTree {A} `{_ : Show A} : Show (tree A) :=
  {| show t := let fix aux (indent : string) t :=
       match t with
         | leaf => "leaf"
         | node x l r =>
                      "(node" ++ nl 
                      ++ indent ++ "(" ++ show x ++ ")" ++ nl
                      ++ indent ++ aux (indent ++ "  ") l ++ nl 
                      ++ indent ++  aux (indent ++ "  ") r ++ ")"
       end
     in nl ++ "Begin Tree:" ++ nl ++ (aux "  " t) ++ nl ++ "End Tree."
  |}.
Close Scope string_scope.

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

(* Example t : tree LocalChainStep := node (mk_basic_step_add_block lc_initial) 
              (node (mk_basic_step_action c1 []) leaf leaf)
              leaf. *)
Open Scope string_scope.
Instance showLocalChainStepVerbose : Show LocalChainStep :=
{|
  show step := match step with
  | step_add_block prev header next => 
    "step_add_block{ prev_lc: " ++ show prev ++ sep ++ "header: " ++ show header ++ sep ++ "next_lc:" ++ show next ++ "}"  
  | step_action prev header next acts =>
    "step_action{ prev_lc: " ++ show prev ++ sep ++ "header: " ++ show header ++ sep ++ "next_lc:" ++ show next ++ sep ++ "acts: " ++ show acts ++ "}"
  end
|}.

Instance showLocalChainStep {AddrSize : N} : Show (@LocalChainStep AddrSize) :=
{|
  show step := match step with
  | step_add_block prev header next => 
    "step_add_block{ ... }"  
  | step_action prev header next acts =>
    "step_action{" ++ show acts ++ "}"
  end
|}.

(* Instance showLocalChainStepWithOnlyName {AddrSize : N} : Show (@LocalChainStep AddrSize) :=
{|
  show step := match step with
  | step_add_block prev header next => 
    "step_add_block"  
  | step_action prev header next acts =>
    "step_action"
  end
|}. *)

Definition lctracetree := tree (@LocalChainStep AddrSize).

Instance showLctracetree : Show lctracetree :=
{|
  show t := @show _ (@showTree _ showLocalChainStep) t 
|}.


Fixpoint glctracetree_fix (prev_lc : LocalChain)
                          (gActOptFromLCSized : LocalChain -> nat -> G (option Action))
                          (height : nat) : G lctracetree :=
  match height with
  | 0 | 1 => returnGen leaf
  | S height => 
    lc_opt <- backtrack [
      (10, 
          (* acts <- liftM (shrinkListTo 2) (optToVector 5 (gActOptFromLCSized prev_lc 2)) ;; *)
          bindGenOpt (gActOptFromLCSized prev_lc 2)
          (fun act => returnGen (mk_basic_step_action prev_lc [act]))
      )
          (* match acts with
          | [] => returnGen None
          | _ => returnGen (mk_basic_step_action prev_lc acts)
          end) *)
      (* (1, returnGen (mk_basic_step_add_block prev_lc)) ; *)
      (* (3, liftM (mk_basic_step_action prev_lc ) (optToVector 1 (gDeployCongressActionFromLC prev_lc)))  *)
      ] ;;
    match lc_opt with
          | Some (lc, step) => 
            liftM2 (node step) 
                   (glctracetree_fix lc gActOptFromLCSized height) 
                   (glctracetree_fix lc gActOptFromLCSized height) 
          | None => returnGen leaf
    end
  end.



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

(* QuickChick (forAll (glctracetree 7) next_lc_eq_child_prev_lc_P). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)


Fixpoint gLocalChainTraceList_fix (prev_lc : LocalChain)
                              (gActOptFromLCSized : LocalChain -> nat -> G (option Action))
                              (length : nat) : G (list LocalChainStep) :=
  match length with
  | 0 => returnGen []
  | S length => 
    lc_opt <- backtrack [
      (10, 
          (* What we're essentially doing here trying twice and then discarding one - to increase robustness.  *)
          let gAct_try_twice := backtrack [
            (1, (gActOptFromLCSized prev_lc 2));
            (1, (gActOptFromLCSized prev_lc 2))
          ] in
          bindGenOpt gAct_try_twice (fun act => returnGen (mk_basic_step_action prev_lc [act]))
          (* acts <- liftM (shrinkListTo 1) (optToVector nr_retries ) ;; *)
          (* returnGen (mk_basic_step_action prev_lc acts) *)
          (* bindGenOpt (gActOptFromLCSized prev_lc 2) *)
          (* (fun act => returnGen (mk_basic_step_action prev_lc [act])) *)
      )
          (* match acts with
          | [] => returnGen None
          | _ => returnGen (mk_basic_step_action prev_lc acts)
          end) *)
      (* (1, returnGen (mk_basic_step_add_block prev_lc)) ; *)
      (* (3, liftM (mk_basic_step_action prev_lc ) (optToVector 1 (gDeployCongressActionFromLC prev_lc)))  *)
      ] ;;
    match lc_opt with
          | Some (lc, step) => 
            liftM (cons step) 
                   (gLocalChainTraceList_fix lc gActOptFromLCSized length) 
          | None => returnGen []
    end
  end.

Open Scope string_scope.
Instance showLocalChainList {AddrSize : N}: Show (list (@LocalChainStep AddrSize)) :=
{|
  show l := nl ++ "Begin Trace: " ++ nl ++ String.concat (";;" ++ nl) (map show l) ++ nl ++ "End Trace"
|}.
Close Scope string_scope.  

Fixpoint all_suffices_fix {A : Type} (l : list A) (acc : list (list A)) : list (list A) := 
  match l with
  | [] => acc
  | x::xs => match acc with
             | [] => all_suffices_fix xs [[x]]
             | _ => all_suffices_fix xs ([x] :: (map (fun l => app l [x]) acc)) 
             end
  end.

(* TODO: pretty ugly solution. Maybe fix. *)
Definition all_prefixes {A : Type} (l : list A) := map (fun l => rev' l) (all_suffices_fix (rev' l) []).
Compute (all_prefixes [1;2;3;4]).

Instance shrinkLocalChainTraceList {AddrSize : N}: Shrink (list (@LocalChainStep AddrSize)) :=
{|
  shrink := all_prefixes
|}.

(* Checks that a property holds on all states in all traces from a given trace generator *)
Definition forAllTraces {prop : Type}
                       `{Checkable prop}
                        {AddrSize : N}
                        (maxLength : nat)
                        (init_lc : @LocalChain AddrSize)
                        (gTrace : LocalChain -> nat -> G (list LocalChainStep))
                        (pf : LocalChain -> prop)
                        : Checker :=
  forAllShrink (gTrace init_lc maxLength) shrink
  (fun trace => conjoin (map (checker o pf o next_lc_of_lcstep) trace))
.


Definition reachableFromSized {AddrSize : N}
                         (maxLength : nat) 
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : LocalChain -> nat -> G (list LocalChainStep))
                         (pf : LocalChain -> bool)
                         : Checker := 
  existsPShrink (gTrace init_lc maxLength) (fun trace => existsb pf (map (next_lc_of_lcstep) trace)).

Definition reachableFrom {AddrSize : N} init_lc gTrace pf : Checker := 
  sized (fun n => @reachableFromSized AddrSize n init_lc gTrace pf).

(* represents: if there is a state x, satisfying pf1, reachable from init_lc,
               then there is a state y, satisfyring pf2, reachable from state x. *)
(* TODO: currently "shrink" kinda saves us from a bug, which is that we only do existsb on the
   outermost call, whereas it should be the last element satisfying pf1. *)
Definition reachableFrom_implies_reachableSized
                         (maxLength : nat) 
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                         (pf1 : LocalChain -> bool)
                         (pf2 : LocalChain -> bool)
                         : Checker := 
  expectFailure (forAllShrink (gTrace init_lc maxLength) shrink 
    (fun trace =>
      if (existsb pf1 (map next_lc_of_lcstep trace))
      then let new_init_lc : LocalChain := (List.last (map next_lc_of_lcstep trace) init_lc) in 
        expectFailure (forAllShrink (gTrace new_init_lc maxLength) shrink
        (fun new_trace => whenFail ("Success - found witness satisfying the predicate!" )
          ((checker o negb) (existsb pf2 (map (next_lc_of_lcstep) new_trace)))
        )
      )
      else checker true
    )).

Definition reachableFrom_implies_reachable init_lc gTrace pf1 pf2 := 
  sized (fun n => reachableFrom_implies_reachableSized n init_lc gTrace pf1 pf2).


(* -------------------------- Tests of the EIP20 Token Implementation -------------------------- *)

Definition token_setup := EIP20Token.build_setup creator 100.
Definition deploy_eip20token : @ActionBody Base := create_deployment 0 EIP20Token.contract token_setup.

Let contract_base_addr := BoundedN.of_Z_const AddrSize 128%Z.

Definition chain_with_token_deployed :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_eip20token
  ]).

Definition gEIP20TokenChainTraceList lc length := 
  gLocalChainTraceList_fix lc (fun lc _ => 
    gEIP20TokenAction lc contract_base_addr) length.


Definition token_reachableFrom (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc gEIP20TokenChainTraceList pf.

Definition token_reachableFrom_implies_reachable (lc : LocalChain) pf1 pf2 : Checker := 
  reachableFrom_implies_reachable lc gEIP20TokenChainTraceList pf1 pf2.

Compute (show (map fst (FMap.elements (lc_contracts chain_with_token_deployed)))).
Compute (show (lc_token_contracts_states_deserialized chain_with_token_deployed)).
Compute (show (lc_account_balances chain_with_token_deployed)).
(* Sample (gEIP20TokenChainTraceList chain_with_token_deployed 10). *)
Open Scope string_scope.
Definition debug_gEIP20Checker lc (act : option Action) :=
  let print_valid_actions := match act with
                            | Some act => "valid actions: " ++ show (validate_actions [act]) ++ sep ++ nl
                            | None => ""
                            end in
  whenFail 
    ("lc balances: " ++ show (lc_account_balances lc) ++ sep ++ nl
    ++ print_valid_actions
    ++ "token state: " ++ show (lc_token_contracts_states_deserialized lc) ++ sep ++ nl 
    ).


(* QuickChick (forAll 
  (gEIP20TokenAction chain_with_token_deployed contract_base_addr) 
  (fun act_opt => isSomeCheck act_opt (fun act => 
    (isSomeCheck (my_add_block chain_with_token_deployed [act]) (fun _ => checker true))
  ))). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

(* Sample (gEIP20TokenAction chain_with_token_deployed contract_base_addr). *)
Sample (gEIP20TokenChainTraceList chain_with_token_deployed 10).
(* QuickChick (forAll 
  (gEIP20TokenAction chain_with_token_deployed contract_base_addr) 
  (fun act_opt => isSomeCheck act_opt (fun act => 
    (debug_gEIP20Checker chain_with_token_deployed (Some act))  
      ((checker o isSome) (my_add_block chain_with_token_deployed [act]))))). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition last_state trace := List.last (map next_lc_of_lcstep trace) chain_with_token_deployed.


(* Generate a trace, and then execute an action on the last state of the trace. Check that this always succeeds *)
(* QuickChick (forAll2 
  (gEIP20TokenChainTraceList chain_with_token_deployed 5) 
  (fun trace => 
    gEIP20TokenAction (last_state trace) 
                      contract_base_addr)
  (fun trace act_opt => isSomeCheck act_opt (fun act => 
    (debug_gEIP20Checker (last_state trace) (Some act))  
      ((checker o isSome) (my_add_block (last_state trace) [act]))))). *)


Open Scope nat_scope.
(* One key property: the sum of the balances is always equal to the initial supply *)
Definition sum_balances_eq_init_supply_P maxLength := 
  forAllTraces maxLength chain_with_token_deployed gEIP20TokenChainTraceList
    (fun (lc : LocalChain) =>
      debug_gEIP20Checker lc None
      (checker match FMap.find contract_base_addr (lc_token_contracts_states_deserialized lc) with
      | Some state => 
        let balances_list := (map snd o FMap.elements) state.(balances) in
        let balances_sum : nat := fold_left plus balances_list 0 in
        balances_sum =? state.(total_supply)
      | None => false
      end)).

(* QuickChick (sum_balances_eq_init_supply_P 7). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

(* INVALID PROPERTY: accounts may allow multiple other accounts to transfer tokens, but the actual transfer ensures that
   no more tokens are sent than the balance of the sender. *)
Definition sum_allowances_le_init_supply_P maxLength :=
  forAllTraces maxLength chain_with_token_deployed gEIP20TokenChainTraceList
    (fun (lc : LocalChain) =>
      debug_gEIP20Checker lc None
      (checker match FMap.find contract_base_addr (lc_token_contracts_states_deserialized lc) with
      | Some state => 
        let allowances := map_values_FMap 
          (fun allowance_map => fold_left plus ((map snd o FMap.elements) allowance_map) 0)
          state.(allowances) in
        let allowances_list := (map snd o FMap.elements) allowances in
        let allowances_sum := fold_left plus allowances_list 0 in 
        allowances_sum <=? state.(total_supply)
      | None => false
      end)).
    
(* QuickChick (sum_allowances_le_init_supply_P 5). *)

Definition person_has_tokens person (n : nat) := 
  fun lc =>
    match FMap.find contract_base_addr (lc_token_contracts_states_deserialized lc) with
    | Some state => n =? (FMap_find_ person state.(balances) 0)  
    | None => false
    end.

Notation "lc '~~>' pf" :=
  (token_reachableFrom lc pf)
  (at level 45, no associativity).



(* QuickChick (chain_with_token_deployed ~~> person_has_tokens person_3 12). *)
(* QuickChick (chain_with_token_deployed ~~> person_has_tokens creator 0). *)

QuickChick (token_reachableFrom_implies_reachable 
  chain_with_token_deployed
  (person_has_tokens creator 10)
  (person_has_tokens creator 0)        
).

(* Notation "lc '~~>' pf1 '~~>' pf2" :=
  (token_reachableFrom_implies_reachable lc pf1 pf2)   
  (at level 99).
QuickChick (chain_with_token_deployed ~~> person_has_tokens creator 0 ~~> person_has_tokens creator 10 ). *)