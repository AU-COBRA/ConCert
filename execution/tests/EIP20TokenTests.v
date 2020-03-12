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

From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters SerializablePrinters EIP20TokenPrinters EIP20TokenGens TraceGens.

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