From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.iTokenBuggy Require Import iTokenBuggy.
From ConCert.Examples.iTokenBuggy Require Import iTokenBuggyPrinters.
From ConCert.Examples.iTokenBuggy Require Import iTokenBuggyGens.
From Coq Require Import ZArith.
From Coq Require Import List. 
Import ListNotations.


(* -------------------------- Tests of the Buggy iToken Implementation -------------------------- *)

(* F# style piping notation *)
Notation "f <| x" := (f x) (at level 91, left associativity, only parsing).
(* i.e. f <| x <| y = (f <| x) <| y, and means (f x) y *)
Notation "x |> f" := (f x) (at level 31, left associativity, only parsing).
(* i.e. x |> f |> g = (x |> f) |> g, and means g (f x) *)

Definition token_setup := iTokenBuggy.build_setup creator (100%N).
Definition token_caddr := addr_of_Z 128.

(* In the initial chain we transfer some assets to a few accounts, just to make the addresses
   present in the chain state. The amount transferred is irrelevant. *)
Definition token_cb :=
  ResultMonad.unpack_result (TraceGens.add_block empty_chain
  [
    build_transfer creator person_1 0;
    build_transfer creator person_2 0;
    build_transfer creator person_3 0;
    build_deploy creator 0 iTokenBuggy.contract token_setup
  ]).

Module TestInfo <: iTokenBuggyGensInfo.
  Definition contract_addr := token_caddr.
  Definition gAccount := gTestAddrs3.
End TestInfo.
Module MG := iTokenBuggyGens TestInfo. Import MG.

Module NotationInfo <: TestNotationParameters.
  Definition gAction := giTokenBuggyAction.
  Definition init_cb := token_cb.
End NotationInfo.
Module TN := TestNotations NotationInfo. Import TN.
(* Sample gChain. *)

Definition checker_get_state {prop} `{Checkable prop} (pf : State -> prop) (cs : ChainState) : Checker := 
  match get_contract_state iTokenBuggy.State cs token_caddr with
  | Some state => checker (pf state)
  | None => checker true (* trivially true case *) 
  end.

(* bool variant of checker_get_state *)
Definition get_state (pf : State -> bool) (cs : ChainState) : bool := 
  match get_contract_state iTokenBuggy.State cs token_caddr with
  | Some state => pf state
  | None => true (* trivially true case *) 
  end.

Open Scope N_scope.
Open Scope string_scope.
(* One key property: the sum of the balances is always equal to the initial supply *)
Definition sum_balances_eq_init_supply_checker (state : iTokenBuggy.State) :=
  let balances_list := state.(balances) |> FMap.elements |> map snd in
  let balances_sum : N := fold_left N.add balances_list 0%N in
  whenFail
    <| "balances_sum: " ++ show balances_sum ++ nl ++
       "total_supply: " ++ show state.(total_supply) ++ nl ++
       "balances: " ++ show state.(balances)
    <| N.eqb balances_sum state.(total_supply).
  
Close Scope string_scope.

Definition sum_balances_eq_init_supply (state : iTokenBuggy.State) : bool :=
  let balances_sum := state.(balances) |> FMap.elements
                                       |> map snd 
                                       |> fold_right N.add 0 in
  balances_sum =? state.(total_supply).

Instance genBuggyTokenChainSized : GenSized ChainBuilder := {
  arbitrarySized n := gChain_ token_cb n
}.

Conjecture token_supply_preserved : forall sig_to : {to | reachable to}, 
  let to := proj1_sig sig_to in
  get_state sum_balances_eq_init_supply to = true.

(* QuickChick (expectFailure token_supply_preserved). *)
(* Or alternatively, for better output: *)
(* QuickChick (expectFailure (forAllBlocks (checker_get_state sum_balances_eq_init_supply_checker))). *)
(* *** Failed (as expected) after 5 tests and 1000 shrinks. (0 discards) *)
(* Action{act_from: 11%256, act_body: (act_call 128%256, 0, withdraw)}}
balances_sum: 12
total_supply: 10
balances: [11%256-->1; 13%256-->2; 10%256-->9] *)

Definition msg_is_not_mint_or_burn (state : iTokenBuggy.State) (msg : iTokenBuggy.Msg) :=
  match msg with
  | mint _ | burn _ => false
  | _ => true
  end.

Definition sum_balances_unchanged (chain : Chain)
                                  (cctx : ContractCallContext)
                                  (old_state : State)
                                  (msg : Msg)
                                  (result_opt : option (State * list ActionBody))
                                  : Checker :=
  (* sum all entries in the balances field of a given iToken contract state *)
  let balances_sum s := s.(balances) |> FMap.elements 
                                     |> map snd
                                     |> fold_right N.add 0%N in
  match result_opt with
  | Some (new_state, _) => checker <| balances_sum old_state =? balances_sum new_state 
  | None => false ==> true
  end.

(*
QuickChick (expectFailure (
                {{msg_is_not_mint_or_burn}}
                  token_caddr
                  {{sum_balances_unchanged}}
           )).
*)
(* *** Failed (as expected) after 1 tests and 0 shrinks. (0 discards)
       On Msg: transfer_from 13%256 13%256 1 *)
