
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Monad.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Dexter Require Import Dexter.
From ConCert.Examples.Dexter Require Export DexterPrinters.
From ConCert.Examples.Dexter Require Import DexterGens.
From ConCert.Examples.EIP20 Require Import EIP20Token.
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.


Definition token_pool_size : N := 100.

Definition token_setup : EIP20Token.Setup := {|
  EIP20Token.owner := creator;
  EIP20Token.init_amount := token_pool_size;
|}.

Definition token_caddr : Address := addr_of_Z 128.
Definition dexter_caddr : Address := addr_of_Z 129.

(* Dexter will have 60 tokens in reverse initially *)
Definition dexter_setup : Dexter.Setup := {|
  token_caddr_ := token_caddr;
  token_pool_ := (token_pool_size - 40);
|}.

Definition add_as_operator_act owner operator tokens :=
  build_call owner token_caddr 0 (EIP20Token.approve operator tokens).

Definition exchange_tokens_to_money_act owner amount :=
  build_call owner dexter_caddr 0 (Dexter.tokens_to_asset {|
    exchange_owner := owner;
    tokens_sold := amount;
  |}).

(* Set up a chain with token contract, and dexter contract deployed.
   Also adds some tokens to person_1 and dexter contract, and adds some operators on the fa2 contract *)
Definition chain : ChainBuilder :=
  unpack_result (TraceGens.add_block builder_initial
  [ (* Give 10 to person 1 *)
    build_transfer creator person_1 10 ;
    (* Deploy contracts *)
    build_deploy creator 0 EIP20Token.contract token_setup ;
    build_deploy creator 30 Dexter.contract dexter_setup ;
    (* Tranfer tokens to exchange contract and person1 *)
    build_call creator token_caddr 0 (EIP20Token.transfer person_1 40%N) ;
    build_call creator token_caddr 0 (EIP20Token.transfer dexter_caddr (token_pool_size - 40)%N) ;
    (* Let dexter transfer tokens on behalf of person_1 and person_2 *)
    add_as_operator_act person_1 dexter_caddr token_pool_size ;
    add_as_operator_act person_2 dexter_caddr token_pool_size
  ]).

Definition add_block_with_acts (c : ChainBuilder) acts :=
  (TraceGens.add_block c acts).

Definition dexter_state env := get_contract_state Dexter.State env dexter_caddr.
Definition token_state env := get_contract_state EIP20Token.State env token_caddr.

Module TestInfo <: DexterTestsInfo.
  Definition token_caddr := token_caddr.
  Definition dexter_contract_addr := dexter_caddr.
  Definition test_accounts := [person_1].
End TestInfo.
Module MG := DexterGens.DexterGens TestInfo. Import MG.

(* Sample (gDexterAction chain1). *)

(* Sample ((liftM (fun a => add_block_with_acts chain1 [a]) (gDexterAction chain1))). *)
(* Sample (gDexterChain 2 chain1 1). *)

Definition person_1_initial_balance : Amount := env_account_balances chain person_1.

Definition dexter_liquidity chain : Amount := env_account_balances chain dexter_caddr.

Definition account_tokens (env : Environment) (account : Address) : N :=
  with_default 0%N (
    do token_state <- token_state env ;
    FMap.find account token_state.(EIP20Token.balances)
    ).

Definition dexter_token_pool (env : Environment) : N :=
  with_default 0%N (
    do s <- dexter_state env ;
    Some s.(token_pool)
    ).

Open Scope Z_scope.
Coercion Z.of_N : N >-> Z.

(* Asserts that exchanges are priced correctly *)
Definition tokens_to_asset_correct_P_opt (old_env new_env : Environment) : option Checker :=
  do state_dexter <- dexter_state new_env;
  let person_1_balance := env_account_balances new_env person_1 in
  let dexter_balance := env_account_balances new_env dexter_caddr in
  let dexter_initial_balance := env_account_balances old_env dexter_caddr in
  let dexter_initial_token_reserve := account_tokens old_env dexter_caddr in
  let dexter_current_token_reserve := account_tokens new_env dexter_caddr in
  (* We assume only the given account has made exchanges in this time period.
     This assumption holds for these tests. *)
  let tokens_received := dexter_current_token_reserve - dexter_initial_token_reserve in
  (* Calculate token exchange price if only a single exchange was made *)
  let expected_currency_sold := getInputPrice tokens_received dexter_initial_token_reserve dexter_initial_balance in
  let expected_dexter_balance := dexter_initial_balance - expected_currency_sold in
  Some (
    whenFail (
      "dexter balance was " ++ show dexter_balance ++
      " while it was expected to be at least " ++ show expected_dexter_balance ++ nl ++
      "person_1 balance: " ++ show person_1_balance ++ nl ++
      "person_1 tokens: " ++ show (account_tokens new_env person_1) ++ nl ++
      "dexter balance: " ++ show dexter_balance ++ nl ++
      "dexter tokens: " ++ show dexter_current_token_reserve ++ nl ++
      "history: " ++ show (state_dexter.(price_history))
    )
    (checker (expected_dexter_balance <=? dexter_balance))
  ).

Definition tokens_to_asset_correct_P old_env env :=
  match tokens_to_asset_correct_P_opt old_env env with
  | Some p => p
  | None => checker true
  end.

Definition tokens_to_asset_correct :=
  forAllChainStatePairs 1 chain (gDexterChain 2) tokens_to_asset_correct_P.

(* We first test the Dexter contract with breadth-first execution model *)
(* QuickChick (tokens_to_asset_correct). *)
(* +++ Passed 10000 tests (0 discards) *)
(* We see that the property holds with breadth-first execution model *)

(* However, the Dexter contract was designed for Tezos which used
   breadth-first execution model.
   Thus, we next test the property with that model *)
(* Extract Constant DepthFirst => "false".
QuickChick (tokens_to_asset_correct). *)
(*
Chain{|
Block 1 [
Action{act_from: 10%256, act_body: (act_deploy 0, DexterSetup{token_caddr_: 10%256, token_pool_: 100})};
Action{act_from: 10%256, act_body: (act_deploy 30, DexterSetup{token_caddr_: 128%256, token_pool_: 60})};
Action{act_from: 10%256, act_body: (act_call 128%256, 0, DexterSetup{token_caddr_: 11%256, token_pool_: 40})};
Action{act_from: 10%256, act_body: (act_call 128%256, 0, DexterSetup{token_caddr_: 129%256, token_pool_: 60})};
Action{act_from: 11%256, act_body: (act_call 128%256, 0, approve 129%256 100)}];
Block 2 [
Action{act_from: 11%256, act_body: (act_call 129%256, 0, token_to_asset exchange{exchange_owner: 11%256, tokens_sold: 20})};
Action{act_from: 11%256, act_body: (act_call 129%256, 0, token_to_asset exchange{exchange_owner: 11%256, tokens_sold: 14})}]; |}

dexter balance was 19 while it was expected to be at least 20
person_1 balance: 11
person_1 tokens: 6
dexter balance: 19
dexter tokens: 94
history: [7; 4]
*** Failed after 23 tests and 2 shrinks. (0 discards)
*)

(* We can see that the property fails in breadth-first model when two trades are made
   in the same block. Below we simulate what goes wrong in this example.
   The starting configuration is
   person_1 balance: 10
   person_1 tokens: 40
   dexter balance: 30
   dexter tokens: 60
*)
(* Compute (env_account_balances chain person_1). *)
(* = 10 : N *)
(* Compute (account_tokens chain person_1). *)
(* = 40 : N *)
(* Compute (env_account_balances chain dexter_caddr). *)
(* = 30 : N *)
(* Compute (account_tokens chain dexter_caddr). *)
(* = 60 : N *)

(* If both trades were merged person_1 would get 10 tez for his 34 tokens *)
(* Compute (getInputPrice 34 60 30). *)
(* = 10 : Z *)

(* However, this is not what happens, in total person_1 gains 7+4=11 tez from
   trading 34 tokens (20 in the first trade, 14 in the second) *)
(* In the first trade person_1 trades 20 tokens for 7 tez *)
(* Compute (getInputPrice 20 60 30). *)
(* = 7 : Z *)
(* In the second trade we would expect person_1 to get 3 tez for his 14 tokens *)
(* Compute (getInputPrice 14 80 23). *)
(* = 3 : Z *)
(* However, this is not the calculation that is being done.
   Instead the contract computes the yield of the second trade as follows *)
(* Compute (getInputPrice 14 80 30). *)
(* = 4 : Z *)
(* This is because in breadth first execution model both trades gets started before tokens and tez
   from previous trades have been transferred. Thus trades uses wrong values.
   Dexter manually tracks and decrements the number of tokens in the reserve because of this.
   However, the contract doesn't manually track tez the same way, thus the tez amount used is wrong. *)
