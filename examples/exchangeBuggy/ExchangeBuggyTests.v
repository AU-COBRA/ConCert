From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Execution.Test Require TestUtils.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2LegacyInterface.
From ConCert.Examples.ExchangeBuggy Require Import ExchangeBuggy.
From ConCert.Examples.ExchangeBuggy Require Import ExchangeBuggyGens.
From ConCert.Examples.ExchangeBuggy Require Export ExchangeBuggyPrinters.
From ConCert.Utils Require Import Extras.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.


Definition exchange_token_id := 0%N.

Definition fa2_caddr : Address := addr_of_Z 128.
Definition exchange_caddr : Address := addr_of_Z 129.
Definition exploit_caddr : Address := addr_of_Z 130.

Section ExplotContract.
  Definition ExploitContractMsg := fa2_token_sender.
  Definition ExploitContractState := nat.
  Definition ExplotContractSetup := unit.
  Definition ExplotContractError := unit.
  Definition exploit_init
              (chain : Chain)
              (ctx : ContractCallContext)
              (setup : ExplotContractSetup)
              : result ExploitContractState ExplotContractError :=
    Ok 1.

  Definition exploit_receive
              (chain : Chain)
              (ctx : ContractCallContext)
              (state : ExploitContractState)
              (maybe_msg : option ExploitContractMsg)
              : result (ExploitContractState * list ActionBody) ExplotContractError :=
    match maybe_msg with
    | Some (tokens_sent param) =>
      if 5 <? state (* Repeat reentrancy up to five times *)
      then Ok (state, [])
      else
        let token_exchange_msg := other_msg (tokens_to_asset {|
          exchange_owner := person_1;
          ExchangeBuggy.exchange_token_id := exchange_token_id;
          tokens_sold := 200%N;
          callback_addr := ctx.(ctx_contract_address);
        |}) in
        Ok (state + 1, [act_call exchange_caddr 0 (serialize token_exchange_msg)])
    | _ => Ok (state, [])
    end.

  Definition exploit_contract : Contract ExplotContractSetup ExploitContractMsg ExploitContractState ExplotContractError :=
    build_contract exploit_init exploit_receive.

End ExplotContract.

(* The policy which allows both owners and operators to transfer tokens. *)
Definition policy_all : permissions_descriptor := {|
  descr_self := self_transfer_permitted;
  descr_operator := operator_transfer_permitted;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

Definition token_metadata_0 : token_metadata := {|
  metadata_token_id := exchange_token_id;
  metadata_decimals := 8%N;
|}.

Definition token_setup : FA2Token.Setup := {|
  transfer_hook_addr_ := None;
  setup_total_supply := [];
  setup_tokens := FMap.add exchange_token_id token_metadata_0 FMap.empty;
  initial_permission_policy := policy_all;
|}.

Definition exchange_setup : ExchangeBuggy.Setup := {|
  fa2_caddr_ := fa2_caddr;
|}.

Definition exchange_other_msg := @other_msg _ ExchangeMsg.

Definition add_operator_all owner operator := {|
  op_param_owner := owner;
  op_param_operator := operator;
  op_param_tokens := all_tokens;
|}.

(* Set up a chain with FA2 contract, exchange contract, and exploit contract deployed.
   Also adds some tokens to person_1 and exchange contract, and adds some operators on the fa2 contract *)
Definition chain : ChainBuilder :=
  unpack_result (TraceGens.add_block builder_initial
  [ (* Give 10 to person 1 *)
    TestUtils.build_transfer creator person_1 10 ;
    (* Deploy contracts *)
    build_deploy creator 0 FA2Token.contract token_setup ;
    build_deploy creator 30 ExchangeBuggy.contract exchange_setup ;
    build_deploy creator 0 exploit_contract tt ;
    (* Person 1 creates 1000 tokens in FA2 contract *)
    build_call person_1 fa2_caddr 10 (msg_create_tokens exchange_token_id) ;
    (* Exchange contract creates 1000 tokens in FA2 contract *)
    build_call creator exchange_caddr 10
      (exchange_other_msg (add_to_tokens_reserve exchange_token_id)) ;
    (* Person 1 allows Exchange and exploit contracts to operate on its tokens in the FA2 contract *)
    build_call person_1 fa2_caddr 0 (msg_update_operators
      [add_operator (add_operator_all person_1 exploit_caddr);
       add_operator (add_operator_all person_1 exchange_caddr)])
  ]).

Definition exchange_state env := get_contract_state ExchangeBuggy.State env exchange_caddr.
Definition token_state env := get_contract_state FA2Token.State env fa2_caddr.

Module TestInfo <: ExchangeTestsInfo.
  Definition fa2_contract_addr := fa2_caddr.
  Definition exchange_contract_addr := exchange_caddr.
  Definition exploit_contract_addr := exploit_caddr.
  Definition accounts := test_chain_addrs_3.
End TestInfo.
Module MG := ExchangeBuggyGens.ExchangeGens TestInfo. Import MG.

(* Helper function that generates a call to the exploit contract to
   initiate a token exchange on behalf of the caller. *)
Definition call_exchange owner_addr :=
  let dummy_descriptor := {|
    transfer_descr_fa2 := fa2_caddr;
    transfer_descr_batch := [];
    transfer_descr_operator := exchange_caddr;
  |} in
  build_call owner_addr exploit_caddr 0 (tokens_sent dummy_descriptor).

Definition gExploitAction : GOpt Action :=
  bindGen gTestAddrs3 (fun addr => returnGenSome (call_exchange addr)).

Definition gExploitChainTraceList max_acts_per_block cb length :=
  TraceGens.gChain cb (fun cb _ => gExploitAction) length 1 max_acts_per_block.

(* Sample (gExploitAction). *)
(* Sample (gExploitChainTraceList 1 chain 1). *)

Definition person_1_initial_balance : Amount := env_account_balances chain person_1.

Definition exchange_liquidity : Amount := env_account_balances chain exchange_caddr.

(* Helper function to retrieve an account's (exchange contract) token balance *)
Definition account_tokens (env : Environment) (account : Address) : N :=
  with_default 0%N (
    do state_fa2 <- token_state env ;
    do assets <- FMap.find exchange_token_id state_fa2.(assets) ;
    FMap.find account assets.(balances)).

(* Initially, the exchange contract has 1000 tokens, and so does person_1.
   The exchange contract has 30 on-chain currency, and person_1 has 0 *)
(* Compute (account_tokens chain exchange_caddr). *)
(* 1000%N *)
(* Compute (account_tokens chain person_1). *)
(* 1000%N *)
(* Compute person_1_initial_balance. *)
(* 0%Z *)
(* Compute exchange_liquidity. *)
(* 30%Z *)

(* --- PATH-DEPENDENCE ---
  This property is a consequence of the *path-dependence* property,
  and asserts that the token reserve of the exchange contract is consistent
  with how much money has been exchanged for tokens, with respect to the conversion function 'getInputPrice'.
  "Consistency" in this case means that given a sequence of trades for some account, the total tokens obtained
  by this sequence of trades should be less than if the trades were combined into a single trade, i.e.
  *splitting trades should always be more expensive*
*)
Open Scope Z_scope.
Definition tokens_to_asset_correct_P_opt (old_env new_env : Environment) : option Checker :=
  do state_exchange <- exchange_state new_env;
  let person_1_balance := env_account_balances new_env person_1 in
  let exchange_balance := env_account_balances new_env exchange_caddr in
  let exchange_initial_balance := env_account_balances old_env exchange_caddr in
  let exchange_initial_token_reserve := Z.of_N (account_tokens old_env exchange_caddr) in
  let exchange_current_token_reserve := Z.of_N (account_tokens new_env exchange_caddr) in
  (* We assume only the given account has made exchanges in this time period.
     This assumption holds for these tests. *)
  let tokens_received := exchange_current_token_reserve - exchange_initial_token_reserve in
  (* Calculate token exchange price if only a single exchange was made *)
  let expected_currency_sold := getInputPrice tokens_received exchange_initial_token_reserve exchange_initial_balance in
  let expected_exchange_balance := exchange_initial_balance - expected_currency_sold in
  Some (
    whenFail (
      "exchange balance was " ++ show exchange_balance ++
      " while it was expected to be at least " ++ show expected_exchange_balance ++ nl ++
      "person_1 balance: " ++ show person_1_balance ++ nl ++
      "person_1 tokens: " ++ show (account_tokens new_env person_1) ++ nl ++
      "exchange balance: " ++ show exchange_balance ++ nl ++
      "exchange tokens: " ++ show exchange_current_token_reserve ++ nl ++
      "history: " ++ show (state_exchange.(price_history))
    )
    (checker (expected_exchange_balance <=? exchange_balance))
  ).

Definition tokens_to_asset_correct_P old_env new_env :=
  match tokens_to_asset_correct_P_opt old_env new_env with
  | Some p => p
  | None => checker true
  end.

Definition tokens_to_asset_correct :=
  TraceGens.forAllChainStatePairs 1 chain (gExploitChainTraceList 1) tokens_to_asset_correct_P.

(* Illustration of how the reentrancy attack can give the caller more money with the same amount of tokens.
   Notice how in the second sequence, the second argument remains the same, i.e. it emulates the reentrancy attack. *)
(* Compute (getInputPrice 200 1000 30). *)
(* 4 *)
(* Compute (getInputPrice 200 1200 26). *)
(* 3 *)
(* Compute (getInputPrice 200 1400 23). *)
(* 2 *)
(* Compute (getInputPrice 200 1600 21). *)
(* 2 *)
(* Compute (getInputPrice 200 1800 19). *)
(* 1 *)
(* total = 12 *)

(* Compute (getInputPrice 200 1000 30). *)
(* 4 *)
(* Compute (getInputPrice 200 1000 26). *)
(* 4 *)
(* Compute (getInputPrice 200 1000 22). *)
(* 3 *)
(* Compute (getInputPrice 200 1000 19). *)
(* 3 *)
(* Compute (getInputPrice 200 1000 16). *)
(* 2 *)
(* total = 16 *)

(* QuickChick (expectFailure tokens_to_asset_correct). *)
(*
Begin Trace:
step_action{Action{act_from: 11%256, act_body: (act_call 130%256, 0, transferhook transfer_descriptor_param{transfer_descr_fa2: 128%256, transfer_descr_batch: [], transfer_descr_operator: 129%256})}}
End Trace
exchange balance was 14 while it was expected to be at least 16person_1 balance: 16
person_1 tokens: 0
exchange balance: 14
exchange tokens: 2000
history: [2; 3; 3; 4; 4]
*** Failed after 1 tests and 0 shrinks. (0 discards)
*)
