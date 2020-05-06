From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface Dexter.
From ConCert Require Import Serializable.
From ConCert Require Import LocalBlockchainTests.
(* From Coq Require Import Morphisms. *)
From ConCert Require Import Extras.
From ConCert Require Import Containers.
From ConCert Require Import BoundedN.
Global Set Warnings "-extraction-logical-axiom".

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters SerializablePrinters TraceGens DexterPrinters.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import ZArith List.
Import ListNotations.
Import RecordSetNotations.
(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
(* Notation "f 'o' g" := (compose f g) (at level 50). *)

Module Type DexterTestsInfo.
  Parameter fa2_contract_addr : Address.
  Parameter dexter_contract_addr : Address.
  Parameter exploit_contract_addr : Address.
End DexterTestsInfo.

Module DexterGens (Info : DexterTestsInfo).
Import Info.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.
Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

Definition returnGenSome {A : Type} (a : A) := returnGen (Some a).

(* --------------------- FA2 Contract Generators --------------------- *)
Section DexterContractGens.

Definition gTokensToExchange (balance : N) : G (option N) := 
  if N.eqb 0%N balance
  then returnGen None
  else 
    amount <- choose (0%N, balance) ;;
    returnGenSome amount.

Definition gTokenExchange  (state : FA2Token.State) : G (option (Address * Dexter.Msg)):=
  let has_balance p :=
    let ledger := snd p in 
    0 <? FMap.size ledger.(balances) in
  p <-  (sampleFMapOpt_filter state.(assets) has_balance) ;;
  let tokenid := fst p in
  let ledger := snd p in
  let has_tokens p := N.ltb 0 (snd p) in
  pp <- sampleFMapOpt_filter ledger.(balances) has_tokens ;;
  let addr := fst pp in 
  let nr_tokens : N := snd pp in
  tokens_to_exchange <- gTokensToExchange nr_tokens ;;
  let exchange_msg := {|
    exchange_owner := addr;
    exchange_token_id := tokenid;
    tokens_sold := tokens_to_exchange;
    callback_addr := exploit_contract_addr;
  |} in
  returnGenSome (addr, other_msg (Dexter.tokens_to_asset exchange_msg))
.

Definition gDexterAction (lc : LocalChain) : G (option Action) :=
  let mk_call caller_addr amount msg :=
		returnGenSome {|
			act_from := caller_addr;
			act_body := act_call dexter_contract_addr amount (serialize Dexter.Msg _ msg) 
    |} in
  match FMap.find fa2_contract_addr (lc_contract_state_deserialized FA2Token.State lc) with
  | Some fa2_state => caller <- gContractAddrFromLCWithoutAddrs lc [fa2_contract_addr; dexter_contract_addr] ;;
                      p <- gTokenExchange fa2_state ;;
                      mk_call caller 0%Z (snd p) 
  | None => returnGen None
  end.

End DexterContractGens.


Definition gDexterChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun lc _ => gDexterAction lc) length max_acts_per_block.

(* the '1' fixes nr of actions per block to 1 *)
Definition token_reachableFrom (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc (gDexterChainTraceList 1) pf.

Definition token_reachableFrom_implies_reachable (lc : LocalChain) pf1 pf2 : Checker := 
  reachableFrom_implies_reachable lc (gDexterChainTraceList 1) pf1 pf2.

End DexterGens.

Module DummyTestInfo <: DexterTestsInfo.
  Definition fa2_contract_addr := zero_address.
  Definition dexter_contract_addr := zero_address.
  Definition exploit_contract_addr := zero_address.
End DummyTestInfo.
Module MG := DexterGens.DexterGens DummyTestInfo. Import MG.