From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface Dexter.
From ConCert Require Import Serializable.
From ConCert Require Import LocalBlockchainTests.
(* From Coq Require Import Morphisms. *)
From ConCert Require Import Extras.
From ConCert Require Import Containers.
From ConCert Require Import BoundedN.
Global Set Warnings "-extraction-logical-axiom".
Require Import ZArith Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters SerializablePrinters TraceGens DexterGens.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Import ListNotations.
Import RecordSetNotations.
(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
Close Scope address_scope.
(* Notation "f 'o' g" := (compose f g) (at level 50). *)

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

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
  setup_total_supply := [];
  setup_tokens := FMap.add 0%N token_metadata_0 FMap.empty; 
  initial_permission_policy := policy_all;
|}.

Definition deploy_fa2token : @ActionBody Base := create_deployment 0 FA2Token.contract token_setup.
Definition fa2_caddr : Address := BoundedN.of_Z_const AddrSize 128%Z.

Definition dexter_setup : Dexter.Setup := {|
  fa2_caddr_ := fa2_caddr;
|}.

(* The Dexter contract gets 30 chain assets initially *)
Definition deploy_dexter : @ActionBody Base := create_deployment 30 Dexter.contract dexter_setup.
Definition dexter_caddr : Address := BoundedN.of_Z_const AddrSize 129%Z.

Definition dexter_other_msg := @other_msg _ DexterMsg _.

Definition add_operator_all owner operator := {|
  op_param_owner := owner;
  op_param_operator := operator;
  op_param_tokens := all_tokens;
|}.

Definition chain1 : LocalChain :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator deploy_fa2token;
    build_act creator deploy_dexter;
    build_act person_1 (act_call fa2_caddr 10%Z (serialize _ _ (msg_create_tokens 0%N))) ;
    build_act person_2 (act_call fa2_caddr 10%Z (serialize _ _ (msg_create_tokens 0%N))) ; 
    build_act person_1 (act_call fa2_caddr 0%Z  (serialize _ _ (msg_update_operators [add_operator (add_operator_all person_1 dexter_caddr)]))) ;
    build_act person_2 (act_call fa2_caddr 0%Z  (serialize _ _ (msg_update_operators [add_operator (add_operator_all person_2 dexter_caddr)])))
  ]).

Definition dexter_state lc := 
  match (FMap.find dexter_caddr lc.(lc_contract_state)) with
  | Some state => deserialize Dexter.State _ state
  | None => None
  end.
Definition token_state lc := 
  match (FMap.find fa2_caddr lc.(lc_contract_state)) with
  | Some state => deserialize FA2Token.State _ state
  | None => None
  end.

Compute (dexter_state chain1).
Compute (show (token_state chain1)).

From ConCert.Execution.QCTests Require Import DexterGens.

Module TestInfo <: DexterTestsInfo.
  Definition fa2_contract_addr := fa2_caddr.
  Definition dexter_contract_addr := dexter_caddr.
End TestInfo.
Module MG := DexterGens.DexterGens TestInfo. Import MG.

Sample (gDexterAction chain1).
Sample (gDexterChainTraceList 1 chain1 10).