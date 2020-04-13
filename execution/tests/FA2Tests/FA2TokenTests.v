From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface.
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
	ChainGens TestUtils ChainPrinters SerializablePrinters TraceGens FA2Printers TestContracts.
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

(** example policies *)

(* the policy which allows only token owners to transfer their own tokens. *)
Definition policy_self_only : permissions_descriptor := {|
  descr_self := self_transfer_permitted;
  descr_operator := operator_transfer_denied;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* the policy which allows only operators to transfer tokens. *)
Definition policy_operators_only : permissions_descriptor := {|
  descr_self := self_transfer_denied;
  descr_operator := operator_transfer_permitted;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* non-transferable token (neither token owner, nor operators can transfer tokens. *)
Definition policy_no_transfers : permissions_descriptor := {|
  descr_self := self_transfer_denied;
  descr_operator := operator_transfer_denied;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

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
Definition token_contract_base_addr : Address := BoundedN.of_Z_const AddrSize 128%Z.

Definition token_client_setup := build_clientsetup token_contract_base_addr.
Definition deploy_fa2token_client : @ActionBody Base := create_deployment 0 client_contract token_client_setup.
Definition client_contract_addr : Address := BoundedN.of_Z_const AddrSize 129%Z.

Definition fa2hook_setup : HookSetup := {|
  hook_fa2_caddr_ := token_contract_base_addr;
  hook_policy_ := policy_self_only; 
|}.
Definition deploy_fa2hook := create_deployment 0 hook_contract fa2hook_setup.
Definition fa2hook_contract_addr : Address := BoundedN.of_Z_const AddrSize 130%Z.

Definition chain_with_token_deployed : LocalChain :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_fa2token;
    build_act creator deploy_fa2token_client;
    build_act creator deploy_fa2hook
  ]).

Definition client_other_msg := @other_msg _ FA2ClientMsg _.

Definition call_client_is_op_act :=
  let params := Build_is_operator_param 
      (Build_operator_param zero_address zero_address all_tokens)
      (Build_callback is_operator_response None) in 
  let msg := client_other_msg (Call_fa2_is_operator params) in
  act_call client_contract_addr 0%Z (serialize ClientMsg _ msg).

Definition chain1 : LocalChain :=
  unpack_option (my_add_block chain_with_token_deployed 
  [
    build_act person_1 (act_call token_contract_base_addr 10%Z (serialize _ _ (msg_create_tokens 0%N))) ;
    build_act person_2 (act_call token_contract_base_addr 10%Z (serialize _ _ (msg_create_tokens 0%N)))
  ]).

Definition client_state lc := 
  match (FMap.find client_contract_addr lc.(lc_contract_state)) with
  | Some state => deserialize ClientState _ state
  | None => None
  end.
Definition token_state lc := 
  match (FMap.find token_contract_base_addr lc.(lc_contract_state)) with
  | Some state => deserialize FA2Token.State _ state
  | None => None
  end.

Compute (client_state chain1).
Compute (show (token_state chain1)).

From ConCert.Execution.QCTests Require Import FA2Gens.

Module TestInfo <: FA2TestsInfo.
  Definition fa2_contract_addr := token_contract_base_addr.
  Definition fa2_client_addr := client_contract_addr.
  Definition fa2_hook_addr := fa2hook_contract_addr.
End TestInfo.
Module MG := FA2Gens.FA2Gens TestInfo. Import MG.

Definition chain1_token_state : FA2Token.State := unpack_option (token_state chain1).

(* Inductive valid_transfer : transfer -> Prop :=
| valid : forall trx, 
  (valid_transfer_prop chain1_token_state trx) = true -> valid_transfer trx.
(* Derive ArbitrarySizedSuchThat for (fun trx => valid_transfer trx). *)

Instance asd : GenSuchThat transfer valid_transfer  := {|
  arbitraryST := gValidTransfer chain1_token_state  
|}.

Sample (genST valid_transfer).
Sample (bindGenOpt (returnGen (token_state chain1)) gValidTransfer). *)
Definition gFA2ChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun lc _ => gFA2TokenAction lc) length max_acts_per_block.

Definition gFA2ClientChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun lc _ => gClientAction lc) length max_acts_per_block.

Sample (gFA2TokenAction chain1).
(* Sample gClientAction. *)
Sample (gFA2ChainTraceList 1 chain_with_token_deployed 4).
(* Sanity Check that the trace generator never fails early *)
QuickChick (forAll 
  (choose (1, 10))
  (fun size => forAll 
    (gFA2ChainTraceList 1 chain_with_token_deployed size)
    (fun trace => 
      whenFail 
        ("failed with trace of length: " ++ show (List.length trace)) 
        (size =? List.length trace))
  )).

(* Sanity check that generating two actions in a row will always succeed *)
(* QuickChick (
  forAll2 (gFA2TokenAction chain_with_token_deployed)
  (fun act_opt =>
  match act_opt with
  | Some act =>
    match (my_add_block chain_with_token_deployed [act]) with
    | Some c => gFA2TokenAction c 
    | None => returnGen None
    end
  | None => returnGen None
  end)
  (fun act1_opt act2_opt => 
    match (act1_opt, act2_opt) with
    | (Some act1, Some act2) => 
      whenFail 
        ("execution failed:" ++ nl
        ++ show (my_add_block chain_with_token_deployed [act1])) 
        (
          let c_opt := my_add_block chain_with_token_deployed [act1] in 
          match c_opt with
          | Some c => checker (isSome (my_add_block c [act2]))
          | None => whenFail "empty chain" false
          end
        )
    | _ => whenFail "empty act" false
    end) 
). *)

Sample (gFA2ClientChainTraceList 1 chain_with_token_deployed 4).







