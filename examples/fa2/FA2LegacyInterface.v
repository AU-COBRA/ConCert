From Coq Require Import ZArith.
From Coq Require Import List.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.


Section FA2LegacyInterface.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Section FA2Types.

Definition token_id := N.

(* Dummy implementation of callbacks. *)
Record callback (A : Type) := {
  blob : option A;
  return_addr : Address;
}.

Definition callback_addr {A : Type} (c : callback A) : Address := c.(return_addr A).
Global Coercion callback_addr : callback >-> Address.

Record transfer_destination := 
  build_transfer_destination {
    to_ : Address;
    dst_token_id : N;
    amount : N;
}.

Record transfer := 
  build_transfer {
    from_ : Address;
    txs : list transfer_destination;
    sender_callback_addr : option Address
}.

Record balance_of_request := {
  owner : Address;
  bal_req_token_id : token_id;
}.

Record balance_of_response := {
  request : balance_of_request;
  balance : N;
}.

Record balance_of_param := {
  bal_requests : list balance_of_request;
  bal_callback : callback (list balance_of_response);
}.

Record total_supply_response := {
  supply_resp_token_id : token_id;
  total_supply : N;
}.

Record total_supply_param := {
  supply_param_token_ids : list token_id;
  supply_param_callback : callback (list total_supply_response);
}.

Record token_metadata := {
  metadata_token_id : token_id;
  metadata_decimals : N;
}.

Record token_metadata_param := {
  metadata_token_ids : list token_id;
  metadata_callback : callback (list token_metadata);
}.

Inductive operator_tokens  :=
  | all_tokens : operator_tokens
  | some_tokens : list token_id -> operator_tokens. (* a set could be used here instead of list?*)

Record operator_param := {
  op_param_owner : Address;
  op_param_operator : Address;
  op_param_tokens : operator_tokens;
}.

Inductive update_operator :=
  | add_operator : operator_param -> update_operator
  | remove_operator : operator_param -> update_operator.

Record is_operator_response := {
  operator : operator_param;
  is_operator : bool;
}.

Record is_operator_param := {
  is_operator_operator : operator_param;
  is_operator_callback : callback (is_operator_response);
}.

(* permission policy definition *)

Inductive self_transfer_policy :=
  | self_transfer_permitted : self_transfer_policy
  | self_transfer_denied : self_transfer_policy.

Inductive operator_transfer_policy :=
  | operator_transfer_permitted : operator_transfer_policy
  | operator_transfer_denied : operator_transfer_policy.

Inductive owner_transfer_policy :=
  | owner_no_op : owner_transfer_policy
  | optional_owner_hook : owner_transfer_policy
  | required_owner_hook : owner_transfer_policy.

Record permissions_descriptor := {
  descr_self : self_transfer_policy;
  descr_operator : operator_transfer_policy;
  descr_receiver : owner_transfer_policy;
  descr_sender : owner_transfer_policy;
  descr_custom : option Address;
}.

Record transfer_destination_descriptor := {
  transfer_dst_descr_to_ : option Address;
  transfer_dst_descr_token_id : token_id;
  transfer_dst_descr_amount : N  
}.

Record transfer_descriptor := {
  transfer_descr_from_ : option Address;
  transfer_descr_txs : list transfer_destination_descriptor
}.

Record transfer_descriptor_param := {
  transfer_descr_fa2 : Address;
  transfer_descr_batch : list transfer_descriptor;
  transfer_descr_operator : Address;
}.

Inductive fa2_token_receiver :=
  | tokens_received : transfer_descriptor_param -> fa2_token_receiver.

Inductive fa2_token_sender :=
  | tokens_sent : transfer_descriptor_param -> fa2_token_sender.

Record set_hook_param := {
  hook_addr : Address;
  hook_permissions_descriptor : permissions_descriptor;
}.

End FA2Types.

Section Setters.

MetaCoq Run (make_setters transfer_destination).
MetaCoq Run (make_setters transfer).
MetaCoq Run (make_setters balance_of_request).
MetaCoq Run (make_setters balance_of_response).
MetaCoq Run (make_setters balance_of_param).
MetaCoq Run (make_setters total_supply_response).
MetaCoq Run (make_setters total_supply_param).
MetaCoq Run (make_setters token_metadata).
MetaCoq Run (make_setters token_metadata_param).
MetaCoq Run (make_setters operator_param).
MetaCoq Run (make_setters is_operator_response).
MetaCoq Run (make_setters is_operator_param).
MetaCoq Run (make_setters permissions_descriptor).
MetaCoq Run (make_setters transfer_destination_descriptor).
MetaCoq Run (make_setters transfer_descriptor).
MetaCoq Run (make_setters transfer_descriptor_param).
MetaCoq Run (make_setters set_hook_param).

End Setters.

Section Serialization.
Instance callback_serializable {A : Type} `{serA : Serializable A} : Serializable (callback A) :=
Derive Serializable (callback_rect A) <(Build_callback A)>.

Global Instance transfer_destination_serializable : Serializable transfer_destination :=
  Derive Serializable transfer_destination_rect<build_transfer_destination>.

Global Instance transfer_serializable : Serializable transfer :=
  Derive Serializable transfer_rect <build_transfer>.

Global Instance balance_of_request_serializable : Serializable balance_of_request :=
  Derive Serializable balance_of_request_rect <Build_balance_of_request>.

Global Instance balance_of_response_serializable : Serializable balance_of_response :=
  Derive Serializable balance_of_response_rect <Build_balance_of_response>.

Instance bal_of_param_callback_serializable : Serializable (callback (list balance_of_response)) :=
  Derive Serializable (callback_rect (list balance_of_response)) <(Build_callback (list balance_of_response))>.

Global Instance balance_of_param_serializable : Serializable balance_of_param :=
  Derive Serializable balance_of_param_rect <Build_balance_of_param>.

Global Instance total_supply_response_serializable : Serializable total_supply_response :=
  Derive Serializable total_supply_response_rect <Build_total_supply_response>.

Instance supply_param_callback_serializable : Serializable (callback (list total_supply_response)) :=
  Derive Serializable (callback_rect (list total_supply_response)) <(Build_callback (list total_supply_response))>.

Global Instance total_supply_param_serializable : Serializable total_supply_param :=
  Derive Serializable total_supply_param_rect <Build_total_supply_param>.

Global Instance token_metadata_serializable : Serializable token_metadata :=
  Derive Serializable token_metadata_rect <Build_token_metadata>.

Instance metadata_callback_serializable : Serializable (callback (list token_metadata)) :=
  Derive Serializable (callback_rect (list token_metadata)) <(Build_callback (list token_metadata))>.

Global Instance token_metadata_param_serializable : Serializable token_metadata_param :=
  Derive Serializable token_metadata_param_rect <Build_token_metadata_param>.

Global Instance operator_tokens_serializable : Serializable operator_tokens :=
  Derive Serializable operator_tokens_rect <all_tokens, some_tokens>.

Global Instance operator_param_serializable : Serializable operator_param :=
  Derive Serializable operator_param_rect <Build_operator_param>.

Global Instance update_operator_serializable : Serializable update_operator :=
  Derive Serializable update_operator_rect <add_operator, remove_operator>.

Global Instance is_operator_response_serializable : Serializable is_operator_response :=
  Derive Serializable is_operator_response_rect <Build_is_operator_response>.

Instance is_operator_param_callback_serializable : Serializable (callback is_operator_response) :=
  Derive Serializable (callback_rect is_operator_response) <(Build_callback is_operator_response)>.

Global Instance is_operator_param_serializable : Serializable is_operator_param :=
  Derive Serializable is_operator_param_rect <Build_is_operator_param>.

Global Instance self_transfer_policy_serializable : Serializable self_transfer_policy :=
  Derive Serializable self_transfer_policy_rect <self_transfer_permitted, self_transfer_denied>.

Global Instance operator_transfer_policy_serializable : Serializable operator_transfer_policy :=
  Derive Serializable operator_transfer_policy_rect <operator_transfer_permitted, operator_transfer_denied>.

Global Instance owner_transfer_policy_serializable : Serializable owner_transfer_policy :=
  Derive Serializable owner_transfer_policy_rect <owner_no_op , optional_owner_hook, required_owner_hook>.

Global Instance permissions_descriptor_serializable : Serializable permissions_descriptor :=
  Derive Serializable permissions_descriptor_rect <Build_permissions_descriptor>.

Global Instance transfer_destination_descriptor_serializable : Serializable transfer_destination_descriptor :=
Derive Serializable transfer_destination_descriptor_rect <Build_transfer_destination_descriptor>.

Global Instance transfer_descriptor_serializable : Serializable transfer_descriptor :=
  Derive Serializable transfer_descriptor_rect <Build_transfer_descriptor>.

Global Instance transfer_descriptor_param_serializable : Serializable transfer_descriptor_param :=
  Derive Serializable transfer_descriptor_param_rect <Build_transfer_descriptor_param>.

Global Instance fa2_token_receiver_serializable : Serializable fa2_token_receiver :=
  Derive Serializable fa2_token_receiver_rect <tokens_received>.

Global Instance fa2_token_sender_serializable : Serializable fa2_token_sender :=
  Derive Serializable fa2_token_sender_rect <tokens_sent>.

Instance transfer_descriptor_param_callback_serializable : Serializable (callback transfer_descriptor_param) :=
  Derive Serializable (callback_rect transfer_descriptor_param) <(Build_callback transfer_descriptor_param)>.

Global Instance set_hook_param_serializable : Serializable set_hook_param :=
  Derive Serializable set_hook_param_rect <Build_set_hook_param>.

End Serialization.

End FA2LegacyInterface.
