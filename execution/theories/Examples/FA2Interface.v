From Coq Require Import ZArith.
From Coq Require Import List String.
Require Import Serializable.
Require Import Blockchain.

Import ListNotations.
Require Import Extras.
Require Import Containers.
From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Section FA2Types.
Context {BaseTypes : ChainBase}.

Definition token_id := N.

Record transfer := {
  from_ : Address;
  to_ : Address;
  transfer_token_id : token_id;
  amount : N;
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
  bal_callback : (list balance_of_response); (*TODO : what type here? *)
}.

Record total_supply_response := {
  supply_resp_token_id : token_id;
  total_supply : N;
}.

Record total_supply_param := {
  supply_param_token_ids : list token_id;
  supply_param_callback : (list total_supply_response); (*TODO : what type here? *)
}.

Record token_metadata := {
  metadata_token_id : token_id;
  metadata_symbol : string;
  metadata_name : string;
  metadata_decimals : N;
  metadata_extras : FMap string string;
}.

Record token_metadata_param := {
  metadata_token_ids : list token_id;
  metadata_callback : (list token_metadata); (*TODO : what type here? *)
}.

Inductive operator_tokens :=
  | All_tokens : operator_tokens
  | Some_tokens : list token_id -> operator_tokens (* TODO: maybe set instead of list?*) .

Record operator_param := {
  op_param_owner : Address;
  op_param_operator : Address;
  op_param_tokens : operator_tokens;
}.

Inductive update_operator :=
  | Add_operator : operator_param -> update_operator
  | Remove_operator : operator_param -> update_operator.

Record is_operator_response := {
  operator : operator_param;
  is_operator : bool;
}.

Record is_operator_param := {
  is_operator_operator : operator_param;
  is_operator_callback : (is_operator_response); (* TODO *)
}.

(* permission policy definition *)

Inductive self_transfer_policy :=
  | Self_transfer_permitted : self_transfer_policy
  | Self_transfer_denied : self_transfer_policy.

Inductive operator_transfer_policy :=
  | Operator_transfer_permitted : operator_transfer_policy
  | Operator_transfer_denied : operator_transfer_policy.

Inductive owner_transfer_policy :=
  | Owner_no_op : owner_transfer_policy
  | Optional_owner_hook : owner_transfer_policy
  | Required_owner_hook : owner_transfer_policy.

Record custom_permission_policy := {
  custom_policy_tag : string;
  custom_policy_config_api: option Address;
}.

Record permissions_descriptor := {
  descr_self : self_transfer_policy;
  descr_operator : operator_transfer_policy;
  descr_receiver : owner_transfer_policy;
  descr_sender : owner_transfer_policy;
  descr_custom : option custom_permission_policy;
}.

Inductive fa2_entry_points :=
  | Transfer : list transfer -> fa2_entry_points
  | Balance_of : balance_of_param -> fa2_entry_points
  | Total_supply : total_supply_param -> fa2_entry_points
  | Token_metadata : token_metadata_param -> fa2_entry_points
  | Permissions_descriptor : permissions_descriptor -> fa2_entry_points (* TODO fix callback type *)
  | Update_operators : list update_operator -> fa2_entry_points
  | Is_operator : is_operator_param -> fa2_entry_points.

Record transfer_descriptor := {
  transfer_descr_from_ : option Address;
  transfer_descr_to_ : option Address;
  transfer_descr_token_id : token_id;
  transfer_descr_amount : N;
}.

Record transfer_descriptor_param := {
  tramsfer_descr_fa2 : Address;
  tramsfer_descr_batch : list transfer_descriptor;
  tramsfer_descr_operator : Address;
}.

Inductive fa2_token_receiver :=
  | Tokens_received : transfer_descriptor_param -> fa2_token_receiver.

Inductive fa2_token_sender :=
  | Tokens_sent : transfer_descriptor_param -> fa2_token_sender.

End FA2Types.