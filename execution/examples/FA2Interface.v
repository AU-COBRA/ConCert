From Coq Require Import ZArith.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Require Import Monads.

Import ListNotations.
Require Import Extras.
Require Import Containers.
From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Section FA2Interface.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Section FA2Types.

Definition token_id := N.

(* Definition callback (A : Type) := A -> ActionBody.  *)

Record callback (A : Type) := {
  (* callback_addr : Address; *)
  blob : option A;
}.

Record transfer :=
  build_transfer {
    from_ : Address;
    to_ : Address;
    transfer_token_id : token_id;
    amount : N;
    sender_callback_addr : option Address;
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
  bal_callback : callback (list balance_of_response); (* TODO : what type here? *)
}.

Record total_supply_response := {
  supply_resp_token_id : token_id;
  total_supply : N;
}.

Record total_supply_param := {
  supply_param_token_ids : list token_id;
  supply_param_callback : callback (list total_supply_response); (*TODO : what type here? *)
}.

Record token_metadata := {
  metadata_token_id : token_id;
  (* metadata_symbol : string; *)
  (* metadata_name : string; *)
  metadata_decimals : N;
  (* metadata_extras : FMap string string; *)
}.

Record token_metadata_param := {
  metadata_token_ids : list token_id;
  metadata_callback : callback (list token_metadata); (*TODO : what type here? *)
}.

Inductive operator_tokens  :=
  | all_tokens : operator_tokens
  | some_tokens : list token_id -> operator_tokens (* TODO: maybe set instead of list?*) .

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
  is_operator_callback : callback (is_operator_response); (* TODO *)
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
  
(* Inlined the address instead *)
(* Record custom_permission_policy := {
  (* custom_policy_tag : string; *)
  custom_policy_config_api: option Address;
}. *)

Record permissions_descriptor := {
  descr_self : self_transfer_policy;
  descr_operator : operator_transfer_policy;
  descr_receiver : owner_transfer_policy;
  descr_sender : owner_transfer_policy;
  descr_custom : option Address;
}.

(* Inductive fa2_entry_points :=
  | Transfer : list transfer -> fa2_entry_points
  | Balance_of : balance_of_param -> fa2_entry_points
  | Total_supply : total_supply_param -> fa2_entry_points
  | Token_metadata : token_metadata_param -> fa2_entry_points
  | Permissions_descriptor : permissions_descriptor -> fa2_entry_points (* TODO fix callback type *)
  | Update_operators : list update_operator -> fa2_entry_points
  | Is_operator : is_operator_param -> fa2_entry_points. *)

Record transfer_descriptor := {
  transfer_descr_from_ : Address;
  transfer_descr_to_ : Address;
  transfer_descr_token_id : token_id;
  transfer_descr_amount : N;
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

(* Instance callback_settable {A : Type} : Settable (callback A) :=
  settable! (Build_callback A) <(callback_addr A); (body A)>. *)
  
Instance transfer_settable : Settable transfer :=
  settable! build_transfer <from_; to_; transfer_token_id; amount; sender_callback_addr>.

Instance balance_of_request_settable : Settable balance_of_request :=
  settable! Build_balance_of_request <owner; bal_req_token_id>.

Instance balance_of_response_settable : Settable balance_of_response :=
  settable! Build_balance_of_response <request; balance>.

Instance balance_of_param_settable : Settable balance_of_param :=
  settable! Build_balance_of_param <bal_requests; bal_callback>.

Instance total_supply_reponse_settable : Settable total_supply_response :=
  settable! Build_total_supply_response <supply_resp_token_id; total_supply>.

Instance total_supply_param_settable : Settable total_supply_param :=
  settable! Build_total_supply_param <supply_param_token_ids; supply_param_callback>.

Instance token_metadata_settable : Settable token_metadata :=
  settable! Build_token_metadata <  metadata_token_id; metadata_decimals>.

Instance token_metadata_param_settable : Settable token_metadata_param :=
  settable! Build_token_metadata_param <  metadata_token_ids; metadata_callback>.

Instance operator_param_settable : Settable operator_param :=
  settable! Build_operator_param <op_param_owner; op_param_operator; op_param_tokens>.

Instance is_operator_response_settable : Settable is_operator_response :=
  settable! Build_is_operator_response <operator; is_operator>.

Instance is_operator_param_settable : Settable is_operator_param :=
  settable! Build_is_operator_param <is_operator_operator; is_operator_callback>.

(* Instance custom_permission_policy_settable : Settable custom_permission_policy :=
  settable! Build_custom_permission_policy <custom_policy_config_api>. *)

Instance permissions_descriptor_settable : Settable permissions_descriptor :=
  settable! Build_permissions_descriptor <descr_self; descr_operator; descr_receiver; descr_sender; descr_custom>.

Instance transfer_descriptor_settable : Settable transfer_descriptor :=
  settable! Build_transfer_descriptor <
    transfer_descr_from_;
    transfer_descr_to_;
    transfer_descr_token_id;
    transfer_descr_amount>.

Instance transfer_descriptor_param_settable : Settable transfer_descriptor_param :=
  settable! Build_transfer_descriptor_param <transfer_descr_fa2; transfer_descr_batch; transfer_descr_operator>.

Instance set_hook_param_settable : Settable set_hook_param :=
  settable! Build_set_hook_param <hook_addr; hook_permissions_descriptor>.

End Setters.

Section Serialization.
Instance callback_serializable {A : Type} `{serA : Serializable A} : Serializable (callback A) :=
Derive Serializable (callback_rect A) <(Build_callback A)>.

(* Global Program Instance callback_serializable {A : Type} : Serializable (callback A) :=
  {| serialize c := @serialize unit _ tt;
     deserialize p := 
     do tt <- @deserialize unit _ p ;
     Some (Build_callback A)
  |}.
Next Obligation.
intros.
cbn.
rewrite deserialize_serialize. 
destruct x.
reflexivity. 
Qed. *)


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

End FA2Interface.