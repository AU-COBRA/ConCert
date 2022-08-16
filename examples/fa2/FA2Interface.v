From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import String.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Containers.

Import ListNotations.


Section FA2Interface.
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

Record token_metadata := {
  metadata_token_id : token_id;
  metadata_token_info : FMap string N
}.

Record operator_param := {
  op_param_owner : Address;
  op_param_operator : Address;
  op_param_token_id : token_id;
}.

Inductive update_operator :=
  | add_operator : operator_param -> update_operator
  | remove_operator : operator_param -> update_operator.

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

End FA2Types.

Section Setters.

MetaCoq Run (make_setters transfer_destination).
MetaCoq Run (make_setters transfer).
MetaCoq Run (make_setters balance_of_request).
MetaCoq Run (make_setters balance_of_response).
MetaCoq Run (make_setters balance_of_param).
MetaCoq Run (make_setters token_metadata).
MetaCoq Run (make_setters operator_param).
MetaCoq Run (make_setters transfer_destination_descriptor).
MetaCoq Run (make_setters transfer_descriptor).
MetaCoq Run (make_setters transfer_descriptor_param).

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

Global Instance token_metadata_serializable : Serializable token_metadata :=
  Derive Serializable token_metadata_rect <Build_token_metadata>.

Instance metadata_callback_serializable : Serializable (callback (list token_metadata)) :=
  Derive Serializable (callback_rect (list token_metadata)) <(Build_callback (list token_metadata))>.

Global Instance operator_param_serializable : Serializable operator_param :=
  Derive Serializable operator_param_rect <Build_operator_param>.

Global Instance update_operator_serializable : Serializable update_operator :=
  Derive Serializable update_operator_rect <add_operator, remove_operator>.

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

End Serialization.

End FA2Interface.
