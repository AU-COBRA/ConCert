From Stdlib Require Import ZArith.
From Stdlib Require Import List. Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.

Import DeriveSer.



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

    Definition callback_addr {A : Type}
                             (c : callback A)
                             : Address :=
      c.(return_addr A).
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

    Inductive operator_tokens :=
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

    MetaRocq Run (make_setters transfer_destination).
    MetaRocq Run (make_setters transfer).
    MetaRocq Run (make_setters balance_of_request).
    MetaRocq Run (make_setters balance_of_response).
    MetaRocq Run (make_setters balance_of_param).
    MetaRocq Run (make_setters total_supply_response).
    MetaRocq Run (make_setters total_supply_param).
    MetaRocq Run (make_setters token_metadata).
    MetaRocq Run (make_setters token_metadata_param).
    MetaRocq Run (make_setters operator_param).
    MetaRocq Run (make_setters is_operator_response).
    MetaRocq Run (make_setters is_operator_param).
    MetaRocq Run (make_setters permissions_descriptor).
    MetaRocq Run (make_setters transfer_destination_descriptor).
    MetaRocq Run (make_setters transfer_descriptor).
    MetaRocq Run (make_setters transfer_descriptor_param).
    MetaRocq Run (make_setters set_hook_param).

  End Setters.

  Section Serialization.
    Instance callback_serializable {A : Type} `{serA : Serializable A} : Serializable (callback A) := Derive Ser.

    Global Instance transfer_destination_serializable : Serializable transfer_destination := Derive Ser.

    Global Instance transfer_serializable : Serializable transfer :=  Derive Ser.

    Global Instance balance_of_request_serializable : Serializable balance_of_request := Derive Ser.

    Global Instance balance_of_response_serializable : Serializable balance_of_response := Derive Ser.

    Instance bal_of_param_callback_serializable : Serializable (callback (list balance_of_response)) := Derive Ser.

    Global Instance balance_of_param_serializable : Serializable balance_of_param := Derive Ser.

    Global Instance total_supply_response_serializable : Serializable total_supply_response := Derive Ser.

    Instance supply_param_callback_serializable : Serializable (callback (list total_supply_response)) := Derive Ser.

    Global Instance total_supply_param_serializable : Serializable total_supply_param := Derive Ser.

    Global Instance token_metadata_serializable : Serializable token_metadata := Derive Ser.

    Instance metadata_callback_serializable : Serializable (callback (list token_metadata)) := Derive Ser.

    Global Instance token_metadata_param_serializable : Serializable token_metadata_param := Derive Ser.

    Global Instance operator_tokens_serializable : Serializable operator_tokens := Derive Ser.

    Global Instance operator_param_serializable : Serializable operator_param := Derive Ser.

    Global Instance update_operator_serializable : Serializable update_operator := Derive Ser.

    Global Instance is_operator_response_serializable : Serializable is_operator_response := Derive Ser.

    Instance is_operator_param_callback_serializable : Serializable (callback is_operator_response) := Derive Ser.

    Global Instance is_operator_param_serializable : Serializable is_operator_param := Derive Ser.

    Global Instance self_transfer_policy_serializable : Serializable self_transfer_policy := Derive Ser.

    Global Instance operator_transfer_policy_serializable : Serializable operator_transfer_policy := Derive Ser.

    Global Instance owner_transfer_policy_serializable : Serializable owner_transfer_policy := Derive Ser.

    Global Instance permissions_descriptor_serializable : Serializable permissions_descriptor := Derive Ser.

    Global Instance transfer_destination_descriptor_serializable : Serializable transfer_destination_descriptor := Derive Ser.

    Global Instance transfer_descriptor_serializable : Serializable transfer_descriptor := Derive Ser.

    Global Instance transfer_descriptor_param_serializable : Serializable transfer_descriptor_param := Derive Ser.

    Global Instance fa2_token_receiver_serializable : Serializable fa2_token_receiver := Derive Ser.

    Global Instance fa2_token_sender_serializable : Serializable fa2_token_sender := Derive Ser.

    Instance transfer_descriptor_param_callback_serializable : Serializable (callback transfer_descriptor_param) := Derive Ser.

    Global Instance set_hook_param_serializable : Serializable set_hook_param := Derive Ser.

  End Serialization.
End FA2LegacyInterface.
