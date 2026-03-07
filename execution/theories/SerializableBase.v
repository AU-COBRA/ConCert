(* This file defines a common storage format for countable types.
This format, SerializedValue, is either a unit/int/bool or a pair/list
of these. We also define Serializable as a type class capturing that a
type can be converted from and to this format. *)

From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import OptionMonad.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import BoundedN.
From Stdlib Require Import Ascii.
From Stdlib Require Import List.
From Stdlib Require Import Psatz.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.

Import ListNotations.

Inductive SerializedType :=
  | ser_unit : SerializedType
  | ser_int : SerializedType
  | ser_bool : SerializedType
  | ser_pair : SerializedType -> SerializedType -> SerializedType
  | ser_list : SerializedType -> SerializedType.

Module SerializedType.
  Scheme Equality for SerializedType.
  Definition eqb := SerializedType_beq.
  Definition eq_dec := SerializedType_eq_dec.

  Fixpoint eqb_spec (a b : SerializedType) :
    Bool.reflect (a = b) (eqb a b).
  Proof.
    destruct a, b; cbn in *; try (left; congruence); try (right; congruence).
    - destruct (eqb_spec a1 b1), (eqb_spec a2 b2);
        try (left; congruence); try (right; congruence).
    - destruct (eqb_spec a b); try (left; congruence); try (right; congruence).
  Qed.
End SerializedType.

Fixpoint interp_type (t : SerializedType) : Type :=
  match t with
  | ser_unit => unit
  | ser_int => Z
  | ser_bool => bool
  | ser_pair a b => interp_type a * interp_type b
  | ser_list a => list (interp_type a)
  end.

Set Primitive Projections.
Record SerializedValue :=
  build_ser_value {
    ser_value_type : SerializedType;
    ser_value : interp_type ser_value_type;
  }.
Unset Primitive Projections.

Definition extract_ser_value (t : SerializedType)
                             (value : SerializedValue)
                             : option (interp_type t).
Proof.
  destruct value as [ty val].
  destruct (SerializedType.eq_dec t ty).
  - subst. exact (Some val).
  - exact None.
Defined.

(* Defines that a type can be serialized into SerializedValue
   and deserialized from it, and that deserializing is a left
   inverse of serializing. *)
Class Serializable (ty : Type) :=
  build_serializable {
    serialize : ty -> SerializedValue;
    deserialize : SerializedValue -> option ty;
    deserialize_serialize x : deserialize (serialize x) = Some x;
  }.

Class SerializableComplete (ty : Type) `{Serializable ty} :=
  {
    complete e : deserialize (serialize e) = Some e;
  }.

Class SerializableSound (ty : Type) `{Serializable ty} :=
  {
    sound e a : deserialize (e) = Some a -> serialize a = e;
  }.

Global Opaque serialize deserialize deserialize_serialize complete sound.

#[export]
Instance SerializableComplete_Serializable {A} `{Serializable A} : SerializableComplete A.
Proof.
  constructor.
  destruct H as [? ? compl].
  exact compl.
Qed.

Lemma serialize_injective {T : Type} `{Serializable T} x y :
  serialize x = serialize y ->
  x = y.
Proof.
  intros eq.
  enough (Some x = Some y) by congruence.
  rewrite <- 2!deserialize_serialize.
  now rewrite eq.
Qed.
