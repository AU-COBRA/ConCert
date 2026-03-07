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



Section Countable.
  Instance SerializedType_interp_EqDecision
           (t : SerializedType) : stdpp.base.EqDecision (interp_type t).
  Proof. induction t; typeclasses eauto. Defined.
  Instance SerializedType_interp_Countable
           (t : SerializedType) : countable.Countable (interp_type t).
  Proof. induction t; typeclasses eauto. Defined.

  Import (hints) stdpp.base.

  Global Instance SerializedValue_EqDecision : stdpp.base.EqDecision SerializedValue.
  Proof.
    intros x y.
    destruct x as [xt xv], y as [yt yv].
    destruct (SerializedType.eq_dec xt yt) as [<-|?]; [|right; congruence].
    destruct (stdpp.base.decide (xv = yv)).
    - left.
      congruence.
    - right.
      intros eq.
      inversion eq.
      congruence.
  Defined.

  Instance SerializedType_EqDecision : stdpp.base.EqDecision SerializedType.
  Proof.
    intros x y.
    destruct (SerializedType.eq_dec x y) as [<-|?]; [left|right]; easy.
  Defined.
  Fixpoint depth st : nat :=
    match st with
    | ser_unit => 1
    | ser_int => 1
    | ser_bool => 1
    | ser_pair x y => S (max (depth x) (depth y))
    | ser_list x => S (depth x)
    end.
  Local Open Scope positive.
  Fixpoint encode_st_body (st : SerializedType) : positive :=
    match st with
    | ser_unit => countable.encode (1, 1)
    | ser_int => countable.encode (2, 1)
    | ser_bool => countable.encode (3, 1)
    | ser_pair x y =>
        countable.encode (4, countable.encode (encode_st_body x, encode_st_body y))
    | ser_list x => countable.encode (5, encode_st_body x)
    end.
  Definition encode_st (st : SerializedType) : positive :=
    countable.encode (depth st, encode_st_body st).

  Fixpoint decode_st_body (depth : nat) (p : positive) : option SerializedType :=
    match depth with
    | 0%nat => None
    | S depth =>
      do '(tag, body) <- countable.decode p;
      match tag with
      | 1 => ret ser_unit
      | 2 => ret ser_int
      | 3 => ret ser_bool
      | 4 => do '(x, y) <- countable.decode body;
             do x <- decode_st_body depth x;
             do y <- decode_st_body depth y;
             ret (ser_pair x y)
      | 5 => do x <- decode_st_body depth body;
             ret (ser_list x)
      | _ => None
      end
    end.
  Definition decode_st (p : positive) : option SerializedType :=
    do '(depth, body) <- countable.decode p;
    decode_st_body depth body.

  Local Open Scope nat.
  Lemma decode_st_body_encode_st_body (d : nat) (st : SerializedType) :
    depth st <= d ->
    decode_st_body d (encode_st_body st) = Some st.
  Proof.
    revert st.
    induction d; intros st dle; cbn in *.
    - exfalso.
      induction st; cbn in *; lia.
    - destruct st; auto; cbn in *.
      + now rewrite !countable.decode_encode, !IHd by lia.
      + now rewrite !countable.decode_encode, !IHd by lia.
  Qed.

  Lemma decode_st_encode_st (st : SerializedType) :
    decode_st (encode_st st) = Some st.
  Proof.
    unfold decode_st, encode_st.
    rewrite countable.decode_encode; cbn.
    now apply decode_st_body_encode_st_body.
  Qed.

  Local Open Scope positive.
  Instance SerializedType_Countable : countable.Countable SerializedType :=
    {| countable.encode := encode_st;
       countable.decode := decode_st;
       countable.decode_encode := decode_st_encode_st |}.

  Definition encode_sv (sv : SerializedValue) : positive :=
    countable.encode (ser_value_type sv, countable.encode (ser_value sv)).

  Definition decode_sv (p : positive) : option SerializedValue :=
    do '(ty, p) <- countable.decode p;
    do v <- countable.decode p;
    ret {| ser_value_type := ty; ser_value := v |}.

  Lemma decode_sv_encode_sv (sv : SerializedValue) :
    decode_sv (encode_sv sv) = Some sv.
  Proof.
    unfold decode_sv, encode_sv.
    rewrite countable.decode_encode; cbn.
    rewrite countable.decode_encode; cbn.
    reflexivity.
  Qed.

  Global Instance SerializedValue_Countable : countable.Countable SerializedValue :=
    {| countable.encode := encode_sv;
       countable.decode := decode_sv;
       countable.decode_encode := decode_sv_encode_sv |}.

  (* Low priority to always pick 'direct' EqDecision instances first *)
  Global Instance SerializableType_EqDecision
         (A : Type) `{Serializable A} : stdpp.base.EqDecision A | 1000.
  Proof.
    intros a a'.
    destruct (stdpp.base.decide (serialize a = serialize a')) as [eq|neq].
    - left.
      now apply serialize_injective.
    - right.
      intros ->.
      congruence.
  Defined.

  Definition encode_serializable_type {A : Type} `{Serializable A} (a : A) : positive :=
    countable.encode (serialize a).

  Definition decode_serializable_type {A : Type}
                                      `{Serializable A}
                                      (p : positive)
                                      : option A :=
    countable.decode p >>= deserialize.

  Lemma decode_serializable_type_encode_serializable_type
        {A : Type} `{Serializable A}
        (a : A) :
    decode_serializable_type (encode_serializable_type a) = Some a.
  Proof.
    unfold decode_serializable_type, encode_serializable_type.
    rewrite countable.decode_encode.
    cbn.
    now rewrite deserialize_serialize.
  Qed.

  (* Low priority to always pick 'direct' Countable instances first *)
  Global Instance SerializableType_Countable {A : Type} `{Serializable A} :
    countable.Countable A | 1000 :=
    {| countable.encode := encode_serializable_type;
       countable.decode := decode_serializable_type;
       countable.decode_encode := decode_serializable_type_encode_serializable_type; |}.
End Countable.
