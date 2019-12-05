(* This file defines a common storage format for countable types.
This format, SerializedValue, is either a unit/int/bool or a pair/list
of these. We also define Serializable as a type class capturing that a
type can be converted from and to this format. *)

From Coq Require Import ZArith.
Require Import Monads.
Require Import Containers.
Require Import Automation.
Require Import BoundedN.
From Coq Require Import List.

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

Definition extract_ser_value (t : SerializedType) (value : SerializedValue) : option (interp_type t).
Proof.
  destruct value as [ty val].
  destruct (SerializedType.eq_dec t ty).
  - subst. exact (Some val).
  - exact None.
Defined.

(* Defines that a type can be serialized into SerializedValue and deserialized from it,
   and that deserializing is a left inverse of serialziing. *)
Class Serializable (ty : Type) :=
  build_serializable {
    serialize : ty -> SerializedValue;
    deserialize : SerializedValue -> option ty;
    deserialize_serialize x : deserialize (serialize x) = Some x;
  }.

Global Opaque serialize deserialize deserialize_serialize.

Lemma serialize_injective {T : Type} `{Serializable T} x y :
  serialize x = serialize y ->
  x = y.
Proof.
  intros eq.
  enough (Some x = Some y) by congruence.
  rewrite <- 2!deserialize_serialize.
  now rewrite eq.
Qed.

Program Instance unit_serializable : Serializable unit :=
  {| serialize u := build_ser_value ser_unit u;
     deserialize := extract_ser_value ser_unit; |}.
Solve Obligations with reflexivity.

Program Instance int_serializable : Serializable Z :=
  {| serialize i := build_ser_value ser_int i;
     deserialize := extract_ser_value ser_int; |}.
Solve Obligations with reflexivity.

Program Instance bool_serializable : Serializable bool :=
  {| serialize b := build_ser_value ser_bool b;
     deserialize := extract_ser_value ser_bool; |}.
Solve Obligations with reflexivity.

Program Instance nat_serializable : Serializable nat :=
  {| serialize n := serialize (Z.of_nat n);
     deserialize z := do z' <- deserialize z; Some (Z.to_nat z'); |}.
Next Obligation.
  intros x.
  cbn.
  rewrite deserialize_serialize.
  cbn.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Program Instance ser_positive_equivalence : Serializable positive :=
  {| serialize p := serialize (Zpos p);
     deserialize z := do z' <- deserialize z; Some (Z.to_pos z'); |}.
Next Obligation. auto. Qed.

Program Instance ser_value_equivalence : Serializable SerializedValue :=
  {| serialize v := v;
     deserialize v := Some v; |}.
Solve Obligations with reflexivity.

Program Instance BoundedN_equivalence {bound : N} : Serializable (BoundedN bound) :=
  {| serialize bn := serialize (countable.encode bn);
    deserialize v :=
      do p <- (deserialize v : option positive);
      countable.decode p |}.
Next Obligation.
  intros bound x.
  cbn.
  rewrite deserialize_serialize.
  cbn.
  now rewrite countable.decode_encode.
Qed.

(* Program Instance generates an insane amount of obligations for sums,
   so we define it by ourselves. *)
Section Sum.
  Context `{Serializable A} `{Serializable B}.

  Definition serialize_sum (v : A + B) :=
    let (is_left, ser) :=
        match v with
        | inl l => (true, serialize l)
        | inr r => (false, serialize r)
        end in
    build_ser_value (ser_pair ser_bool ser.(ser_value_type)) (is_left, ser.(ser_value)).

  Definition deserialize_sum (val : SerializedValue) : option (A + B) :=
    match val with
    | build_ser_value (ser_pair ser_bool v) (is_left, val) =>
      if is_left then
        do a <- deserialize (build_ser_value v val) : option A;
        Some (inl a)
      else
        do b <- deserialize (build_ser_value v val) : option B;
        Some (inr b)
    | _ => None
    end.

  Lemma deserialize_serialize_sum (s : A + B)
    : deserialize_sum (serialize_sum s) = Some s.
  Proof.
    unfold serialize_sum, deserialize_sum.
    destruct s as [a | b]; cbn; rewrite deserialize_serialize; reflexivity.
  Qed.

  Global Instance sum_serializable : Serializable (A + B) :=
    {| serialize := serialize_sum;
       deserialize := deserialize_sum;
       deserialize_serialize := deserialize_serialize_sum; |}.
End Sum.

Section Product.
  Context `{Serializable A} `{Serializable B}.

  Definition serialize_product (pair : A * B) : SerializedValue :=
    let (a, b) := pair in
    let (a_ty, a_val) := serialize a in
    let (b_ty, b_val) := serialize b in
    build_ser_value (ser_pair a_ty b_ty) (a_val, b_val).

  Definition deserialize_product (val : SerializedValue) : option (A * B) :=
    match val with
    | build_ser_value (ser_pair a_ty b_ty) (a_val, b_val) =>
      do a <- deserialize (build_ser_value a_ty a_val) : option A;
      do b <- deserialize (build_ser_value b_ty b_val) : option B;
      Some (a, b)
    | _ => None
    end.

  Lemma deserialize_serialize_product (p : A * B)
        : deserialize_product (serialize_product p) = Some p.
  Proof.
    unfold serialize_product, deserialize_product.
    destruct p.
    repeat rewrite deserialize_serialize.
    reflexivity.
  Qed.

  Global Instance product_serializable : Serializable (A * B) :=
    {| serialize := serialize_product;
       deserialize := deserialize_product;
       deserialize_serialize := deserialize_serialize_product; |}.
End Product.

Section List.
  Context `{Serializable A}.

  Definition serialize_list (l : list A) : SerializedValue :=
    let go a (acc : SerializedValue) :=
        let (a_ty, a_val) := serialize a in
        let (acc_ty, acc_val) := acc in
        build_ser_value (ser_pair a_ty acc_ty) (a_val, acc_val) in
    fold_right go (build_ser_value ser_unit tt) l.

  Definition deserialize_list (val : SerializedValue) : option (list A) :=
    let fix aux (ty : SerializedType) (val : interp_type ty) : option (list A) :=
        match ty, val with
        | ser_pair hd_ty tl_ty, (hd_val, tl_val) =>
          do hd <- deserialize (build_ser_value hd_ty hd_val);
          do tl <- aux tl_ty tl_val;
          Some (hd :: tl)
        | ser_unit, _ => Some []
        | _, _ => None
        end in
    let (ty, uval) := val in
    aux ty uval.

  Lemma deserialize_serialize_list (l : list A)
        : deserialize_list (serialize_list l) = Some l.
  Proof.
    unfold serialize_list, deserialize_list.
    induction l as [| hd tl IHl].
    - reflexivity.
    - cbn in *.
      rewrite IHl; clear IHl.
      rewrite deserialize_serialize.
      reflexivity.
  Qed.

  Global Instance list_serializable : Serializable (list A) :=
    {| serialize := serialize_list;
       deserialize := deserialize_list;
       deserialize_serialize := deserialize_serialize_list; |}.
End List.

Program Instance map_serializable
        `{Serializable A}
        `{countable.Countable A}
        `{Serializable B}
  : Serializable (FMap A B) :=
  {| serialize m := serialize (@FMap.elements A B _ _ m);
     deserialize val :=
       do elems <- deserialize val : option (list (A * B));
       Some (FMap.of_list elems); |}.
Next Obligation.
  intros.
  cbn.
  rewrite deserialize_serialize.
  cbn.
  rewrite FMap.of_elements_eq.
  reflexivity.
Qed.

Program Instance set_serializable
        `{Serializable A}
        `{countable.Countable A}
  : Serializable (FMap A unit) :=
  {| serialize s := serialize (@FMap.elements A unit _ _ s);
     deserialize val :=
       do elems <- deserialize val : option (list (A * unit));
       Some (FMap.of_list elems); |}.
Next Obligation.
  intros.
  cbn.
  rewrite deserialize_serialize.
  cbn.
  rewrite FMap.of_elements_eq.
  reflexivity.
Qed.

Program Instance option_serializable `{Serializable A} : Serializable (option A) :=
  {| serialize s := serialize
                      match s with
                      | None => inl tt
                      | Some s => inr s
                      end;
     deserialize s := do s <- deserialize s;
                      match s : unit + A with
                      | inl _ => Some None
                      | inr s => Some (Some s)
                      end; |}.
Next Obligation.
  intros.
  cbn.
  rewrite deserialize_serialize.
  cbn.
  destruct x; auto.
Qed.

Ltac make_serializer_case ty :=
  match ty with
  | ?T1 -> ?T2 =>
    let rest := make_serializer_case T2 in
    constr:(fun (f : SerializedValue -> SerializedValue) (v : T1) =>
              rest (fun (cur : SerializedValue) => f (serialize (v, cur))))
  | SerializedValue =>
    constr:(fun (f : SerializedValue -> SerializedValue) => f (serialize tt))
  end.

Ltac make_serializer_aux term tag :=
  match type of term with
  | ?T1 -> (?T2 -> ?T3) =>
    let cs := make_serializer_case T1 in
    let cs := constr:(cs (fun x => serialize (tag, x))) in
    let term := (eval hnf in (term cs)) in
    make_serializer_aux term (S tag)
  | ?T -> SerializedValue =>
    term
  end.

Ltac make_serializer eliminator :=
  let term := (eval hnf in (eliminator (fun _ => SerializedValue))) in
  let serializer := make_serializer_aux term 0 in
  eval cbn in serializer.

Ltac make_deserializer_case ty :=
  match ty with
  | ?T1 -> ?T2 =>
    let rest := make_deserializer_case T2 in
    constr:(fun builder sv =>
              do '(a, sv) <- (deserialize sv : option (T1 * SerializedValue));
              rest (builder a) sv)
  | ?T => constr:(fun (value : T) (sv : SerializedValue) => Some value)
  end.

Ltac make_deserializer_aux ctors rty :=
  match ctors with
  | (?ctor, ?tl) =>
    let ty := type of ctor in
    let cs := make_deserializer_case ty in
    let rest := make_deserializer_aux tl rty in
    constr:(
      fun tag sv =>
        match tag with
        | 0 => cs ctor sv
        | S tag => rest tag sv
        end)
  | tt => constr:(fun (tag : nat) (sv : SerializedValue) => @None rty)
  end.

Ltac get_final_type ty :=
  match ty with
  | ?T1 -> ?T2 => get_final_type T2
  | ?T => T
  end.

Ltac make_deserializer ctors rty :=
  let deser := make_deserializer_aux ctors rty in
  let deser := constr:(fun sv => do '(tag, sv) <- deserialize sv; deser tag sv) in
  eval cbn in deser.

Ltac get_ty_from_elim_ty ty :=
  match ty with
  | forall (_ : ?T -> Type), _ => T
  end.

Ltac make_serializable eliminator ctors :=
  let ser := make_serializer eliminator in
  let elim_ty := type of eliminator in
  let ty := get_ty_from_elim_ty elim_ty in
  let deser := make_deserializer ctors ty in
  exact
    {| serialize := ser;
       deserialize := deser;
       deserialize_serialize :=
         ltac:(intros []; repeat (cbn in *; try rewrite deserialize_serialize; auto)) |}.

Notation "'Derive' 'Serializable' rect" :=
  ltac:(make_serializable rect tt) (at level 0, rect at level 10, only parsing).

Notation "'Derive' 'Serializable' rect < c0 , .. , cn >" :=
  (let pairs := pair c0 .. (pair cn tt) .. in
   ltac:(
     (* This matches last-to-first so it always finds 'pairs' *)
     match goal with
     | [pairs := ?x |- _] => make_serializable rect x
     end))
    (at level 0, rect at level 10, c0, cn at level 9, only parsing).
