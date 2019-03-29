From Coq Require Import ZArith.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Containers.
From SmartContracts Require Import Automation.
From SmartContracts Require Import BoundedN.
From Coq Require Import List.

Import ListNotations.

Inductive OakType :=
  | oak_empty : OakType
  | oak_unit : OakType
  | oak_int : OakType
  | oak_bool : OakType
  | oak_pair : OakType -> OakType -> OakType
  | oak_sum : OakType -> OakType -> OakType
  | oak_list : OakType -> OakType
  | oak_set : OakType -> OakType
  | oak_map : OakType -> OakType -> OakType.

Module OakType.
  Scheme Equality for OakType.
  Definition eqb := OakType_beq.
  Definition eq_dec := OakType_eq_dec.

  Fixpoint eqb_spec (a b : OakType) :
    Bool.reflect (a = b) (eqb a b).
  Proof.
    destruct a, b; simpl in *; try (left; congruence); try (right; congruence).
    1, 2, 5: destruct (eqb_spec a1 b1), (eqb_spec a2 b2);
      try (left; congruence); try (right; congruence).
    1, 2: destruct (eqb_spec a b); try (left; congruence); try (right; congruence).
  Qed.
End OakType.

Set Primitive Projections.
Record OakInterpretation :=
  build_interpretation {
    oi_ty : Type;
    oi_eqdec : stdpp.base.EqDecision oi_ty;
    oi_countable : countable.Countable oi_ty;
  }.

Arguments build_interpretation _ {_ _}.

Local Fixpoint interp_type_with_ordering (t : OakType) : OakInterpretation :=
  match t with
  | oak_empty => build_interpretation Empty_set
  | oak_unit => build_interpretation unit
  | oak_int => build_interpretation Z
  | oak_bool => build_interpretation bool
  | oak_sum a b =>
    let (aT, _, _) := interp_type_with_ordering a in
    let (bT, _, _) := interp_type_with_ordering b in
    build_interpretation (aT + bT)%type
  | oak_pair a b =>
    let (aT, _, _) := interp_type_with_ordering a in
    let (bT, _, _) := interp_type_with_ordering b in
    build_interpretation (aT * bT)%type
  | oak_list a =>
    let (aT, _, _) := interp_type_with_ordering a in
    build_interpretation (list aT)
  | oak_set a =>
    let (aT, _, _) := interp_type_with_ordering a in
    build_interpretation (FMap aT unit)
  | oak_map a b =>
    let (aT, _, _) := interp_type_with_ordering a in
    let (bT, _, _) := interp_type_with_ordering b in
    build_interpretation (FMap aT bT)
  end.

Definition interp_type (t : OakType) : Type :=
  oi_ty (interp_type_with_ordering t).

Record OakValue :=
  build_oak_value {
    oak_value_type : OakType;
    oak_value : interp_type oak_value_type;
  }.

Definition extract_oak_value (t : OakType) (value : OakValue) : option (interp_type t).
Proof.
  destruct value as [ty val].
  destruct (OakType.eq_dec t ty).
  - subst. exact (Some val).
  - exact None.
Defined.

(* Defines that a type can be serialized into OakValue and deserialized from it,
   and that these are inverses *)
Class OakTypeEquivalence (ty : Type) :=
  {
    serialize : ty -> OakValue;
    deserialize : OakValue -> option ty;
    deserialize_serialize : forall (x : ty), deserialize (serialize x) = Some x;
  }.

Global Opaque serialize deserialize deserialize_serialize.

Program Instance oak_empty_equivalence : OakTypeEquivalence Empty_set :=
  {| serialize e := ltac:(contradiction);
     deserialize v := None; |}.
Solve Obligations with contradiction.

Program Instance oak_unit_equivalence : OakTypeEquivalence unit :=
  {| serialize u := build_oak_value oak_unit u;
     deserialize := extract_oak_value oak_unit; |}.
Solve Obligations with reflexivity.

Program Instance oak_int_equivalence : OakTypeEquivalence Z :=
  {| serialize i := build_oak_value oak_int i;
     deserialize := extract_oak_value oak_int; |}.
Solve Obligations with reflexivity.

Program Instance oak_bool_equivalence : OakTypeEquivalence bool :=
  {| serialize b := build_oak_value oak_bool b;
     deserialize := extract_oak_value oak_bool; |}.
Solve Obligations with reflexivity.

Program Instance oak_nat_equivalence : OakTypeEquivalence nat :=
  {| serialize n := serialize (Z.of_nat n);
     deserialize z := do z' <- deserialize z; Some (Z.to_nat z'); |}.
Next Obligation.
  intros x.
  simpl.
  rewrite deserialize_serialize.
  simpl.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Program Instance oak_positive_equivalence : OakTypeEquivalence positive :=
  {| serialize p := serialize (Zpos p);
     deserialize z := do z' <- deserialize z; Some (Z.to_pos z'); |}.
Next Obligation. prove. Qed.

Program Instance oak_value_equivalence : OakTypeEquivalence OakValue :=
  {| serialize v := v;
     deserialize v := Some v; |}.
Solve Obligations with reflexivity.

Program Instance BoundedN_equivalence {bound : N}
  : OakTypeEquivalence (BoundedN bound) :=
  {| serialize bn := serialize (countable.encode bn);
    deserialize v :=
      do p <- (deserialize v : option positive);
      countable.decode p |}.
Next Obligation.
  intros bound x.
  simpl.
  rewrite deserialize_serialize.
  simpl.
  now rewrite countable.decode_encode.
Qed.

(* Program Instance generates an insane amount of obligations for sums,
   so we define it by ourselves. *)
Section Sum.
  Context `{OakTypeEquivalence A} `{OakTypeEquivalence B}.

  Definition serialize_sum (v : A + B) :=
    let (is_left, ov) :=
        match v with
        | inl l => (true, serialize l)
        | inr r => (false, serialize r)
        end in
    build_oak_value (oak_pair oak_bool ov.(oak_value_type)) (is_left, ov.(oak_value)).

  Definition deserialize_sum
            `{OakTypeEquivalence A} `{OakTypeEquivalence B}
            (os : OakValue) :=
    match os with
    | build_oak_value (oak_pair oak_bool v) (b, val) =>
      if b then
        do a <- @deserialize A _ (build_oak_value v val);
        Some (inl a)
      else
        do b <- @deserialize B _ (build_oak_value v val);
        Some (inr b)
    | _ => None
    end.

  Lemma deserialize_serialize_sum (s : A + B)
    : deserialize_sum (serialize_sum s) = Some s.
  Proof.
    unfold serialize_sum, deserialize_sum.
    destruct s as [a | b]; simpl; rewrite deserialize_serialize; reflexivity.
  Qed.

  Global Instance oak_sum_equivalence : OakTypeEquivalence (A + B)%type :=
    {| serialize := serialize_sum;
       deserialize := deserialize_sum;
       deserialize_serialize := deserialize_serialize_sum; |}.
End Sum.

Section Product.
  Context `{OakTypeEquivalence A} `{OakTypeEquivalence B}.

  Definition serialize_product '(a, b) :=
    let 'build_oak_value a_oty a_val := @serialize A _ a in
    let 'build_oak_value b_oty b_val := @serialize B _ b in
    build_oak_value (oak_pair a_oty b_oty) (a_val, b_val).

  Definition deserialize_product op :=
    match op with
    | build_oak_value (oak_pair a_ty b_ty) (a_val, b_val) =>
      do a <- @deserialize A _ (build_oak_value a_ty a_val);
      do b <- @deserialize B _ (build_oak_value b_ty b_val);
      Some (a, b)
    | _ => None
    end.

  Lemma deserialize_serialize_product (p : A * B)
        : deserialize_product (serialize_product p) = Some p.
  Proof.
    unfold serialize_product, deserialize_product.
    destruct p as [a b].
    repeat rewrite deserialize_serialize.
    reflexivity.
  Qed.

  Global Instance oak_product_equivalence : OakTypeEquivalence (A * B) :=
    {| serialize := serialize_product;
       deserialize := deserialize_product;
       deserialize_serialize := deserialize_serialize_product; |}.
End Product.

Section List.
  Context `{OakTypeEquivalence A}.

  Definition serialize_list (l : list A) :=
    let go a acc :=
        let 'build_oak_value a_oty a_val := serialize a in
        let 'build_oak_value acc_oty acc_val := acc in
        build_oak_value (oak_pair a_oty acc_oty) (a_val, acc_val) in
    fold_right go (build_oak_value oak_unit tt) l.

  Definition deserialize_list (ol : OakValue) :=
    let fix aux (ty : OakType) (val : interp_type ty) : option (list A) :=
        match ty, val with
        | oak_pair hd_ty tl_ty, (hd_val, tl_val) =>
          do hd <- deserialize (build_oak_value hd_ty hd_val);
          do tl <- aux tl_ty tl_val;
          Some (hd :: tl)
        | oak_unit, _ => Some []
        | _, _ => None
        end in
    let 'build_oak_value ol_ty ol_val := ol in
    aux ol_ty ol_val.

  Lemma deserialize_serialize_list (l : list A)
        : deserialize_list (serialize_list l) = Some l.
  Proof.
    unfold serialize_list, deserialize_list.
    induction l as [| hd tl IHl].
    - reflexivity.
    - simpl in *.
      rewrite IHl; clear IHl.
      rewrite deserialize_serialize.
      reflexivity.
  Qed.

  Global Instance oak_list_equivalence : OakTypeEquivalence (list A) :=
    {| serialize := serialize_list;
       deserialize := deserialize_list;
       deserialize_serialize := deserialize_serialize_list; |}.
End List.

Program Instance oak_map_equivalence
        `{OakTypeEquivalence A}
        `{countable.Countable A}
        `{OakTypeEquivalence B}
  : OakTypeEquivalence (FMap A B) :=
  {| serialize m := serialize (@FMap.elements A B _ _ m);
     deserialize om :=
       do elems <- @deserialize (list (A * B)) _ om;
     Some (FMap.of_list elems); |}.
Next Obligation.
  intros A OTE_A Eq_A C_A B OTE_B m.
  simpl.
  rewrite deserialize_serialize.
  simpl.
  rewrite FMap.of_elements_eq.
  reflexivity.
Qed.

Program Instance oak_set_equivalence
        `{OakTypeEquivalence A}
        `{countable.Countable A}
  : OakTypeEquivalence (FMap A unit) :=
  {| serialize s := serialize (@FMap.elements A unit _ _ s);
     deserialize os :=
       do elems <- @deserialize (list (A * unit)) _ os;
       Some (FMap.of_list elems); |}.
Next Obligation.
  intros A OTE_A Eq_A C_A m.
  simpl.
  rewrite deserialize_serialize.
  simpl.
  rewrite FMap.of_elements_eq.
  reflexivity.
Qed.

(*
Examples:
Definition test_bool : OakValue := build_oak_value oak_bool true.
Definition test_int : OakValue := build_oak_value oak_int 5%Z.
Definition test_set : OakValue :=
  build_oak_value
    (oak_set oak_int)
    (FSet.of_list [5; 6]%Z).
Definition test_fmap : FMap Z Z :=
  (FMap.of_list [(5, 10); (6, 10); (5, 15)])%Z.

Definition test_map : OakValue :=
  build_oak_value
    (oak_map oak_int oak_int)
    test_fmap.

Definition test_map2 : OakValue :=
  build_oak_value
    (oak_map (oak_map oak_int oak_int) oak_int)
    (FMap.of_list [(test_fmap, 15)])%Z.

Compute (extract_oak_value oak_bool test_bool) : option bool.
Compute (extract_oak_value oak_int test_bool) : option Z.
Compute (extract_oak_value oak_bool test_int) : option bool.
Compute (extract_oak_value oak_int test_int) : option Z.
Compute (extract_oak_value (oak_set oak_int) test_set) : option (FSet Z).
Compute
  (extract_oak_value
     (oak_map
        (oak_map oak_int oak_int)
        oak_int)
     test_map2)
  : option (FMap (FMap Z Z) Z).
Compute (option_map FSet.elements (extract_oak_value (oak_set oak_int) test_set)).
Compute (option_map FMap.elements (extract_oak_value (oak_map oak_int oak_int) test_map)).
*)
