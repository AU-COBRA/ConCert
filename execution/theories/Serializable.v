(* This file defines a common storage format for countable types.
This format, SerializedValue, is either a unit/int/bool or a pair/list
of these. We also define Serializable as a type class capturing that a
type can be converted from and to this format. *)

From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import OptionMonad.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import BoundedN.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import String.
From Coq Require Import ZArith.

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

#[export]
Program Instance unit_serializable : Serializable unit :=
  {| serialize u := build_ser_value ser_unit u;
     deserialize := extract_ser_value ser_unit; |}.
Solve Obligations with reflexivity.

#[export]
Program Instance int_serializable : Serializable Z :=
  {| serialize i := build_ser_value ser_int i;
     deserialize := extract_ser_value ser_int; |}.
Solve Obligations with reflexivity.

#[export]
Program Instance bool_serializable : Serializable bool :=
  {| serialize b := build_ser_value ser_bool b;
     deserialize := extract_ser_value ser_bool; |}.
Solve Obligations with reflexivity.

#[export]
Program Instance nat_serializable : Serializable nat :=
  {| serialize n := serialize (Z.of_nat n);
     deserialize z := do z' <- deserialize z;
                      if (z' <? 0)%Z
                      then None
                      else Some (Z.to_nat z'); |}.
Next Obligation.
  intros x.
  cbn.
  rewrite deserialize_serialize.
  cbn.
  rewrite Nat2Z.id.
  specialize (Nat2Z.is_nonneg x) as H.
  apply Z.ltb_ge in H.
  rewrite H.
  reflexivity.
Qed.

#[export]
Program Instance N_serializable : Serializable N :=
  {| serialize n := serialize (Z.of_N n);
     deserialize z := do z' <- deserialize z;
                      if (z' <? 0)%Z
                      then None
                      else Some (Z.to_N z'); |}.
Next Obligation.
  intros x.
  cbn.
  rewrite deserialize_serialize.
  cbn.
  rewrite N2Z.id.
  specialize (N2Z.is_nonneg x) as H.
  apply Z.ltb_ge in H.
  rewrite H.
  reflexivity.
Qed.

#[export]
Program Instance ser_positive_equivalence : Serializable positive :=
  {| serialize p := serialize (Zpos p);
     deserialize z := do z' <- deserialize z;
                      if (0 <? z')%Z
                      then Some (Z.to_pos z')
                      else None; |}.
Solve Obligations with auto.

#[export]
Program Instance ser_value_equivalence : Serializable SerializedValue :=
  {| serialize v := v;
     deserialize v := Some v; |}.
Solve Obligations with reflexivity.

#[export]
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

#[export]
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

#[export]
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

#[export]
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

#[export]
Program Instance ascii_serializable : Serializable ascii :=
  {| serialize a := serialize (Ascii.N_of_ascii a);
     deserialize p := do p <- deserialize p;
                      if (p <? 256)%N then Some (Ascii.ascii_of_N p)
                      else None; |}.
Next Obligation.
  intros.
  cbn.
  rewrite deserialize_serialize.
  specialize (N_ascii_bounded x) as H.
  apply N.ltb_lt in H.
  rewrite H.
  apply f_equal.
  apply ascii_N_embedding.
Qed.

#[export]
Program Instance string_serializable : Serializable string :=
  {| serialize s := serialize (list_ascii_of_string s);
     deserialize p := do la <- deserialize p;
                      Some (string_of_list_ascii la); |}.
Next Obligation.
  intros.
  cbn.
  rewrite deserialize_serialize.
  apply f_equal.
  apply string_of_list_ascii_of_string.
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
  | ?T => constr:(fun (value : T) (sv : SerializedValue) =>
              do _ <- (deserialize sv : option unit);
              Some value)
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

Section Countable.
  Instance SerializedType_interp_EqDecision
           (t : SerializedType) : stdpp.base.EqDecision (interp_type t).
  Proof. induction t; typeclasses eauto. Defined.
  Instance SerializedType_interp_Countable
           (t : SerializedType) : countable.Countable (interp_type t).
  Proof. induction t; typeclasses eauto. Defined.

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

Section RightInverse.
Local Transparent deserialize serialize.

Lemma deserialize_unit_right_inverse : forall x (y : unit),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  destruct x as [ty val].
  destruct ty;
    now inversion_clear deser_some.
Qed.

Lemma deserialize_int_right_inverse : forall x (y : Z),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  destruct x as [ty val].
  destruct ty;
    now inversion_clear deser_some.
Qed.

Lemma deserialize_bool_right_inverse : forall x (y : bool),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  destruct x as [ty val].
  destruct ty;
    now inversion_clear deser_some.
Qed.

Lemma deserialize_nat_right_inverse : forall x (y : nat),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  apply deserialize_int_right_inverse.
  cbn in *.
  destruct extract_ser_value;
    try discriminate.
  destruct (i <? 0)%Z eqn:H;
    try discriminate.
  apply Z.ltb_ge in H.
  inversion_clear deser_some.
  rewrite Z2Nat.id by assumption.
  reflexivity.
Qed.

Lemma deserialize_N_right_inverse : forall x (y : N),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  apply deserialize_int_right_inverse.
  cbn in *.
  destruct extract_ser_value;
    try discriminate.
  destruct (i <? 0)%Z eqn:H;
    try discriminate.
  apply Z.ltb_ge in H.
  inversion_clear deser_some.
  rewrite Z2N.id by assumption.
  reflexivity.
Qed.

Lemma deserialize_positive_right_inverse : forall x (y : positive),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  apply deserialize_int_right_inverse.
  cbn in *.
  destruct extract_ser_value;
    try discriminate.
  destruct (0 <? i)%Z eqn:H;
    try discriminate.
  apply Z.ltb_lt in H.
  inversion_clear deser_some.
  rewrite Z2Pos.id by assumption.
  reflexivity.
Qed.

Lemma deserialize_serialized_value_right_inverse : forall x (y : SerializedValue),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  now inversion deser_some.
Qed.

Lemma deserialize_sum_right_inverse : forall {A B : Type} `{Serializable A} `{Serializable B}
                                              x (y : A + B),
  (forall x' (y' : A), deserialize x' = Some y' -> x' = serialize y') ->
  (forall x' (y' : B), deserialize x' = Some y' -> x' = serialize y') ->
  deserialize x = Some y ->
  x = serialize y.
Proof.
  cbn.
  unfold serialize_sum, deserialize_sum in *.
  destruct x as [ty val].
  intros * HA HB deser_some.
  destruct ty;
    try discriminate.
  destruct ty1;
    try discriminate.
  destruct val.
  destruct i; cbn in *;
    destruct deserialize eqn:deser_a_some;
    try discriminate;
    inversion_clear deser_some.
  - apply HA in deser_a_some as <-.
    reflexivity.
  - apply HB in deser_a_some as <-.
    reflexivity.
Qed.

Lemma deserialize_product_right_inverse : forall {A B : Type} `{Serializable A} `{Serializable B}
                                              x (y : A * B),
  (forall x' (y' : A), deserialize x' = Some y' -> x' = serialize y') ->
  (forall x' (y' : B), deserialize x' = Some y' -> x' = serialize y') ->
  deserialize x = Some y ->
  x = serialize y.
Proof.
  cbn.
  unfold serialize_product, deserialize_product.
  destruct x as [ty val].
  intros * HA HB deser_some.
  destruct ty;
    try discriminate.
  destruct val.
  cbn in *.
  destruct deserialize eqn:deser_a_some in deser_some;
    try discriminate.
  destruct deserialize eqn:deser_b_some in deser_some;
    try discriminate.
  inversion_clear deser_some.
  apply HA in deser_a_some as <-.
  apply HB in deser_b_some as <-.
  reflexivity.
Qed.

Lemma deserialize_list_right_inverse : forall {A : Type} `{Serializable A} (l : list A) x,
  (forall x' (l' : A), deserialize x' = Some l' -> x' = serialize l') ->
  deserialize x = Some l ->
  x = serialize l.
Proof.
  cbn.
  (* unfold serialize_list, deserialize_list. *)
  destruct x as [ty val]. cbn.
  generalize dependent ty.
  induction l as [| hd tl IHl];
    intros * HA deser_some;
    cbn.
  -
    destruct ty;
      try discriminate;
      destruct val;
      auto.
    repeat match goal with
    | H : match ?x with | Some _ => _ | None => _ end = _ |- _ => destruct x
    end;
    discriminate.
  - destruct ty;
      try discriminate.
    destruct val.
    destruct deserialize eqn:deser_hd_some in deser_some;
      try discriminate.
    match goal with
    | H : match ?x with | Some _ => _ | None => _ end = _ |- _ => destruct x eqn:H1
    end;
    try discriminate.
    inversion deser_some. subst.
    apply HA in deser_hd_some as <-.
    apply IHl in H1; auto.
    unfold serialize_list in H1.
    rewrite <- H1.
    reflexivity.
Qed.


Lemma deserialize_option_right_inverse : forall {A : Type} `{Serializable A} x (y : option A),
  (forall x' (y' : A), deserialize x' = Some y' -> x' = serialize y') ->
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * H deser_some.
  specialize deserialize_unit_right_inverse as H1.
  apply deserialize_sum_right_inverse; auto.
  clear H H1.
  cbn in *.
  destruct deserialize_sum;
    try discriminate.
  destruct s;
    inversion_clear deser_some;
    auto.
  now destruct u.
Qed.

Lemma deserialize_ascii_right_inverse : forall x (y : ascii),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  apply deserialize_N_right_inverse.
  unfold deserialize, ascii_serializable in deser_some.
  destruct deserialize;
    try discriminate.
  cbn in *.
  destruct (n <? 256)%N eqn:H;
    inversion_clear deser_some.
  apply N.ltb_lt in H.
  now rewrite N_ascii_embedding.
Qed.

Lemma deserialize_string_right_inverse : forall x (y : string),
  deserialize x = Some y ->
  x = serialize y.
Proof.
  intros * deser_some.
  specialize deserialize_ascii_right_inverse as H.
  apply deserialize_list_right_inverse; auto.
  clear H.
  cbn in *.
  destruct deserialize_list;
    try discriminate.
  inversion_clear deser_some.
  rewrite list_ascii_of_string_of_list_ascii.
  reflexivity.
Qed.

Local Opaque deserialize serialize.
End RightInverse.
