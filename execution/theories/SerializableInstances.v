From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import OptionMonad.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import SerializableBase.
From Stdlib Require Import Ascii.
From Stdlib Require Import List.
From Stdlib Require Import Psatz.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.

Import ListNotations.



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

    replace ({|
      ser_value_type := ser_value_type (serialize a);
      ser_value := ser_value (serialize a)
    |}) with (serialize a).
    2: reflexivity.
    replace ({|
      ser_value_type := ser_value_type (serialize b);
      ser_value := ser_value (serialize b)
    |}) with (serialize b).
    2: reflexivity.

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
      replace ({|
        ser_value_type := ser_value_type (serialize hd);
        ser_value := ser_value (serialize hd)
      |}) with (serialize hd).
      2: reflexivity.
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
