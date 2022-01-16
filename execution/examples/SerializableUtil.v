From ConCert.Execution Require Import Serializable.
From Coq Require Import Ascii.
From Coq Require Import String.
From Coq Require Import ZArith.


Lemma q {T : Type} `{Serializable T} x y :
  deserialize x <> deserialize y ->
  x <> y.
Proof.
  intros * deser_ne.
  contradict deser_ne.
  subst.
  reflexivity.
Qed.

Lemma q0 {T : Type} `{Serializable T} x y :
  deserialize x <> Some y ->
  x <> serialize y.
Proof.
  intros * deser_ne.
  contradict deser_ne.
  subst.
  apply deserialize_serialize.
Qed.

Lemma q1 {T : Type} `{Serializable T} x y :
  x = serialize y ->
  deserialize x = Some y.
Proof.
  intros * eq.
  rewrite eq, deserialize_serialize.
  reflexivity.
Qed.

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
    repeat match  goal with
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
