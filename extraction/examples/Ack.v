(** * Ackermann function *)

From Coq Require Import Program.Wf.
From Coq Require Import Arith.Arith.

(** Taken from here: https://stackoverflow.com/a/44832894 *)

Definition lexicographic_ordering (ab1 ab2 : nat * nat) : Prop :=
  match ab1, ab2 with
  | (a1, b1), (a2, b2) =>
      (a1 < a2) \/ ((a1 = a2) /\ (b1 < b2))
  end.

Lemma lt_wf_ind :
  forall n (P:nat -> Prop), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof. intro p; intros; elim (lt_wf p); auto with arith. Defined.

Lemma lt_wf_double_ind :
  forall P:nat -> nat -> Prop,
    (forall n m,
      (forall p (q:nat), p < n -> P p q) ->
      (forall p, p < m -> P n p) -> P n m) -> forall n m, P n m.
Proof.
  intros P Hrec p. pattern p. apply lt_wf_ind.
  intros n H q. pattern q. apply lt_wf_ind. auto.
Defined.

Lemma lexicographic_ordering_wf : well_founded lexicographic_ordering.
Proof.
  intros (a, b); pattern a, b; apply lt_wf_double_ind.
  intros m n H1 H2.
  constructor; intros (m', n') [G | [-> G]].
  - now apply H1.
  - now apply H2.
Defined.

Program Fixpoint ack (ab : nat * nat) {wf lexicographic_ordering ab} : nat :=
  match ab with
  | (0, b) => b + 1
  | (S a, 0) => ack (a, 1)
  | (S a, S b) => ack (a, ack (S a, b))
  end.
Next Obligation.
  inversion Heq_ab; subst. left; auto. Defined.
Next Obligation.
  apply lexicographic_ordering_wf. Defined.
