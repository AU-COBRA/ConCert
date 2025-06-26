(* This file formalizes a bounded natural number type which is
efficient to compute with. *)
From ConCert.Execution Require Import Finite.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import OptionMonad.
From ConCert.Utils Require Import Extras.
From Stdlib Require Import NArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Eqdep_dec.
From Stdlib Require Import List.
From Stdlib Require Import Psatz.
From stdpp Require countable.
Import ListNotations.

Local Open Scope N.

(* The shape of the proof is carefully chosen so that we have unicity
of identity proofs. This is similar to CompCert's formalization of
machine integers. Additionally, we choose to put bound first in the
comparison so that Coq does not partially reduce the comparison, which
results in a term with a match containing 'bound' cases. This was
suggested as a solution by Gaëtan Gilbert in Gitter. *)
Inductive BoundedN (bound : N) :=
  bounded (n : N) (_ : (bound ?= n) = Gt).

Arguments bounded {_}.

Module BoundedN.
  Definition to_N {bound : N} (n : BoundedN bound) : N :=
    let (val, _) := n in val.

  Definition eqb {bound : N} (a b : BoundedN bound) : bool :=
    N.eqb (to_N a) (to_N b).

  Definition of_N_compare {bound : N} (n : N) : option ((bound ?= n) = Gt) :=
    match bound ?= n as comp return (option (comp = Gt)) with
    | Gt => Some eq_refl
    | _ => None
    end.

  Definition of_N {bound : N} (n : N) : option (BoundedN bound) :=
    match of_N_compare n with
    | Some prf => Some (bounded n prf)
    | None => None
    end.

  Definition to_nat {bound : N} (n : BoundedN bound) : nat :=
    N.to_nat (to_N n).

  Definition of_nat {bound : N} (n : nat) : option (BoundedN bound) :=
    of_N (N.of_nat n).

  Definition to_Z {bound : N} (n : BoundedN bound) : Z :=
    Z.of_N (to_N n).

  Definition of_Z {bound : N} (z : Z) : option (BoundedN bound) :=
    if (z <? 0)%Z then None else of_N (Z.to_N z).

  Definition of_Z_const (bound : N) (z : Z) :=
    unpack_option (@of_Z bound z).

  Lemma to_N_inj {bound : N} {a b : BoundedN bound} :
    to_N a = to_N b -> a = b.
  Proof.
    intros eq.
    destruct a, b.
    cbn in *.
    subst.
    f_equal.
    apply UIP_dec.
    decide equality.
  Qed.

  Local Hint Resolve to_N_inj : core.

  Lemma eqb_spec {bound : N} (a b : BoundedN bound) :
    Bool.reflect (a = b) (eqb a b).
  Proof.
    unfold eqb.
    destruct (N.eqb_spec (to_N a) (to_N b)) as [eq | neq].
    - constructor.
      auto.
    - constructor.
      intros H; rewrite H in neq; tauto.
  Qed.

  Lemma eqb_refl {bound : N} (n : BoundedN bound) :
    eqb n n = true.
  Proof. destruct (eqb_spec n n); tauto. Qed.

  Lemma to_nat_inj {bound : N} (a b : BoundedN bound) :
    to_nat a = to_nat b -> a = b.
  Proof.
    intros eq.
    apply to_N_inj.
    unfold to_nat in eq.
    now apply N2Nat.inj.
  Qed.

  Lemma to_Z_inj {bound : N} (a b : BoundedN bound) :
    to_Z a = to_Z b -> a = b.
  Proof.
    intros eq.
    apply to_N_inj.
    unfold to_Z in eq.
    now apply N2Z.inj.
  Qed.

  Lemma of_to_N {bound : N} (n : BoundedN bound) :
    of_N (to_N n) = Some n.
  Proof.
    destruct n as [n prf]; cbn.
    unfold of_N.
    replace (of_N_compare n) with (Some prf); auto.
    unfold of_N_compare.
    now rewrite prf.
  Qed.

  Lemma of_to_nat {bound : N} (n : BoundedN bound) :
    of_nat (to_nat n) = Some n.
  Proof.
    unfold to_nat, of_nat.
    rewrite N2Nat.id.
    apply of_to_N.
  Qed.

  Lemma of_n_not_lt_0 (n : N) :
    (Z.of_N n <? 0)%Z = false.
  Proof.
    destruct (Z.ltb_spec (Z.of_N n) 0).
    - apply Zlt_not_le in H.
      destruct (H (N2Z.is_nonneg n)).
    - reflexivity.
  Qed.

  Lemma of_to_Z {bound : N} (n : BoundedN bound) :
    of_Z (to_Z n) = Some n.
  Proof.
    unfold to_Z, of_Z.
    rewrite of_n_not_lt_0.
    rewrite N2Z.id.
    apply of_to_N.
  Qed.

  Lemma of_N_some {bound : N} {m : N} {n : BoundedN bound} :
    of_N m = Some n -> to_N n = m.
  Proof.
    intros H.
    unfold of_N in H.
    destruct (of_N_compare m); try congruence.
    now inversion H.
  Qed.

  Lemma of_N_none {bound : N} {m : N} :
    @of_N bound m = None -> bound <= m.
  Proof.
    intros H.
    unfold of_N in H.
    destruct (of_N_compare m) eqn:comp; try congruence.
    unfold of_N_compare in comp.
    destruct (bound ?= m) eqn:comp'; congruence.
  Qed.

  Lemma of_nat_some {bound : N} {m : nat} {n : BoundedN bound} :
    of_nat m = Some n -> to_nat n = m.
  Proof.
    intros H.
    unfold to_nat.
    rewrite (of_N_some H).
    apply Nat2N.id.
  Qed.

  Lemma of_nat_none {bound : N} {m : nat} :
    @of_nat bound m = None -> bound <= N.of_nat m.
  Proof. apply of_N_none. Qed.

  Lemma in_map_of_nat (bound : N) (n : BoundedN bound) (xs : list nat) :
    In n (map_option (@of_nat bound) xs) <-> In (to_nat n) xs.
  Proof.
    induction xs as [|x xs IH].
    - split; intros H; inversion H.
    - cbn.
      destruct (of_nat x) eqn:of_nat_x; split; intros H.
      + destruct H.
        * subst.
          left.
          symmetry.
          now apply of_nat_some.
        * tauto.
      + destruct H as [eq | Hin].
        * left.
          rewrite eq, of_to_nat in of_nat_x.
          congruence.
        * cbn. tauto.
      + tauto.
      + destruct H as [eq | Hin].
        * rewrite eq, of_to_nat in of_nat_x; inversion of_nat_x.
        * tauto.
  Qed.

  Module Stdpp.
    Import countable.
    Lemma eq_dec {bound : N} : EqDecision (BoundedN bound).
    Proof.
      intros x y.
      destruct (BoundedN.eqb_spec x y); [left|right]; assumption.
    Qed.

    Global Instance BoundedNEqDec {bound : N} : EqDecision (BoundedN bound) :=
      eq_dec.

    Definition encode_bounded {bound : N} (n : BoundedN bound) : positive :=
      encode (to_N n).

    Definition decode_bounded {bound : N} (n : positive) : option (BoundedN bound) :=
      decode n >>= of_N.

    Lemma decode_encode_bounded {bound : N} (n : BoundedN bound) :
      decode_bounded (encode_bounded n) = Some n.
    Proof.
      unfold decode_bounded, encode_bounded.
      rewrite decode_encode.
      cbn.
      apply of_to_N.
    Qed.

    Global Instance BoundedNCountable {bound : N} : Countable (BoundedN bound) :=
      {| encode := encode_bounded;
         decode := decode_bounded;
         decode_encode := decode_encode_bounded; |}.
  End Stdpp.

  Definition bounded_elements (bound : N) : list (BoundedN bound) :=
    map_option of_nat (List.seq 0 (N.to_nat bound)).

  Lemma bounded_elements_set (bound : N) :
    NoDup (bounded_elements bound).
  Proof.
    unfold bounded_elements.
    pose proof (seq_NoDup (N.to_nat bound) 0) as nodup.
    pose proof (in_seq (N.to_nat bound) 0) as in_seq'.
    pose proof (fun n => proj1 (in_seq' n)) as in_seq; clear in_seq'.
    induction nodup; try constructor.
    cbn.
    pose proof (in_seq x) as x_bound.
    specialize (x_bound (or_introl eq_refl)).
    destruct x_bound as [useless x_bound]; clear useless.
    cbn in x_bound.
    destruct (of_nat x) eqn:ofnatx; cycle 1.
    apply of_nat_none in ofnatx.
    lia.
    constructor.
    + intros Hin.
      apply in_map_of_nat in Hin.
      apply of_nat_some in ofnatx.
      rewrite <- ofnatx in H.
      tauto.
    + apply IHnodup.
      intros n in_n_l.
      apply (in_seq n (or_intror in_n_l)).
  Qed.

  Lemma bounded_elements_all (bound : N) :
    forall a, In a (bounded_elements bound).
  Proof.
    unfold bounded_elements.
    intros t.
    apply in_map_of_nat.
    apply in_seq.
    unfold to_nat.
    destruct t as [t lt].
    cbn.
    change ((bound ?= t) = Gt) with (bound > t) in lt.
    lia.
  Qed.

  Global Instance BoundedN_finite {bound : N} : Finite (BoundedN bound) :=
    {| elements := bounded_elements bound;
       elements_set := bounded_elements_set bound;
       elements_all := bounded_elements_all bound; |}.
End BoundedN.

Declare Scope BoundedN_scope.
Delimit Scope BoundedN_scope with BoundedN.
Bind Scope BoundedN_scope with BoundedN.
