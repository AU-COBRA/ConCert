From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
From Coq Require Import Sorted.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
Require Import Extras.
Import ListNotations.

Definition rel_primes (n : nat) : list Z :=
  filter (fun z => Z.gcd z (Z.of_nat n) =? 1) (map Z.of_nat (seq 0 n)).

Definition totient (n : nat) : nat :=
  length (rel_primes n).

Lemma In_rel_primes z n :
  In z (rel_primes n) <->
  rel_prime z (Z.of_nat n) /\
  0 <= z < Z.of_nat n.
Proof.
  split.
  - intros isin.
    unfold rel_primes in isin.
    apply filter_In in isin.
    destruct isin as [inseq isin].
    apply Z.eqb_eq in isin.
    split.
    + apply Zgcd_1_rel_prime; auto.
    + apply in_map_iff in inseq.
      destruct inseq as [i [ieq inseq]].
      apply in_seq in inseq.
      lia.
  - intros [isrelprime bound].
    unfold rel_primes.
    apply filter_In.
    split; cycle 1.
    + apply Z.eqb_eq.
      apply Zgcd_1_rel_prime; auto.
    + apply in_map_iff.
      exists (Z.to_nat z).
      rewrite Z2Nat.id by lia.
      split; auto.
      apply in_seq.
      split; [lia|].
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      lia.
Qed.

Lemma NoDup_rel_primes n :
  NoDup (rel_primes n).
Proof.
  unfold rel_primes.
  apply NoDup_filter.
  apply NoDup_map.
  - apply seq_NoDup.
  - intros a a' _ _.
    apply Nat2Z.inj.
Qed.

Lemma mul_both_r_mod r a a' n :
  rel_prime r n ->
  a * r mod n = a' * r mod n ->
  a mod n = a' mod n.
Proof.
  destruct (Z.eqb_spec n 0) as [->|?].
  { now rewrite !Zmod_0_r. }
  intros rel eq.
  rewrite <- (Z.mul_1_r a), <- (Z.mul_1_r a').
  rewrite <- (Z.mul_mod_idemp_r a), <- (Z.mul_mod_idemp_r a') by lia.
  destruct (rel_prime_bezout _ _ rel).
  rewrite <- H.
  rewrite !Z.mul_mod_idemp_r by auto.
  rewrite !Z.mul_add_distr_l, !Z.mul_assoc.
  rewrite !Z_mod_plus_full.
  replace (a * u * r) with (a * r * u) by lia.
  replace (a' * u * r) with (a' * r * u) by lia.
  rewrite <- Z.mul_mod_idemp_l, <- (Z.mul_mod_idemp_l (a' * r)) by auto.
  now rewrite eq.
Qed.

Fixpoint prod (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * prod xs
  end.

Instance prod_perm_proper : Proper (@Permutation Z ==> eq) prod.
Proof.
  intros l l' perm.
  induction perm; cbn.
  - easy.
  - now rewrite IHperm.
  - lia.
  - lia.
Qed.

Lemma rel_prime_prod l n :
  Forall (fun x => rel_prime x n) l ->
  rel_prime (prod l) n.
Proof.
  intros all.
  induction l as [|x xs IH].
  - cbn.
    apply rel_prime_1.
  - cbn.
    inversion all; subst.
    apply rel_prime_sym.
    apply rel_prime_mult;
      apply rel_prime_sym; auto.
Qed.

Lemma euler a n :
  n >= 0 ->
  rel_prime a n ->
  a^(Z.of_nat (totient (Z.to_nat n))) mod n = 1 mod n.
Proof.
  destruct (Z.eqb_spec n 0) as [->|?].
  { now rewrite !Zmod_0_r. }

  intros ge0 relan.
  set (rprimes := rel_primes (Z.to_nat n)).
  assert (Permutation (map (fun ai => ai * a mod n) rprimes) rprimes).
  {
    symmetry.
    apply NoDup_Permutation.
    - apply NoDup_rel_primes.
    - apply NoDup_map; [apply NoDup_rel_primes|].
      intros.
      apply In_rel_primes in H.
      apply In_rel_primes in H0.
      destruct H as [_ H], H0 as [_ H0].
      rewrite !Z2Nat.id in * by lia.
      rewrite <- (Z.mod_small a0 n), <- (Z.mod_small a' n) by lia.
      now apply (mul_both_r_mod a).
    - intros x.
      split; intros isin.
      + apply in_map_iff.
        destruct (proj1 (In_rel_primes _ _) isin) as [isrelprime bound].
        rewrite Z2Nat.id in * by lia.
        destruct (rel_prime_bezout _ _ relan).
        exists (x * u mod n).
        split.
        * rewrite Z.mul_mod_idemp_l by lia.
          rewrite <- Z.mul_assoc.
          replace (u * a) with (1 + n*(-v)) by lia.
          replace (x * (1 + n * (-v))) with (x + (x * (-v)) * n) by lia.
          rewrite Z_mod_plus_full.
          apply Z.mod_small; lia.
        * apply In_rel_primes.
          rewrite Z2Nat.id by lia.
          split; [|pose proof (Z.mod_pos_bound (x * u) n); lia].
          apply rel_prime_mod; [lia|].
          apply rel_prime_sym.
          apply rel_prime_mult; [now apply rel_prime_sym|].
          apply rel_prime_sym.
          apply bezout_rel_prime.
          apply (Bezout_intro u n 1 a v).
          lia.
      + apply in_map_iff in isin.
        destruct isin as [x' [<- inx']].
        apply In_rel_primes.
        apply In_rel_primes in inx'.
        rewrite Z2Nat.id in * by lia.
        split; [|pose proof (Z.mod_pos_bound (x' * a) n); lia].
        apply rel_prime_mod; [lia|].
        now
          apply rel_prime_sym, rel_prime_mult;
          apply rel_prime_sym.
  }

  unfold totient.
  apply (mul_both_r_mod (prod rprimes)).
  {
    apply rel_prime_prod.
    apply Forall_forall.
    intros x xin.
    apply In_rel_primes in xin.
    now rewrite Z2Nat.id in xin by lia.
  }

  rewrite Z.mul_1_l.
  subst rprimes; cbn.
  rewrite <- H at 3.
  clear -n0.
  induction (rel_primes (Z.to_nat n)) as [|x xs IH]; [easy|].
  cbn.
  rewrite Z.pow_pos_fold.
  rewrite Zpos_P_of_succ_nat.
  rewrite <- Z.add_1_r.
  rewrite Z.pow_add_r by lia.
  replace (a ^ Z.of_nat (length xs) * a^1 * (x * prod xs))
    with (x * a * (a ^ Z.of_nat (length xs) * prod xs))
    by lia.
  rewrite Z.mul_mod by auto.
  rewrite IH.
  now rewrite Z.mul_mod_idemp_r by auto.
Qed.

Lemma prime_rel_primes p :
  prime p ->
  rel_primes (Z.to_nat p) = map Z.of_nat (seq 1 (Z.to_nat p - 1)).
Proof.
  intros isprime.
  pose proof (prime_ge_2 _ isprime).
  assert (0 < Z.to_nat p)%nat.
  { apply Nat2Z.inj_lt; cbn; rewrite Z2Nat.id; lia. }
  unfold rel_primes.
  replace (Z.to_nat p) with (1 + (Z.to_nat p - 1))%nat at 1 by lia.
  rewrite seq_app.
  cbn.
  rewrite Z2Nat.id by lia.
  destruct (Z.eqb_spec (Z.abs p) 1); [lia|].
  rewrite filter_map.
  rewrite filter_all; [easy|].
  intros a ain.
  apply Z.eqb_eq, Zgcd_1_rel_prime, rel_prime_le_prime; auto.
  apply in_seq in ain.
  split; [lia|].
  apply Z2Nat.inj_lt.
  - lia.
  - lia.
  - rewrite Nat2Z.id.
    lia.
Qed.

Lemma prime_totient p :
  prime p -> Z.of_nat (totient (Z.to_nat p)) = p - 1.
Proof.
  intros isprime.
  pose proof (prime_ge_2 _ isprime).
  unfold totient.
  rewrite prime_rel_primes by auto.
  rewrite map_length, seq_length.
  rewrite Nat2Z.inj_sub; cycle 1.
  { apply Nat2Z.inj_le; rewrite Z2Nat.id; lia. }
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Corollary fermat a p :
  prime p ->
  a mod p <> 0 ->
  a^(p - 1) mod p = 1.
Proof.
  intros isprime ap0.
  pose proof (prime_ge_2 _ isprime).
  rewrite <- (Z.mod_1_l p) at 2 by lia.
  rewrite <- prime_totient by auto.
  apply euler; [lia|].
  apply rel_prime_sym, prime_rel_prime; auto.
  intros pdividea.
  contradiction ap0.
  now apply Zdivide_mod.
Qed.
