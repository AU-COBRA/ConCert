From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
Import ListNotations.

Local Open Scope Z.

Fixpoint egcd_aux
        (n : nat)
        (r0 a0 b0 r1 a1 b1 : Z) {struct n} : Z * Z :=
  match n with
  | 0%nat => (0, 0)
  | S n => let (q, r) := Z.div_eucl r0 r1 in
           if r =? 0 then
             (a1, b1)
           else
             egcd_aux n r1 a1 b1 r (a0 - q*a1) (b0 - q*b1)
  end.

(* returns (x, y) such that x*m + y*n = Z.gcd(x, y) *)
Definition egcd (m n : Z) : Z * Z :=
  if m =? 0 then
    (0, Z.sgn n)
  else if n =? 0 then
    (Z.sgn m, 0)
  else
    let num_steps := S (Z.to_nat (Z.log2 (Z.abs m) + Z.log2 (Z.abs n))) in
    if Z.abs m <? Z.abs n then
      let (x, y) := egcd_aux num_steps (Z.abs n) 1 0 (Z.abs m) 0 1 in
      (Z.sgn m * y, Z.sgn n * x)
    else
      let (x, y) := egcd_aux num_steps (Z.abs m) 1 0 (Z.abs n) 0 1 in
      (Z.sgn m * x, Z.sgn n * y).

Lemma egcd_aux_spec m n steps r0 a0 b0 r1 a1 b1 :
  Z.log2 r0 + Z.log2 r1 < Z.of_nat steps ->
  0 < r1 ->
  r1 <= r0 ->
  r0 = a0*m + b0*n ->
  r1 = a1*m + b1*n ->
  Z.gcd r0 r1 = Z.gcd m n ->
  let (x, y) := egcd_aux steps r0 a0 b0 r1 a1 b1 in
  x*m + y*n = Z.gcd m n.
Proof.
  revert r0 a0 b0 r1 a1 b1.
  induction steps as [|steps IH];
    intros r0 a0 b0 r1 a1 b1 enough_steps r1pos r1gt r0eq r1eq is_gcd.
  {
    cbn -[Z.add] in enough_steps.
    pose proof (Z.log2_nonneg r0).
    pose proof (Z.log2_nonneg r1).
    lia.
  }
  cbn.
  pose proof (Z_div_mod r0 r1 ltac:(lia)).
  destruct (Z.div_eucl r0 r1) as [q r].
  destruct (Z.eqb_spec r 0) as [->|?].
  - destruct H.
    rewrite Z.add_0_r in *.
    rewrite <- r1eq.
    rewrite <- is_gcd.
    rewrite H.
    rewrite Z.gcd_comm.
    now rewrite Z.gcd_mul_diag_l by lia.
  - apply IH; auto.
    + destruct H.
      destruct q; try lia; cycle 1.
      {
        pose proof (Z.mul_pos_neg r1 (Z.neg p) ltac:(lia) ltac:(lia)).
        lia.
      }
      assert (r + r1 <= r0).
      {
        enough (r1 <= r1 * Z.pos p) by lia.
        apply Z.le_mul_diag_r; lia.
      }
      assert (Z.log2 r1 + Z.log2 r < Z.log2 r0 + Z.log2 r1).
      {
        enough (Z.log2 r < Z.log2 r0) by lia.
        pose proof (Z.log2_le_mono (r*2^1) r0 ltac:(lia)).
        rewrite <- Z.shiftl_mul_pow2 in H2 by lia.
        rewrite Z.log2_shiftl in H2 by lia.
        lia.
      }
      lia.
    + lia.
    + lia.
    + rewrite !Z.mul_sub_distr_r.
      replace (a0 * m - q * a1 * m + (b0 * n - q * b1 * n))
        with (a0 * m + b0*n + (-1) * (q*(a1*m + b1*n)))
        by lia.
      rewrite <- r0eq, <-r1eq.
      lia.
    + rewrite <- is_gcd.
      rewrite (proj1 H).
      rewrite (Z.gcd_comm (r1 * q + r)).
      rewrite Z.add_comm, Z.mul_comm.
      now rewrite Z.gcd_add_mult_diag_r.
Qed.

Lemma egcd_spec m n :
  let (x, y) := egcd m n in
  m*x + n*y = Z.gcd m n.
Proof.
  unfold egcd.
  destruct (Z.eqb_spec m 0) as [->|?].
  { apply Z.sgn_abs. }
  destruct (Z.eqb_spec n 0) as [->|?].
  { rewrite Z.gcd_0_r, Z.add_0_r; apply Z.sgn_abs. }
  pose proof (Z.log2_nonneg (Z.abs m)).
  pose proof (Z.log2_nonneg (Z.abs n)).
  destruct (Z.ltb_spec (Z.abs m) (Z.abs n)).
  - unshelve epose proof (egcd_aux_spec
                            (Z.abs n) (Z.abs m)
                            (S (Z.to_nat (Z.log2 (Z.abs m) + Z.log2 (Z.abs n))))
                            (Z.abs n) 1 0
                            (Z.abs m) 0 1
                            _ _ _ _ _ _).
    + rewrite Nat2Z.inj_succ.
      rewrite Z2Nat.id by lia.
      lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct (egcd_aux _ _ _ _ _ _ _).
      rewrite !Z.mul_assoc.
      rewrite Z.gcd_abs_l, Z.gcd_comm, Z.gcd_abs_l in H2.
      rewrite !Z.sgn_abs.
      lia.
  - unshelve epose proof (egcd_aux_spec
                            (Z.abs m) (Z.abs n)
                            (S (Z.to_nat (Z.log2 (Z.abs m) + Z.log2 (Z.abs n))))
                            (Z.abs m) 1 0
                            (Z.abs n) 0 1
                            _ _ _ _ _ _).
    + rewrite Nat2Z.inj_succ.
      rewrite Z2Nat.id by lia.
      lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct (egcd_aux _ _ _ _ _ _ _).
      rewrite !Z.mul_assoc.
      rewrite Z.gcd_abs_l, Z.gcd_comm, Z.gcd_abs_l, Z.gcd_comm in H2.
      rewrite !Z.sgn_abs.
      lia.
Qed.

Lemma mul_fst_egcd a n :
  rel_prime a n ->
  a * fst (egcd a n) mod n = 1 mod n.
Proof.
  destruct (Z.eqb_spec n 0) as [->|?].
  { intros; now rewrite !Zmod_0_r. }
  intros relprime.
  pose proof (egcd_spec a n).
  destruct (egcd a n) as [x y]; cbn.
  rewrite (proj2 (Zgcd_1_rel_prime _ _) relprime) in H.
  replace (a * x) with (1  + (-y)*n) by lia.
  rewrite <- Z.add_mod_idemp_r by lia.
  now rewrite Z.mod_mul, Z.add_0_r by lia.
Qed.

Lemma egcd_divides a b :
  b <> 0 ->
  (b | a) ->
  egcd a b = (0, Z.sgn b).
Proof.
  intros b0 divides.
  unfold egcd.
  destruct (Z.eqb_spec a 0) as [->|a0]; [easy|].
  rewrite (proj2 (Z.eqb_neq _ _) b0).
  assert (Z.abs b <= Z.abs a) by (apply Zdivide_bounds; auto).
  replace (Z.abs a <? Z.abs b) with false; cycle 1.
  { now symmetry; apply Z.ltb_ge. }
  cbn.
  pose proof (Z_div_mod_full (Z.abs a) (Z.abs b) ltac:(lia)).
  destruct (Z.div_eucl (Z.abs a) (Z.abs b)) as [q r].
  rewrite (Zmod_unique_full _ _ _ _ (proj2 H0) (proj1 H0)).
  apply Z.divide_abs_l, Z.divide_abs_r in divides.
  rewrite (Zdivide_mod _ _ divides).
  cbn.
  now rewrite Z.mul_0_r, Z.mul_1_r.
Qed.
