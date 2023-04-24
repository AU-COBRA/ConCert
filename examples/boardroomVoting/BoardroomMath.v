From Coq Require Import Morphisms.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
From Coq Require Import SetoidTactics.
From Coq Require Import Field.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coq Require Import List.
From Bignums Require Import BigZ.
From ConCert.Examples.BoardroomVoting Require Import Egcd.
From ConCert.Examples.BoardroomVoting Require Import Euler.
From ConCert.Utils Require Import Extras.
Import ListNotations.

Local Open Scope Z.

Class BoardroomAxioms {A : Type} :=
  {
    elmeq : A -> A -> Prop;
    elmeqb : A -> A -> bool;
    elmeqb_spec x y : Bool.reflect (elmeq x y) (elmeqb x y);
    zero : A;
    one : A;

    add : A -> A -> A;
    mul : A -> A -> A;

    opp : A -> A;
    inv : A -> A;
    pow : A -> Z -> A;

    order : Z;
    expeq e e' := e mod (order - 1) = e' mod (order - 1);

    order_ge_2 : order >= 2;

    elmeq_equiv :: Equivalence elmeq;
    add_proper :: Proper (elmeq ==> elmeq ==> elmeq) add;
    mul_proper :: Proper (elmeq ==> elmeq ==> elmeq) mul;
    opp_proper :: Proper (elmeq ==> elmeq) opp;
    inv_proper :: Proper (elmeq ==> elmeq) inv;
    pow_base_proper :: Proper (elmeq ==> eq ==> elmeq) pow;
    pow_exp_proper a :
      ~(elmeq a zero) -> Proper (expeq ==> elmeq) (pow a);

    one_neq_zero : ~(elmeq one zero);

    add_comm a b : elmeq (add a b) (add b a);
    add_assoc a b c : elmeq (add a (add b c)) (add (add a b) c);

    mul_comm a b : elmeq (mul a b) (mul b a);
    mul_assoc a b c : elmeq (mul a (mul b c)) (mul (mul a b) c);

    add_0_l a : elmeq (add zero a) a;
    mul_0_l a : elmeq (mul zero a) zero;
    mul_1_l a : elmeq (mul one a) a;

    opp_inv_l a : elmeq (add (opp a) a) zero;
    inv_inv_l a : ~(elmeq a zero) -> elmeq (mul (inv a) a) one;

    mul_add a b c : elmeq (mul (add a b) c) (add (mul a c) (mul b c));

    pow_0_r a :
      ~(elmeq a zero) ->
      elmeq (pow a 0) one;

    pow_1_r a : elmeq (pow a 1) a;

    pow_opp_1 a :
      ~(elmeq a zero) ->
      elmeq (pow a (-1)) (inv a);

    pow_plus a e e' :
      ~(elmeq a zero) ->
      elmeq (pow a (e + e')) (mul (pow a e) (pow a e'));

    pow_pow a b e :
      ~(elmeq a zero) ->
      elmeq (pow (pow a b) e)
            (pow a (b * e)%Z);

    pow_nonzero a e :
      ~(elmeq a zero) ->
      ~(elmeq (pow a e) zero);

    inv_nonzero a :
      ~(elmeq a zero) ->
      ~(elmeq (inv a) zero);
  }.

Arguments BoardroomAxioms : clear implicits.

Declare Scope broom.
Declare Scope broom_scope.
Delimit Scope broom_scope with broom.

Module BoardroomMathNotations.
  Infix "==" := elmeq (at level 70) : broom.
  Infix "=?" := elmeqb (at level 70) : broom.
  Notation "a !== b" := (~(elmeq a b)) (at level 70) : broom.
  Notation "0" := zero : broom.
  Notation "1" := one : broom.
  Infix "+" := add : broom.
  Infix "*" := mul : broom.
  Infix "^" := pow : broom.
  Notation "a 'exp=' b" := (expeq a b) (at level 70) : broom.
  Notation "a 'exp<>' b" := (~(expeq a b)) (at level 70) : broom.
End BoardroomMathNotations.

Export BoardroomMathNotations.
Local Open Scope broom.

Global Instance oeq_equivalence {A : Type}
                                (field : BoardroomAxioms A)
                                : Equivalence expeq.
Proof.
  unfold expeq.
  constructor.
  - constructor.
  - repeat intro; auto.
  - now intros ? ? ? -> ->.
Qed.

Definition BoardroomAxioms_field_theory {A : Type} (field : BoardroomAxioms A) :
  field_theory
    0 1
    add mul
    (fun x y => x + (opp y)) opp
    (fun x y => x * inv y) inv
    elmeq.
Proof.
  constructor; [constructor| | |].
  - apply add_0_l.
  - apply add_comm.
  - apply add_assoc.
  - apply mul_1_l.
  - apply mul_comm.
  - apply mul_assoc.
  - apply mul_add.
  - reflexivity.
  - intros x. rewrite add_comm. apply opp_inv_l.
  - apply one_neq_zero.
  - reflexivity.
  - apply inv_inv_l.
Qed.

Class Generator {A : Type} (field : BoardroomAxioms A) :=
  {
    generator : A;
    generator_nonzero : generator !== 0;
    generator_generates a : a !== 0 -> exists! e, 0 <= e < order - 1 /\ generator^e == a;
  }.

Class DiscreteLog {A : Type} (field : BoardroomAxioms A) (g : Generator field) :=
  {
    (* This is computationally intractable, but we still require it for ease of specification *)
    log : A -> Z;
    log_proper :: Proper (elmeq ==> expeq) log;
    pow_log a :
      a !== 0 ->
      generator ^ (log a) == a;

    log_1_l : log 1 exp= 0%Z;
    log_mul a b :
      a !== 0 ->
      b !== 0 ->
      log (a * b) exp= log a + log b;

    log_inv a : log (inv a) exp= -log a;
    log_generator : log generator = 1%Z;
  }.

Section WithBoardroomAxioms.
  Context {A : Type}.
  Context {field : BoardroomAxioms A}.
  Context {gen : Generator field}.
  Context {disc_log : DiscreteLog field gen}.

  Fixpoint prod (l : list A) : A :=
    match l with
    | [] => one
    | x :: xs => x * prod xs
    end.

  Definition compute_public_key (sk : Z) : A :=
    generator ^ sk.

  Definition reconstructed_key (pks : list A) (n : nat) : A :=
    let lprod := prod (firstn n pks) in
    let rprod := inv (prod (skipn (S n) pks)) in
    lprod * rprod.

  Definition compute_public_vote (rk : A) (sk : Z) (sv : bool) : A :=
    rk ^ sk * if sv then generator else 1.

  Fixpoint bruteforce_tally_aux
           (n : nat)
           (votes_product : A) : option nat :=
    if generator ^ (Z.of_nat n) =? votes_product then
      Some n
    else
      match n with
      | 0 => None
      | S n => bruteforce_tally_aux n votes_product
      end%nat.

  Definition bruteforce_tally (votes : list A) : option nat :=
    bruteforce_tally_aux (length votes) (prod votes).

  Add Field ff : (BoardroomAxioms_field_theory field).

  Local Open Scope broom.

  Hint Resolve one_neq_zero pow_nonzero generator_nonzero inv_nonzero : core.

  Instance plus_expeq_proper : Proper (expeq ==> expeq ==> expeq) Z.add.
  Proof.
    intros x x' xeq y y' yeq.
    unfold "exp=" in *.
    assert (order - 1 <> 0)%Z by (pose proof order_ge_2; lia).
    now rewrite Z.add_mod, xeq, yeq, <- Z.add_mod.
  Qed.

  Instance mul_expeq_proper : Proper (expeq ==> expeq ==> expeq) Z.mul.
  Proof.
    intros x x' xeq y y' yeq.
    unfold "exp=" in *.
    assert (order - 1 <> 0)%Z by (pose proof order_ge_2; lia).
    now rewrite Z.mul_mod, xeq, yeq, <- Z.mul_mod.
  Qed.

  Instance sub_expeq_proper : Proper (expeq ==> expeq ==> expeq) Z.sub.
  Proof.
    intros x x' xeq y y' yeq.
    unfold "exp=" in *.
    assert (order - 1 <> 0)%Z by (pose proof order_ge_2; lia).
    now rewrite Zminus_mod, xeq, yeq, <- Zminus_mod.
  Qed.

  Instance opp_expeq_proper : Proper (expeq ==> expeq) Z.opp.
  Proof.
    intros x x' xeq.
    rewrite <- !Z.sub_0_l.
    now rewrite xeq.
  Qed.

  Lemma log_pow a e :
    a !== 0 ->
    log (a ^ e) exp= e * log a.
  Proof.
    intros anz.
    induction e using Z.peano_ind.
    - rewrite pow_0_r; auto.
      apply log_1_l.
    - replace (Z.succ e) with (e + 1)%Z by lia.
      rewrite pow_plus by auto.
      rewrite log_mul; auto.
      rewrite IHe.
      replace ((e + 1) * log a)%Z with (e * log a + log a)%Z by lia.
      now rewrite pow_1_r.
    - replace (Z.pred e) with (e + (-1))%Z by lia.
      rewrite pow_plus by auto.
      rewrite log_mul by auto.
      rewrite IHe.
      rewrite (pow_opp_1 a) by auto.
      rewrite log_inv.
      now replace ((e + -1) * log a)%Z with (e * log a + - log a)%Z by lia.
  Qed.

  Instance pow_generator_proper : Proper (expeq ==> elmeq) (pow generator) :=
    pow_exp_proper _ generator_nonzero.

  Lemma log_both a b :
    a !== 0 ->
    b !== 0 ->
    log a exp= log b ->
    a == b.
  Proof.
    intros an0 bn0 dleq.
    assert (generator ^ log a == generator ^ log a) as H by reflexivity.
    rewrite dleq in H at 1.
    now rewrite !pow_log in H by auto.
  Qed.

  Lemma log_pow_generator e :
    log (generator ^ e) exp= e.
  Proof.
    rewrite log_pow; auto.
    rewrite log_generator.
    now rewrite Z.mul_1_r.
  Qed.

  Lemma int_domain a b :
    a !== 0 ->
    b !== 0 ->
    a * b !== 0.
  Proof.
    intros an0 bn0.
    apply (@field_is_integral_domain
             A
             0 1
             add
             mul
             (fun a b => a + (opp b))
             opp
             (fun a b => a * (inv b))
             inv); eauto.
    - typeclasses eauto.
    - constructor; typeclasses eauto.
    - apply F2AF.
      + typeclasses eauto.
      + constructor; typeclasses eauto.
      + apply (BoardroomAxioms_field_theory field).
  Qed.

  Hint Resolve int_domain : core.

  Lemma prod_units (xs : list A) :
    All (fun x => x !== 0) xs <-> prod xs !== 0.
  Proof.
    induction xs as [|x xs IH]; cbn in *; auto.
    - split; auto.
    - split.
      + intros [].
        apply int_domain; auto.
        now apply IH.
      + intros xprod.
        split.
        * intros eq; rewrite eq in *; rewrite mul_0_l in xprod.
          destruct (xprod ltac:(reflexivity)).
        * apply IH.
          intros eq; rewrite eq in *; rewrite mul_comm, mul_0_l in xprod.
          destruct (xprod ltac:(reflexivity)).
  Qed.

  Hint Resolve -> prod_units : core.
  Hint Resolve <- prod_units : core.

  Lemma compute_public_key_unit sk :
    compute_public_key sk !== 0.
  Proof. apply pow_nonzero, generator_nonzero. Qed.

  Hint Resolve compute_public_key_unit : core.

  Lemma compute_public_keys_units sks :
    All (fun x => x !== 0) (map compute_public_key sks).
  Proof.
    induction sks as [|sk sks IH]; cbn; auto.
  Qed.

  Hint Resolve compute_public_keys_units : core.

  Lemma reconstructed_key_unit pks i :
    All (fun a => a !== 0) pks ->
    reconstructed_key pks i !== 0.
  Proof.
    intros all.
    unfold reconstructed_key.
    apply int_domain.
    - apply prod_units.
      apply (all_incl (firstn i pks) pks); auto.
      apply firstn_incl.
    - apply inv_nonzero.
      apply prod_units.
      apply (all_incl (skipn (S i) pks) pks); auto.
      apply skipn_incl.
  Qed.

  Lemma compute_public_vote_unit rk sk sv :
    rk !== 0 ->
    compute_public_vote rk sk sv !== 0.
  Proof.
    intros rk_unit.
    unfold compute_public_vote.
    destruct sv; auto.
  Qed.

  Hint Resolve
          compute_public_key_unit compute_public_keys_units
          reconstructed_key_unit compute_public_vote_unit : core.

  Lemma log_prod (l : list A) :
    All (fun a => a !== 0) l ->
    log (prod l) exp= sumZ log l.
  Proof.
    intros all.
    induction l as [|x xs IH]; cbn in *.
    - now rewrite log_1_l.
    - specialize (IH (proj2 all)).
      destruct all.
      rewrite log_mul by auto.
      now rewrite IH.
  Qed.

  Lemma prod_firstn_units n l :
    prod l !== 0 ->
    prod (firstn n l) !== 0.
  Proof.
    intros prodl.
    apply prod_units.
    pose proof (firstn_incl n l).
    apply all_incl with l; auto.
  Qed.

  Hint Resolve prod_firstn_units : core.

  Lemma prod_skipn_units n l :
    prod l !== 0 ->
    prod (skipn n l) !== 0.
  Proof.
    intros prodl.
    apply prod_units.
    pose proof (skipn_incl n l).
    apply all_incl with l; auto.
  Qed.

  Hint Resolve prod_skipn_units : core.

  Local Open Scope Z.
  Lemma sum_lemma l :
    sumZ (fun i => nth i l 0 *
                   (sumZ id (firstn i l) -
                    sumZ id (skipn (S i) l)))
         (seq 0 (length l)) = 0.
  Proof.
    rewrite (sumZ_seq_feq
               (fun i => sumZ (fun j => if Nat.ltb j i then nth i l 0 * nth j l 0 else 0)
                              (seq 0 (length l)) -
                         sumZ (fun j => if Nat.ltb i j then nth i l 0 * nth j l 0 else 0)
                              (seq 0 (length l))));
      cycle 1.
    {

      intros i ?.
      rewrite Z.mul_sub_distr_l.
      rewrite 2!sumZ_mul.
      unfold id.
      rewrite (sumZ_firstn 0) by (right; lia).
      rewrite (sumZ_skipn 0).
      apply f_equal2.
      - rewrite (sumZ_seq_split i) by lia.
        rewrite Z.add_comm.
        cbn -[Nat.ltb].
        rewrite sumZ_seq_n.
        rewrite (sumZ_seq_feq (fun _ => 0)); cycle 1.
        { intros j jlt. destruct (Nat.ltb_spec (j + i) i); auto; lia. }
        rewrite sumZ_zero.
        cbn -[Nat.ltb].
        apply sumZ_seq_feq.
        intros j jlt.
        destruct (Nat.ltb_spec j i); lia.
      - rewrite (sumZ_seq_split (S i)) by lia.
        rewrite (sumZ_seq_feq (fun _ => 0)); cycle 1.
        { intros j jlt. destruct (Nat.ltb_spec i j); auto; lia. }
        rewrite sumZ_zero.
        cbn.
        rewrite sumZ_seq_n.
        replace (length l - S i)%nat with (length l - i - 1)%nat by lia.
        apply sumZ_seq_feq.
        intros j jlt.
        replace (j + S i)%nat with (S (i + j))%nat by lia.
        destruct (Nat.leb_spec i (i + j)); lia.
    }

    rewrite sumZ_sub.
    rewrite sumZ_sumZ_swap.
    match goal with
    | [|- ?a - ?b = 0] => enough (a = b) by lia
    end.
    apply sumZ_seq_feq.
    intros i ilt.
    apply sumZ_seq_feq.
    intros j jlt.
    destruct (i <? j)%nat; lia.
  Qed.

  Local Open Scope broom.
  Lemma mul_public_votes
        (sks : list Z)
        (votes : nat -> bool) :
    prod (map (fun (i : nat) =>
                 compute_public_vote
                   (reconstructed_key (map compute_public_key sks) i)
                   (nth i sks 0%Z)
                   (votes i))
                 (seq 0 (length sks)))
    == generator ^ sumZ (fun i => if votes i then 1 else 0)%Z (seq 0 (length sks)).
  Proof.
    apply log_both; auto.
    - induction (seq 0 (length sks)); cbn; auto.
    - rewrite log_pow_generator, log_prod; cycle 1.
      {
        induction (seq 0 (length sks)); cbn; auto.
      }

      rewrite sumZ_map.
      unfold compute_public_vote.
      etransitivity.
      {
        apply sumZ_seq_feq_rel; try typeclasses eauto.
        intros i ilt.
        rewrite log_mul at 1 by (destruct (votes i); auto).
        setoid_replace (log (if votes i then generator else 1))
          with (if votes i then 1%Z else 0%Z) at 1;
          cycle 1.
        - destruct (votes i).
          + rewrite <- (pow_1_r generator).
            apply log_pow_generator.
          + apply log_1_l.
        - rewrite log_pow at 1 by auto.
          unfold reconstructed_key.
          rewrite log_mul at 1 by auto.
          rewrite log_prod at 1 by auto.
          rewrite log_inv at 1.
          rewrite log_prod at 1 by auto.
          rewrite 2!(sumZ_map_id log) at 1.
          rewrite firstn_map, skipn_map, !map_map.
          unfold compute_public_key.
          assert (forall l, sumZ id (map (fun x => log (generator ^ x)) l) exp= sumZ id l).
          { clear.
            intros l.
            induction l; cbn; auto.
            - reflexivity.
            - unfold id at 1 3.
              rewrite log_pow_generator.
              now rewrite IHl.
          }
          rewrite 2!H at 1.
          rewrite Z.add_opp_r.
          reflexivity.
      }

      rewrite sumZ_add.
      rewrite sum_lemma.
      reflexivity.
  Qed.

  Global Instance prod_perm_proper :
    Proper (@Permutation A ==> elmeq) prod.
  Proof.
    intros l l' permeq.
    induction permeq.
    - reflexivity.
    - cbn.
      now rewrite IHpermeq.
    - cbn.
      rewrite !mul_assoc.
      now rewrite (mul_comm y).
    - now rewrite IHpermeq1, IHpermeq2.
  Qed.

  Global Instance bruteforce_tally_aux_proper :
    Proper (eq ==> elmeq ==> eq) bruteforce_tally_aux.
  Proof.
    intros n ? <- p p' prodeq.
    induction n as [|n IH].
    - cbn.
      destruct (elmeqb_spec (generator^0) p),
               (elmeqb_spec (generator^0) p'); auto.
      + rewrite prodeq in e; contradiction.
      + rewrite <- prodeq in e; contradiction.
    - cbn.
      destruct (elmeqb_spec (generator^Z.pos (Pos.of_succ_nat n)) p),
               (elmeqb_spec (generator^Z.pos (Pos.of_succ_nat n)) p'); auto.
      + rewrite prodeq in e; contradiction.
      + rewrite <- prodeq in e; contradiction.
  Qed.

  Global Instance bruteforce_tally_proper :
    Proper (@Permutation A ==> eq) bruteforce_tally.
  Proof.
    unfold bruteforce_tally.
    now intros ? ? <-.
  Qed.

  Global Instance elmeqb_elmeq_proper :
    Proper (elmeq ==> elmeq ==> eq) elmeqb.
  Proof.
    intros x x' xeq y y' yeq.
    destruct (elmeqb_spec x y), (elmeqb_spec x' y'); auto.
    - contradiction n.
      now rewrite <- xeq, <- yeq.
    - contradiction n.
      now rewrite xeq, yeq.
  Qed.

  Lemma elmeqb_refl a :
    a =? a = true.
  Proof.
    destruct (elmeqb_spec a a); [easy|].
    contradiction n.
    reflexivity.
  Qed.

  Lemma bruteforce_tally_aux_correct result max :
    Z.of_nat max < order - 1 ->
    (result <= max)%nat ->
    bruteforce_tally_aux max (generator ^ Z.of_nat result) = Some result.
  Proof.
    intros max_lt result_le.
    induction max as [|max IH].
    - replace result with 0%nat by lia.
      cbn.
      now rewrite elmeqb_refl.
    - destruct (Nat.eq_dec result (S max)) as [->|?].
      + cbn.
        now rewrite elmeqb_refl.
      + cbn -[Z.of_nat].
        destruct (elmeqb_spec (generator ^ Z.of_nat (S max))
                              (generator ^ Z.of_nat result)) as [eq|?]; auto.
        * pose proof (generator_generates (generator ^ Z.of_nat result) ltac:(auto)).
          destruct H as [e [sat unique]].
          unshelve epose proof (unique (Z.of_nat (S max)) _) as smax.
          { split; auto; lia. }
          unshelve epose proof (unique (Z.of_nat result) _) as res.
          { split; [lia|reflexivity]. }
          rewrite <- (Z2Nat.id e) in smax, res by lia.
          apply Nat2Z.inj in smax.
          apply Nat2Z.inj in res.
          congruence.
        * apply IH; lia.
  Qed.

  Lemma sumZ_sumnat_votes (svs : nat -> bool) l :
    sumZ (fun i => if svs i then 1%Z else 0%Z) l =
    Z.of_nat (sumnat (fun i => if svs i then 1%nat else 0%nat) l).
  Proof.
    induction l as [|x xs IH]; auto.
    cbn.
    rewrite IH, Nat2Z.inj_add.
    destruct (svs x); lia.
  Qed.

  Lemma bruteforce_tally_correct
        {B}
        (bs : list B)
        (index : B -> nat)
        (sks : B -> Z)
        (pks : list A)
        (svs : B -> bool)
        (pvs : B -> A) :
    Z.of_nat (length bs) < order - 1 ->
    Permutation (map index bs) (seq 0 (length bs)) ->
    length pks = length bs ->
    (forall b, In b bs -> nth_error pks (index b) = Some (compute_public_key (sks b))) ->
    (forall b, In b bs -> pvs b = compute_public_vote
                                    (reconstructed_key pks (index b))
                                    (sks b)
                                    (svs b)) ->
    bruteforce_tally (map pvs bs) =
    Some (sumnat (fun b => if svs b then 1 else 0)%nat bs).
  Proof.
    intros countlt perm len_pks pks_sks pvs_svs.
    set (geti i := find (fun b => index b =? i)%nat bs).
    set (sks_list := map (fun i => match geti i with
                                   | Some x => sks x
                                   | None => 0%Z
                                   end)
                         (seq 0 (length bs))).
    set (svsi i := match geti i with
                   | Some x => svs x
                   | None => false
                   end).
    pose proof (mul_public_votes sks_list svsi).
    assert (geti_i: forall b i,
               In b bs ->
               index b = i ->
               geti i = Some b).
    {
      clear -perm.
      intros b i isin index_eq.
      pose proof (seq_NoDup (length bs) 0).
      rewrite <- perm in H.
      clear perm.
      subst geti.
      cbn.
      induction bs as [|b' bs IH]; cbn in *; try easy.
      destruct isin as [<-|?].
      - now rewrite index_eq, Nat.eqb_refl.
      - inversion H; subst.
        destruct (Nat.eqb_spec (index b') (index b)).
        + rewrite e in H.
          apply (in_map index) in H0.
          rewrite <- e in H0.
          contradiction.
        + inversion H; apply IH; auto.
    }

    assert (map_on_bs:
              forall {C} (f : B -> C) (def : C),
                Permutation (map f bs)
                            (map (fun i => match geti i with
                                           | Some b => f b
                                           | None => def
                                           end) (seq 0 (length bs)))).
    {
      intros C f def.
      rewrite <- perm.
      rewrite map_map.
      match goal with
      | [|- Permutation ?l ?l'] => enough (l = l') as eq by (now rewrite eq)
      end.
      apply map_ext_in.
      intros b inbbs.
      now rewrite geti_i with (b := b) by auto.
    }

    assert (Permutation
              (map (fun i : nat =>
                      compute_public_vote
                        (reconstructed_key
                           (map compute_public_key sks_list) i)
                        (nth i sks_list 0%Z) (svsi i))
                   (seq 0 (length sks_list)))
              (map pvs bs))%nat.
    {
      rewrite (map_on_bs _ pvs 0).
      unfold sks_list.
      rewrite map_length, seq_length.
      match goal with
      | [|- Permutation ?l ?l'] => enough (l = l') as eq by (now rewrite eq)
      end.
      apply map_ext_in.
      intros i iin.
      assert (i < length bs)%nat by (apply in_seq in iin; lia).
      rewrite map_nth_alt with (d2 := 0%nat) by (now rewrite seq_length).
      rewrite seq_nth.
      cbn.
      rewrite <- perm in iin.
      apply in_map_iff in iin.
      destruct iin as [b [indexb inbbs]].
      unfold svsi.
      rewrite geti_i with (b := b) by auto.
      rewrite pvs_svs by auto.
      subst i.
      rewrite map_map.
      f_equal.
      - f_equal.
        clear -perm len_pks pks_sks geti_i.
        apply list_eq_nth.
        { now rewrite map_length, seq_length. }
        intros i a a' ntha ntha'.
        assert (isin: In i (seq 0 (length bs))).
        {
          apply in_seq.
          split; try lia.
          rewrite <- len_pks.
          cbn; apply nth_error_Some.
          congruence.
        }
        assert (i < length bs)%nat by (apply in_seq in isin; lia).
        rewrite <- perm in isin.
        apply in_map_iff in isin.
        destruct isin as [b [indexb inbbs]].
        subst i.
        rewrite pks_sks in ntha' by auto.
        rewrite map_nth_error with (d := index b) in ntha by (now rewrite nth_error_seq_in).
        rewrite geti_i with (b := b) in ntha by auto.
        congruence.
      - auto.
    }

    rewrite <- H0.
    unfold bruteforce_tally.
    rewrite map_length, seq_length.
    rewrite mul_public_votes.
    rewrite <- (sumnat_map svs (fun sv => if sv then 1%nat else 0%nat)).
    enough (Permutation (map svs bs) (map svsi (seq 0 (length sks_list)))).
    {
      rewrite H1.
      rewrite sumnat_map.
      rewrite sumZ_sumnat_votes.
      unfold sks_list.
      rewrite map_length, seq_length.
      rewrite bruteforce_tally_aux_correct; auto.
      rewrite <- Nat.mul_1_l.
      rewrite <- (seq_length (length bs) 0) at 2.
      apply sumnat_max.
      intros i iin.
      destruct (svsi i); lia.
    }
    unfold sks_list.
    rewrite map_length, !seq_length.
    rewrite <- perm.
    pose proof (seq_NoDup (length bs) 0).
    rewrite <- perm in H1.
    clear -H1.
    induction bs as [|b bs IH]; auto.
    subst geti svsi; cbn in *.
    rewrite Nat.eqb_refl.
    inversion H1; subst.
    rewrite (map_ext_in _ (fun i => match find (fun b => (index b =? i)%nat) bs with
                                    | Some x => svs x
                                    | None => false
                                    end)); cycle 1.
    {
      intros a ain.
      destruct (Nat.eqb_spec (index b) a); auto.
      subst a; contradiction.
    }
    apply Permutation_cons; auto.
  Qed.

End WithBoardroomAxioms.

Module Zp.
  Local Open Scope Z.

  (* Look at the definition of [mod] in Coq's StdLib, it probably has changed. *)
  Fixpoint mod_pow_pos_aux (a : Z) (x : positive) (m : Z) (r : Z) : Z :=
    match x with
    | x~0%positive => mod_pow_pos_aux (a * a mod m) x m r
    | x~1%positive => mod_pow_pos_aux (a * a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow_pos (a : Z) (x : positive) (m : Z) : Z :=
    mod_pow_pos_aux a x m 1.

  Definition mod_inv (a : Z) (p : Z) : Z :=
    fst (egcd a p) mod p.

  Definition mod_pow (a x p : Z) : Z :=
    match x with
    | Z0 => a ^ 0 mod p
    | Zpos x => mod_pow_pos a x p
    | Zneg x => mod_inv (mod_pow_pos a x p) p
    end.

  Lemma Z_pow_pos_mod_idemp a x m :
    Z.pow_pos (a mod m) x mod m = Z.pow_pos a x mod m.
  Proof.
    destruct (m =? 0) eqn:mzero.
    {
      apply Z.eqb_eq in mzero.
      rewrite mzero.
      now rewrite 3!Zmod_0_r.
    }

    apply Z.eqb_neq in mzero.

    unfold Z.pow_pos.
    assert (H: forall start l x, Pos.iter (Z.mul l) start x = start * Pos.iter (Z.mul l) 1 x).
    {
      clear.
      intros start l x.
      revert start.
      induction x; intros start.
      - cbn.
        rewrite 2!IHx.
        rewrite (IHx (Pos.iter (Z.mul l) 1 x)).
        lia.
      - cbn.
        rewrite 2!IHx.
        rewrite (IHx (Pos.iter (Z.mul l) 1 x)).
        lia.
      - cbn.
        lia.
    }

    induction x.
    - cbn.
      rewrite (H _ (a mod m)).
      rewrite (H _ a).
      rewrite Z.mul_assoc.
      assert (H2: forall a b c,
                 ((a mod m) * b * c) mod m = ((a mod m) * (b mod m) * (c mod m)) mod m).
      {
        clear.
        intros.
        rewrite <- Z.mul_assoc.
        rewrite Zmult_mod_idemp_l.

        rewrite <- Z.mul_assoc.
        rewrite Zmult_mod_idemp_l.

        rewrite 2!Z.mul_assoc.
        rewrite (Z.mul_comm _ (c mod m)).
        rewrite Zmult_mod_idemp_l.
        rewrite Z.mul_assoc.
        rewrite (Z.mul_comm _ (b mod m)).
        rewrite Zmult_mod_idemp_l.
        replace (b * (c * a)) with (a * b * c) by lia; auto.
      }

      rewrite H2.
      rewrite IHx.
      rewrite <- H2.

      rewrite <- Z.mul_assoc.
      now rewrite Zmult_mod_idemp_l.
    - cbn.
      rewrite H.
      rewrite Z.mul_mod by auto.
      rewrite IHx.
      rewrite <- Z.mul_mod by auto.
      now rewrite <- H.
    - cbn.
      rewrite 2!Z.mul_1_r.
      now apply Z.mod_mod.
  Qed.

  Lemma mod_pow_pos_aux_spec a x p r :
    mod_pow_pos_aux a x p r = r * Z.pow_pos a x mod p.
  Proof.
    revert a r.
    induction x; intros a r.
    + cbn -[Z.pow_pos].
      specialize (IHx ((a * a) mod p) ((r * a) mod p)).
      rewrite IHx.
      rewrite <- Zmult_mod_idemp_r by auto.
      rewrite Z_pow_pos_mod_idemp.
      rewrite <- Zmult_mod by auto.
      replace (x~1)%positive with (x*2+1)%positive by lia.
      rewrite Zpower_pos_is_exp.
      cbn.
      rewrite 2!Z.pow_pos_fold.
      rewrite Z.pow_mul_l.
      rewrite <- Z.pow_add_r by (auto with zarith).
      rewrite Zred_factor1.
      cbn.
      f_equal; lia.
    + cbn -[Z.pow_pos].
      rewrite IHx.
      rewrite <- Zmult_mod_idemp_r.
      rewrite Z_pow_pos_mod_idemp.
      rewrite Zmult_mod_idemp_r.
      replace (x~0)%positive with (x*2)%positive by lia.
      rewrite 2!Z.pow_pos_fold.
      rewrite Z.pow_mul_l.
      rewrite <- Z.pow_add_r by (auto with zarith).
      now rewrite Zred_factor1.
    + cbn.
      f_equal; lia.
  Qed.

  Lemma mod_pow_pos_spec a x p :
    mod_pow_pos a x p = Z.pow_pos a x mod p.
  Proof.
    pose proof (mod_pow_pos_aux_spec a x p 1).
    now rewrite Z.mul_1_l in H.
  Qed.

  Lemma Z_pow_mod_idemp a x p :
    (a mod p)^x mod p = a^x mod p.
  Proof.
    destruct x; auto.
    cbn.
    apply Z_pow_pos_mod_idemp.
  Qed.

  Lemma mod_pow_pos_aux_mod_idemp a x p r :
    mod_pow_pos_aux (a mod p) x p r = mod_pow_pos_aux a x p r.
  Proof.
    revert a r.
    induction x; intros a r; cbn in *.
    + rewrite <- Zmult_mod by auto.
      now rewrite Zmult_mod_idemp_r by auto.
    + now rewrite <- Zmult_mod by auto.
    + now rewrite Zmult_mod_idemp_r by auto.
  Qed.

  Lemma mod_pow_pos_mod_idemp a x p :
    mod_pow_pos (a mod p) x p = mod_pow_pos a x p.
  Proof. apply mod_pow_pos_aux_mod_idemp. Qed.

  Lemma mod_pow_mod_idemp a e p :
    mod_pow (a mod p) e p = mod_pow a e p.
  Proof.
    unfold mod_pow.
    destruct e.
    - now rewrite Z_pow_mod_idemp.
    - now rewrite mod_pow_pos_mod_idemp.
    - now rewrite mod_pow_pos_mod_idemp.
  Qed.

  Lemma mod_pow_pos_aux_mod a x p r :
    mod_pow_pos_aux a x p r mod p = mod_pow_pos_aux a x p r.
  Proof.
    rewrite mod_pow_pos_aux_spec.
    now rewrite Zmod_mod by auto.
  Qed.
  Lemma mod_pow_pos_mod a x p :
    mod_pow_pos a x p mod p = mod_pow_pos a x p.
  Proof. apply mod_pow_pos_aux_mod. Qed.
  Lemma mod_inv_mod a p :
    mod_inv a p mod p = mod_inv a p.
  Proof.
    unfold mod_inv.
    now rewrite Zmod_mod.
  Qed.

  Lemma mod_pow_mod a x p :
    mod_pow a x p mod p = mod_pow a x p.
  Proof.
    destruct x; cbn.
    + now rewrite Zmod_mod by auto.
    + now rewrite mod_pow_pos_mod.
    + now rewrite mod_inv_mod.
  Qed.


  Lemma mul_mod_inv a p :
    prime p ->
    a mod p <> 0 ->
    a * mod_inv a p mod p = 1.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    unfold mod_inv.
    rewrite Z.mul_mod_idemp_r by lia.
    rewrite <- (Z.mod_1_l p) by lia.
    apply mul_fst_egcd.
    apply rel_prime_sym, prime_rel_prime; [easy|].
    intros eq; contradiction ap0.
    apply Z.mod_divide; [lia|easy].
  Qed.

  Lemma mod_mul_both_l a b c p :
    prime p ->
    c mod p <> 0 ->
    (c * a mod p = c * b mod p <-> a mod p = b mod p).
  Proof.
    intros isprime cp0.
    pose proof (prime_ge_2 _ isprime).
    split.
    - intros eq.
      rewrite <- (Z.mul_1_l a).
      rewrite <- (Z.mul_1_l b).
      rewrite <- (mul_mod_inv c _ isprime cp0).
      rewrite !Z.mul_mod_idemp_l by lia.
      rewrite (Z.mul_comm c).
      rewrite <- 2!Z.mul_assoc.
      rewrite <- (Z.mul_mod_idemp_r _ (c * a)) by lia.
      rewrite <- (Z.mul_mod_idemp_r _ (c * b)) by lia.
      now rewrite eq.
    - intros eq.
      now rewrite <- Z.mul_mod_idemp_r, eq, Z.mul_mod_idemp_r by lia.
  Qed.

  Lemma mul_mod_nonzero a b p :
    prime p ->
    a mod p <> 0 ->
    b mod p <> 0 ->
    a * b mod p <> 0.
  Proof.
    intros isprime ap0 bp0.
    intros abp0.
    pose proof (prime_ge_2 _ isprime).
    pose proof (proj1 (Z.mod_divide _ p ltac:(lia)) abp0) as pdiv.
    pose proof (prime_mult _ isprime _ _ pdiv) as onediv.
    destruct onediv as [div|div]; apply Z.mod_divide in div; lia.
  Qed.

  #[local]
  Hint Resolve mul_mod_nonzero : core.

  Lemma mod_mod_nonzero a p :
    a mod p <> 0 ->
    (a mod p) mod p <> 0.
  Proof.
    intros ap0.
    rewrite Zmod_mod by auto.
    auto.
  Qed.

  #[local]
  Hint Resolve mod_mod_nonzero : core.

  Lemma mod_pow_pos_aux_nonzero a x p r :
    prime p ->
    a mod p <> 0 ->
    r mod p <> 0 ->
    mod_pow_pos_aux a x p r <> 0.
  Proof.
    intros prime.
    pose proof (prime_ge_2 _ prime).
    revert a r.
    induction x; intros a r ap0 rp0; cbn; auto.
  Qed.

  #[local]
  Hint Resolve mod_pow_pos_aux_nonzero : core.

  Lemma mod_pow_pos_nonzero a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow_pos a x p <> 0.
  Proof.
    intros isprime ap0.
    apply mod_pow_pos_aux_nonzero; auto.
    pose proof (prime_ge_2 _ isprime).
    now rewrite Z.mod_1_l by lia.
  Qed.

  #[local]
  Hint Resolve mod_pow_pos_nonzero : core.

  Lemma mod_inv_nonzero a p :
    prime p ->
    a mod p <> 0 ->
    mod_inv a p <> 0.
  Proof.
    intros isprime ap0 iszero.
    pose proof (prime_ge_2 _ isprime).
    rewrite <- (Z.mod_0_l p) in iszero by lia.
    rewrite <- mod_inv_mod in iszero.
    apply (mod_mul_both_l _ _ a p isprime ap0) in iszero.
    rewrite mul_mod_inv in iszero by auto.
    rewrite Z.mul_0_r, Z.mod_0_l in iszero; easy.
  Qed.

  #[local]
  Hint Resolve mod_inv_nonzero : core.

  Lemma mod_pow_nonzero a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a x p <> 0.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct x; cbn; auto.
    - rewrite Z.mod_1_l by lia; discriminate.
    - apply mod_inv_nonzero; auto.
      rewrite mod_pow_pos_mod; auto.
  Qed.

  #[local]
  Hint Resolve mod_pow_nonzero : core.

  Lemma mod_pow_pos_mod_nonzero a x p :
    mod_pow_pos a x p <> 0 ->
    mod_pow_pos a x p mod p <> 0.
  Proof. rewrite mod_pow_pos_mod; auto. Qed.
  Lemma mod_inv_mod_nonzero a p :
    mod_inv a p <> 0 ->
    mod_inv a p mod p <> 0.
  Proof. rewrite mod_inv_mod; auto. Qed.
  Lemma mod_pow_mod_nonzero a x p :
    mod_pow a x p <> 0 ->
    mod_pow a x p mod p <> 0.
  Proof. rewrite mod_pow_mod; auto. Qed.
  Lemma one_nonzero p :
    prime p ->
    1 mod p <> 0.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    now rewrite Z.mod_1_l by lia.
  Qed.

  #[local]
  Hint Resolve mod_pow_pos_mod_nonzero mod_inv_mod_nonzero mod_pow_mod_nonzero one_nonzero : core.

  Lemma mod_inv_mod_idemp a p :
    prime p ->
    mod_inv (a mod p) p = mod_inv a p.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    destruct (Z.eqb_spec (a mod p) 0) as [ap0|ap0].
    {
      rewrite ap0.
      apply Zmod_divide in ap0; [|lia].
      unfold mod_inv.
      now rewrite (egcd_divides a p) by (auto; lia).
    }
    rewrite <- mod_inv_mod, <- (mod_inv_mod a).
    apply mod_mul_both_l with a; auto.
    rewrite <- Z.mul_mod_idemp_l by lia.
    now rewrite !mul_mod_inv by auto.
  Qed.

  Lemma mod_pow_pos_fermat a p :
    prime p ->
    a mod p <> 0 ->
    mod_pow_pos a (Z.to_pos (p - 1)) p = 1.
  Proof.
    intros isprime ap.
    pose proof (prime_ge_2 _ isprime).
    rewrite mod_pow_pos_spec.
    rewrite Z.pow_pos_fold.
    rewrite Z2Pos.id by lia.
    now apply fermat.
  Qed.

  Lemma mod_pow_fermat a p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (p - 1) p = 1.
  Proof.
    intros isprime ap.
    pose proof (prime_ge_2 _ isprime).
    pose proof (mod_pow_pos_fermat _ _ isprime ap).
    destruct p; try lia.
    destruct (Z.pos p - 1) eqn:?; try lia.
    assumption.
  Qed.

  Lemma mod_pow_pos_exp_mul a x x' p :
    mod_pow_pos a (x * x') p = mod_pow_pos (mod_pow_pos a x p) x' p.
  Proof.
    rewrite !mod_pow_pos_spec by auto.
    rewrite !Z.pow_pos_fold.
    rewrite Pos2Z.inj_mul.
    rewrite Z_pow_mod_idemp.
    now rewrite <- Z.pow_mul_r by lia.
  Qed.

  Lemma mod_pow_pos_aux_1_l x p r :
    mod_pow_pos_aux 1 x p r = r mod p.
  Proof.
    revert r.
    induction x; intros r; cbn.
    + rewrite mod_pow_pos_aux_mod_idemp.
      rewrite Z.mul_1_r.
      rewrite IHx.
      apply Zmod_mod; auto.
    + rewrite mod_pow_pos_aux_mod_idemp.
      apply IHx.
    + now rewrite Z.mul_1_r.
  Qed.

  Lemma mod_pow_pos_1_l x p :
    mod_pow_pos 1 x p = 1 mod p.
  Proof. apply mod_pow_pos_aux_1_l. Qed.
  Lemma mod_inv_1_l p :
    prime p ->
    mod_inv 1 p = 1 mod p.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    rewrite <- mod_inv_mod.
    apply mod_mul_both_l with 1; auto.
    rewrite mul_mod_inv by auto.
    cbn.
    now rewrite Z.mod_1_l by lia.
  Qed.
  Lemma mod_pow_1_l x p :
    prime p ->
    mod_pow 1 x p = 1 mod p.
  Proof.
    intros isprime.
    destruct x; auto; cbn.
    - apply mod_pow_pos_1_l.
    - rewrite mod_pow_pos_1_l, mod_inv_mod_idemp by auto.
      now apply mod_inv_1_l.
  Qed.

  Lemma mod_pow_1_r a p :
    mod_pow a 1 p = a mod p.
  Proof.
    cbn -[Z.mul].
    now rewrite Z.mul_1_l.
  Qed.

  Lemma mod_inv_mul a b p :
    prime p ->
    a mod p <> 0 ->
    b mod p <> 0 ->
    mod_inv (a * b) p = mod_inv b p * mod_inv a p mod p.
  Proof.
    intros isprime ap0 bp0.
    pose proof (prime_ge_2 _ isprime).
    rewrite <- mod_inv_mod.
    apply mod_mul_both_l with (a * b); auto.
    rewrite mul_mod_inv by auto.
    rewrite <- Z.mul_assoc, (Z.mul_assoc b).
    rewrite <- Z.mul_mod_idemp_r by lia.
    rewrite <- (Z.mul_mod_idemp_l (b * _)) by lia.
    rewrite Z.mul_mod_idemp_r by lia.
    rewrite mul_mod_inv by auto.
    rewrite Z.mul_1_l.
    now rewrite mul_mod_inv by auto.
  Qed.

  Lemma mod_pow_pos_succ_r a x p :
    a * mod_pow_pos a x p mod p = mod_pow_pos a (Pos.succ x) p.
  Proof.
    rewrite !mod_pow_pos_spec, !Z.pow_pos_fold.
    cbn.
    rewrite Zmult_mod_idemp_r.
    rewrite Z.pow_pos_fold.
    rewrite <- Z.pow_succ_r by lia.
    cbn.
    now rewrite <- Pos.add_1_r.
  Qed.

  Lemma mod_pow_succ a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (Z.succ x) p = a * mod_pow a x p mod p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct x.
    - cbn.
      rewrite Z.mod_1_l by lia.
      rewrite Z.mul_1_r.
      destruct a; auto.
    - cbn -[Pos.add].
      rewrite mod_pow_pos_succ_r.
      now replace (p0 + 1)%positive with (Pos.succ p0) by lia.
    - cbn.
      destruct (Pos.eq_dec p0 1) as [->|?].
      + cbn -[Z.mul].
        rewrite Z.mul_1_l.
        rewrite mod_inv_mod_idemp by auto.
        rewrite mul_mod_inv by auto.
        now rewrite Z.mod_1_l by lia.
      + rewrite Z.pos_sub_lt by lia.
        cbn.
        rewrite <- mod_inv_mod.
        apply mod_mul_both_l with (mod_inv a p); auto.
        rewrite Z.mul_assoc.
        rewrite <- (Z.mul_mod_idemp_l (mod_inv a p * a)) by lia.
        rewrite (Z.mul_comm _ a).
        rewrite mul_mod_inv by auto.
        rewrite <- mod_inv_mul by auto.
        rewrite Z.mul_comm.
        rewrite <- mod_inv_mod_idemp by auto.
        rewrite mod_pow_pos_succ_r.
        replace (Pos.succ (p0 - 1)) with p0 by lia.
        now rewrite Z.mul_1_l, mod_inv_mod.
  Qed.

  Lemma mod_pow_pred a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (Z.pred x) p = mod_inv a p * mod_pow a x p mod p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    rewrite <- mod_pow_mod.
    apply mod_mul_both_l with a; auto.
    rewrite <- mod_pow_succ by auto.
    replace (Z.succ (Z.pred x)) with x by lia.
    rewrite Z.mul_assoc.
    rewrite <- Z.mul_mod_idemp_l by lia.
    rewrite mul_mod_inv by auto.
    now rewrite Z.mul_1_l, mod_pow_mod.
  Qed.

  Lemma mod_pow_exp_plus a x x' p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (x + x') p = mod_pow a x p * mod_pow a x' p mod p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    revert x'.
    induction x using Z.peano_ind; intros x'.
    - cbn.
      rewrite Z.mod_1_l by lia.
      rewrite Z.mul_1_l.
      now rewrite mod_pow_mod by lia.
    - replace (Z.succ x + x') with (Z.succ (x + x')) by lia.
      rewrite mod_pow_succ by auto.
      rewrite IHx.
      rewrite Z.mul_mod_idemp_r by lia.
      rewrite Z.mul_assoc.
      rewrite <- Z.mul_mod_idemp_l by lia.
      now rewrite <- mod_pow_succ by auto.
    - replace (Z.pred x + x') with (x + Z.pred x') by lia.
      rewrite IHx.
      rewrite !mod_pow_pred by auto.
      rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by lia.
      apply f_equal2; lia.
  Qed.

  Lemma mod_inv_involutive a p :
    prime p ->
    a mod p <> 0 ->
    mod_inv (mod_inv a p) p = a mod p.
  Proof.
    intros isprime ap0.
    rewrite <- mod_inv_mod.
    apply mod_mul_both_l with (mod_inv a p); auto.
    rewrite mul_mod_inv by auto.
    now rewrite Z.mul_comm, mul_mod_inv by auto.
  Qed.

  Lemma mod_pow_pos_distr_exp a a' x p :
    p <> 0 ->
    mod_pow_pos (a * a') x p =
    (mod_pow_pos a x p * mod_pow_pos a' x p) mod p.
  Proof.
    intros p0.
    rewrite !mod_pow_pos_spec, !Z.pow_pos_fold.
    rewrite Z.pow_mul_l.
    now rewrite Z.mul_mod by auto.
  Qed.

  Lemma mod_inv_mod_pow_pos_comm a x p :
    prime p ->
    a mod p <> 0 ->
    mod_inv (mod_pow_pos a x p) p = mod_pow_pos (mod_inv a p) x p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct (Z.eqb_spec p 2) as [->|?].
    {
      rewrite <- mod_pow_pos_mod_idemp, <- (mod_inv_mod_idemp a) by auto.
      pose proof (Z.mod_pos_bound a 2 ltac:(lia)).
      replace (a mod 2) with 1 by lia.
      now rewrite !mod_pow_pos_1_l, mod_inv_1_l by auto.
    }
    rewrite <- mod_inv_mod, <- (mod_pow_pos_mod (mod_inv a p)).
    apply mod_mul_both_l with (mod_pow_pos a x p); auto.
    rewrite mul_mod_inv by auto.
    rewrite <- mod_pow_pos_distr_exp by lia.
    rewrite <- mod_pow_pos_mod_idemp.
    rewrite mul_mod_inv by auto.
    rewrite mod_pow_pos_1_l.
    now rewrite Z.mod_1_l by lia.
  Qed.

  Lemma mod_pow_exp_mul a x x' p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (x * x') p = mod_pow (mod_pow a x p) x' p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct x, x'; cbn;
      repeat (
          try rewrite Z.mod_1_l by lia;
          try rewrite mod_pow_pos_1_l;
          try rewrite mod_inv_1_l);
      auto.
    - apply mod_pow_pos_exp_mul.
    - now rewrite mod_pow_pos_exp_mul.
    - rewrite !mod_inv_mod_pow_pos_comm by auto.
      now rewrite mod_pow_pos_exp_mul.
    - rewrite mod_inv_mod_pow_pos_comm by auto.
      rewrite mod_inv_involutive by auto.
      rewrite mod_pow_pos_mod_idemp.
      now rewrite <- mod_pow_pos_exp_mul.
  Qed.

  Lemma mod_pow_exp_opp a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (-x) p = mod_inv (mod_pow a x p) p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct x; auto.
    - cbn.
      rewrite mod_inv_mod_idemp by auto.
      now rewrite mod_inv_1_l.
    - cbn.
      rewrite mod_inv_involutive by auto.
      now rewrite mod_pow_pos_mod.
  Qed.

  Lemma mod_pow_exp_mod a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (x mod (p - 1)) p = mod_pow a x p.
  Proof.
    intros isprime ap.
    pose proof (prime_ge_2 _ isprime).
    rewrite (Z.div_mod x (p - 1)) at 2 by lia.
    rewrite mod_pow_exp_plus by auto.
    rewrite mod_pow_exp_mul by auto.
    rewrite mod_pow_fermat by auto.
    rewrite mod_pow_1_l by auto.
    rewrite !Z.mod_1_l by lia.
    now rewrite Z.mul_1_l, mod_pow_mod.
  Qed.

  Definition boardroom_axioms (p : Z) :
    prime p -> BoardroomAxioms Z.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    refine
      {|
        elmeq a b := a mod p = b mod p;
        elmeqb a b := a mod p =? b mod p;
        zero := 0;
        one := 1;
        add a a' := (a + a') mod p;
        mul a a' := (a * a') mod p;
        opp a := p - a;
        inv a := mod_inv a p;
        pow a e := mod_pow a e p;
        order := p;
      |}.
    - intros x y; apply Z.eqb_spec.
    - lia.
    - constructor; auto.
      now intros a a' a'' -> ->.
    - intros a a' aeq b b' beq.
      now rewrite Z.add_mod, aeq, beq, <- Z.add_mod by lia.
    - intros a a' aeq b b' beq.
      now rewrite Z.mul_mod, aeq, beq, <- Z.mul_mod by lia.
    - intros a a' aeq.
      now rewrite Zminus_mod, aeq, <- Zminus_mod.
    - intros a a' aeq.
      cbn.
      now rewrite <- mod_inv_mod_idemp, aeq, mod_inv_mod_idemp by auto.
    - intros a a' aeq e ? <-.
      now rewrite <- mod_pow_mod_idemp, aeq, mod_pow_mod_idemp.
    - intros a anp e e' eeq.
      rewrite <- (mod_pow_exp_mod _ e), <- (mod_pow_exp_mod _ e') by auto.
      now rewrite eeq.
    - now rewrite Z.mod_1_l, Z.mod_0_l by lia.
    - intros a b.
      now rewrite Z.add_comm.
    - intros a b c.
      rewrite !Z.mod_mod by lia.
      rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
      apply f_equal2; lia.
    - intros a b.
      now rewrite Z.mul_comm.
    - intros a b c.
      repeat (try rewrite Z.mul_mod_idemp_l; try rewrite Z.mul_mod_idemp_r); try lia.
      now rewrite Z.mul_assoc.
    - intros a.
      now rewrite Z.mod_mod by lia.
    - intros a.
      now rewrite Z.mod_mod by lia.
    - intros a.
      rewrite Z.mod_mod by lia.
      now rewrite Z.mul_1_l.
    - intros a.
      rewrite Z.mod_mod by lia.
      replace (p - a + a) with p by lia.
      rewrite Z.mod_same, Z.mod_0_l; lia.
    - intros a anp.
      now rewrite Z.mul_comm, mul_mod_inv by auto.
    - intros a b c.
      repeat (try rewrite Z.mul_mod_idemp_l;
              try rewrite Z.mul_mod_idemp_r;
              try rewrite Z.add_mod_idemp_l;
              try rewrite Z.add_mod_idemp_r;
              try rewrite Z.mod_mod); try lia.
      apply f_equal2; lia.
    - intros a anp.
      cbn.
      now rewrite Z.mod_1_l at 1 by lia.
    - intros a.
      now rewrite mod_pow_mod, mod_pow_1_r.
    - intros a ap0.
      rewrite (mod_pow_exp_opp _ 1) by auto.
      rewrite mod_pow_1_r.
      now rewrite mod_inv_mod_idemp.
    - intros a e e' ap0.
      now rewrite mod_pow_exp_plus by auto.
    - intros a b e anz.
      now rewrite mod_pow_exp_mul.
    - auto.
    - auto.
  Defined.
End Zp.

Module BigZp.
  Local Open Scope bigZ.
  Fixpoint mod_pow_pos_aux (a : bigZ) (x : positive) (m : bigZ) (r : bigZ) : bigZ :=
    match x with
    | x~0%positive => mod_pow_pos_aux (BigZ.square a mod m) x m r
    | x~1%positive => mod_pow_pos_aux (BigZ.square a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow_pos (a : bigZ) (x : positive) (m : bigZ) : bigZ :=
    mod_pow_pos_aux a x m 1.

  Fixpoint egcd_aux
           (n : nat)
           (r0 a0 b0 r1 a1 b1 : bigZ) {struct n} : bigZ * bigZ :=
    match n with
    | 0%nat => (0, 0)
    | S n => let (q, r) := BigZ.div_eucl r0 r1 in
             if r =? 0 then
               (a1, b1)
             else
               egcd_aux n r1 a1 b1 r (a0 - q*a1) (b0 - q*b1)
    end.

  Definition egcd (m n : bigZ) : bigZ * bigZ :=
    if m =? 0 then
      (0, BigZ.sgn n)
    else
      if n =? 0 then
        (BigZ.sgn m, 0)
      else
        let num_steps :=
            S (Z.to_nat (BigZ.to_Z (BigZ.log2 (BigZ.abs m) + BigZ.log2 (BigZ.abs n)))) in
        if BigZ.abs m <? BigZ.abs n then
          let (x, y) := egcd_aux num_steps (BigZ.abs n) 1 0 (BigZ.abs m) 0 1 in
          (BigZ.sgn m * y, BigZ.sgn n * x)
        else
          let (x, y) := egcd_aux num_steps (BigZ.abs m) 1 0 (BigZ.abs n) 0 1 in
          (BigZ.sgn m * x, BigZ.sgn n * y).

  Definition mod_inv (a : bigZ) (p : bigZ) : bigZ :=
    fst (egcd a p) mod p.

  Definition mod_pow (a : bigZ) (x : Z) (p : bigZ) : bigZ :=
    match x with
    | Z0 => a ^ 0 mod p
    | Zpos x => mod_pow_pos a x p
    | Zneg x => mod_inv (mod_pow_pos a x p) p
    end.

  #[local]
  Hint Rewrite BigZ.square_spec BigZ.spec_pow_pos : zsimpl.
  #[local]
  Hint Rewrite BigN.spec_of_pos : nsimpl.

  Coercion BigZ.to_Z : BigZ.t_ >-> Z.

  Lemma spec_mod_pow_pos_aux a x p r :
    BigZ.to_Z (mod_pow_pos_aux a x p r) =
    Zp.mod_pow_pos_aux a x p r.
  Proof.
    revert a p r.
    induction x; intros a p r; cbn in *.
    - rewrite IHx.
      now autorewrite with zsimpl.
    - rewrite IHx.
      now autorewrite with zsimpl.
    - now autorewrite with zsimpl.
  Qed.

  #[local]
  Hint Rewrite spec_mod_pow_pos_aux : zsimpl.

  Lemma spec_mod_pow_pos a x p :
    BigZ.to_Z (mod_pow_pos a x p) =
    Zp.mod_pow_pos a x p.
  Proof. apply spec_mod_pow_pos_aux. Qed.

  #[local]
  Hint Rewrite spec_mod_pow_pos : zsimpl.

  Lemma spec_egcd_aux n r0 a0 b0 r1 a1 b1 :
    let (x, y) := egcd_aux n r0 a0 b0 r1 a1 b1 in
    (BigZ.to_Z x, BigZ.to_Z y) =
    Egcd.egcd_aux n r0 a0 b0 r1 a1 b1.
  Proof.
    revert r0 a0 b0 r1 a1 b1.
    induction n as [|n IH]; [easy|]; intros r0 a0 b0 r1 a1 b1.
    cbn.
    pose proof (BigZ.spec_div_eucl r0 r1) as H.
    destruct (BigZ.div_eucl r0 r1) as [q r].
    destruct (Z.div_eucl r0 r1) as [q' r'].
    inversion H; subst.
    rewrite BigZ.spec_eqb.
    cbn.
    destruct (r =? 0)%Z; [easy|].
    rewrite <- !BigZ.spec_mul, <- !BigZ.spec_sub.
    apply IH.
  Qed.

  #[local]
  Hint Rewrite BigZ.spec_abs : zsimpl.

  Lemma spec_egcd a b :
    let (x, y) := egcd a b in
    (BigZ.to_Z x, BigZ.to_Z y) = Egcd.egcd a b.
  Proof.
    unfold egcd, Egcd.egcd.
    autorewrite with zsimpl.
    change (BigZ.to_Z 0) with 0%Z.
    destruct (_ =? _)%Z; [now autorewrite with zsimpl|].
    destruct (_ =? _)%Z; [now autorewrite with zsimpl|].
    destruct (_ <? _)%Z.
    all: rewrite <- !BigZ.spec_abs.
    all: change 1%Z with (BigZ.to_Z 1).
    all: change 0%Z with (BigZ.to_Z 0).
    all:
      repeat
        match goal with
        | [|- context[egcd_aux ?n ?r0 ?a0 ?b0 ?r1 ?a1 ?b1]] =>
          pose proof (spec_egcd_aux n r0 a0 b0 r1 a1 b1);
            destruct (egcd_aux n r0 a0 b0 r1 a1 b1),
                     (Egcd.egcd_aux n r0 a0 b0 r1 a1 b1)
        end.
    all: inversion H.
    all: now autorewrite with zsimpl.
  Qed.

  Lemma spec_mod_inv a p :
    BigZ.to_Z (mod_inv a p) = Zp.mod_inv a p.
  Proof.
    unfold mod_inv, Zp.mod_inv.
    pose proof (spec_egcd a p).
    destruct (egcd _ _), (Egcd.egcd _ _).
    inversion H.
    now autorewrite with zsimpl.
  Qed.

  #[local]
  Hint Rewrite spec_mod_inv : zsimpl.

  Lemma spec_mod_pow a x p :
    BigZ.to_Z (mod_pow a x p) = Zp.mod_pow a x p.
  Proof.
    unfold mod_pow, Zp.mod_pow.
    now destruct x; autorewrite with zsimpl.
  Qed.

  #[local]
  Hint Rewrite spec_mod_pow : zsimpl.
  #[local]
  Hint Rewrite BigZ.spec_modulo : zsimpl.
  #[local]
  Hint Resolve Zp.mod_inv_nonzero : core.
  #[local]
  Hint Resolve Zp.mod_pow_nonzero : core.
  #[local]
  Hint Resolve Zp.mod_inv_mod_nonzero : core.
  #[local]
  Hint Resolve Zp.mod_pow_mod_nonzero : core.

  Local Open Scope Z.
  Definition boardroom_axioms (p : Z) :
    prime p -> BoardroomAxioms Z.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    refine
      {| elmeq a b := a mod p = b mod p;
         elmeqb a b := a mod p =? b mod p;
         zero := 0;
         one := 1;
         add a a' := (a + a') mod p;
         mul a a' := (a * a') mod p;
         opp a := p - a;
         inv a := BigZ.to_Z (mod_inv (BigZ.of_Z a) (BigZ.of_Z p));
         pow a e := BigZ.to_Z (mod_pow (BigZ.of_Z a) e (BigZ.of_Z p));
         order := p;
      |}.
    - intros x y; apply Z.eqb_spec.
    - lia.
    - constructor; auto.
      now intros a a' a'' -> ->.
    - intros a a' aeq b b' beq.
      autorewrite with zsimpl in *.
      now rewrite Z.add_mod, aeq, beq, <- Z.add_mod by lia.
    - intros a a' aeq b b' beq.
      autorewrite with zsimpl in *.
      now rewrite Z.mul_mod, aeq, beq, <- Z.mul_mod by lia.
    - intros a a' aeq.
      autorewrite with zsimpl in *.
      now rewrite Zminus_mod, aeq, <- Zminus_mod.
    - intros a a' aeq.
      autorewrite with zsimpl in *.
      now rewrite <- Zp.mod_inv_mod_idemp, aeq, Zp.mod_inv_mod_idemp.
    - intros a a' aeq e ? <-.
      autorewrite with zsimpl in *.
      now rewrite <- Zp.mod_pow_mod_idemp, aeq, Zp.mod_pow_mod_idemp.
    - intros a anp e e' eeq.
      autorewrite with zsimpl in *.
      rewrite <- (Zp.mod_pow_exp_mod _ e), <- (Zp.mod_pow_exp_mod _ e') by auto.
      now rewrite eeq.
    - autorewrite with zsimpl in *.
      now rewrite Z.mod_1_l, Z.mod_0_l by lia.
    - intros a b.
      autorewrite with zsimpl in *.
      now rewrite Z.add_comm.
    - intros a b c.
      autorewrite with zsimpl in *.
      rewrite !Z.mod_mod by lia.
      rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
      apply f_equal2; lia.
    - intros a b.
      autorewrite with zsimpl in *.
      now rewrite Z.mul_comm.
    - intros a b c.
      autorewrite with zsimpl in *.
      repeat (try rewrite Z.mul_mod_idemp_l; try rewrite Z.mul_mod_idemp_r); try lia.
      now rewrite Z.mul_assoc.
    - intros a.
      autorewrite with zsimpl in *.
      now rewrite Z.mod_mod by lia.
    - intros a.
      autorewrite with zsimpl in *.
      now rewrite Z.mod_mod by lia.
    - intros a.
      autorewrite with zsimpl in *.
      rewrite Z.mod_mod by lia.
      now rewrite Z.mul_1_l.
    - intros a.
      autorewrite with zsimpl in *.
      rewrite Z.mod_mod by lia.
      replace (p - a + a)%Z with p by lia.
      rewrite Z.mod_same, Z.mod_0_l; lia.
    - intros a anp.
      autorewrite with zsimpl in *.
      now rewrite Z.mul_comm, Zp.mul_mod_inv by auto.
    - intros a b c.
      autorewrite with zsimpl in *.
      repeat (try rewrite Z.mul_mod_idemp_l;
              try rewrite Z.mul_mod_idemp_r;
              try rewrite Z.add_mod_idemp_l;
              try rewrite Z.add_mod_idemp_r;
              try rewrite Z.mod_mod); try lia.
      apply f_equal2; lia.
    - intros a anp.
      autorewrite with zsimpl in *.
      cbn.
      now rewrite Z.mod_1_l at 1 by lia.
    - intros a.
      autorewrite with zsimpl in *.
      now rewrite Zp.mod_pow_mod, Zp.mod_pow_1_r.
    - intros a ap0.
      autorewrite with zsimpl in *.
      rewrite (Zp.mod_pow_exp_opp _ 1) by auto.
      rewrite Zp.mod_pow_1_r.
      now rewrite Zp.mod_inv_mod_idemp.
    - intros a e e' ap0.
      autorewrite with zsimpl in *.
      now rewrite Zp.mod_pow_exp_plus by auto.
    - intros a b e ap0.
      autorewrite with zsimpl in *.
      now rewrite Zp.mod_pow_exp_mul.
    - intros a e ap0.
      autorewrite with zsimpl in *.
      auto.
    - intros a ap0.
      autorewrite with zsimpl in *.
      auto.
  Defined.

End BigZp.



Module Type BoardroomAxiomsZParams.
  Parameter p : Z.
  Parameter isprime : prime p.
  Parameter prime_ge_2 : p >= 2.
End BoardroomAxiomsZParams.

Module BoardroomAxiomsZ (Params : BoardroomAxiomsZParams).
  Import Params.
  Local Open Scope Z_scope.

  #[local]
  Hint Resolve Zp.mod_inv_nonzero : core.
  #[local]
  Hint Resolve Zp.mod_pow_nonzero : core.
  #[local]
  Hint Resolve Zp.mod_inv_mod_nonzero : core.
  #[local]
  Hint Resolve Zp.mod_pow_mod_nonzero : core.

  #[export]
  Instance boardroom_axioms_Z : BoardroomAxioms Z.
  Proof.
  (* pose proof (prime_ge_2). *)
  (* pose proof (isprime). *)
  refine
    {| elmeq a b := a mod p = b mod p;
      elmeqb a b := a mod p =? b mod p;
      zero := 0;
      one := 1;
      add a a' := (a + a') mod p;
      mul a a' := (a * a') mod p;
      opp a := p - a;
      inv a := Zp.mod_inv a p;
      pow a e := Zp.mod_pow a e p;
      order := p;
    |};
    (* assert (p >= 2); apply prime_ge_2. ;
    (assert (prime p); apply isprime). *)
    pose proof (prime_ge_2);
    pose proof (isprime).

  - intros x y; apply Z.eqb_spec.
  - lia.
  - constructor; auto.
    now intros a a' a'' -> ->.
  - intros a a' aeq b b' beq.
    autorewrite with zsimpl in *.
    now rewrite Z.add_mod, aeq, beq, <- Z.add_mod by lia.
  - intros a a' aeq b b' beq.
    autorewrite with zsimpl in *.
    now rewrite Z.mul_mod, aeq, beq, <- Z.mul_mod by lia.
  - intros a a' aeq.
    autorewrite with zsimpl in *.
    now rewrite Zminus_mod, aeq, <- Zminus_mod.
  - intros a a' aeq.
    autorewrite with zsimpl in *.
    now rewrite <- Zp.mod_inv_mod_idemp, aeq, Zp.mod_inv_mod_idemp.
  - intros a a' aeq e ? <-.
    autorewrite with zsimpl in *.
    now rewrite <- Zp.mod_pow_mod_idemp, aeq, Zp.mod_pow_mod_idemp.
  - intros a anp e e' eeq.
    autorewrite with zsimpl in *.
    rewrite <- (Zp.mod_pow_exp_mod _ e), <- (Zp.mod_pow_exp_mod _ e') by auto.
    now rewrite eeq.
  - autorewrite with zsimpl in *.
    now rewrite Z.mod_1_l, Z.mod_0_l by lia.
  - intros a b.
    autorewrite with zsimpl in *.
    now rewrite Z.add_comm.
  - intros a b c.
    autorewrite with zsimpl in *.
    rewrite !Z.mod_mod by lia.
    rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
    apply f_equal2; lia.
  - intros a b.
    autorewrite with zsimpl in *.
    now rewrite Z.mul_comm.
  - intros a b c.
    autorewrite with zsimpl in *.
    repeat (try rewrite Z.mul_mod_idemp_l; try rewrite Z.mul_mod_idemp_r); try lia.
    now rewrite Z.mul_assoc.
  - intros a.
    autorewrite with zsimpl in *.
    now rewrite Z.mod_mod by lia.
  - intros a.
    autorewrite with zsimpl in *.
    now rewrite Z.mod_mod by lia.
  - intros a.
    autorewrite with zsimpl in *.
    rewrite Z.mod_mod by lia.
    now rewrite Z.mul_1_l.
  - intros a.
    autorewrite with zsimpl in *.
    rewrite Z.mod_mod by lia.
    replace (p - a + a)%Z with p by lia.
    rewrite Z.mod_same, Z.mod_0_l; lia.
  - intros a anp.
    autorewrite with zsimpl in *.
    now rewrite Z.mul_comm, Zp.mul_mod_inv by auto.
  - intros a b c.
    autorewrite with zsimpl in *.
    repeat (try rewrite Z.mul_mod_idemp_l;
            try rewrite Z.mul_mod_idemp_r;
            try rewrite Z.add_mod_idemp_l;
            try rewrite Z.add_mod_idemp_r;
            try rewrite Z.mod_mod); try lia.
    apply f_equal2; lia.
  - intros a anp.
    autorewrite with zsimpl in *.
    cbn.
    now rewrite Z.mod_1_l at 1 by lia.
  - intros a.
    autorewrite with zsimpl in *.
    now rewrite Zp.mod_pow_mod, Zp.mod_pow_1_r.
  - intros a ap0.
    autorewrite with zsimpl in *.
    rewrite (Zp.mod_pow_exp_opp _ 1) by auto.
    rewrite Zp.mod_pow_1_r.
    now rewrite Zp.mod_inv_mod_idemp.
  - intros a e e' ap0.
    autorewrite with zsimpl in *.
    now rewrite Zp.mod_pow_exp_plus by auto.
  - intros a b e ap0.
    autorewrite with zsimpl in *.
    now rewrite Zp.mod_pow_exp_mul.
  - intros a e ap0.
    autorewrite with zsimpl in *.
    auto.
  - intros a ap0.
    autorewrite with zsimpl in *.
    auto.
  Defined.

End BoardroomAxiomsZ.
