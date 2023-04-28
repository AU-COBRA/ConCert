(** This file implements various helper functions and proofs *)

From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import Morphisms.
From Coq Require Import Psatz.
From ConCert.Utils Require Import Automation.
Import ListNotations.

Fixpoint map_option {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | hd :: tl => match f hd with
                | Some b => b :: map_option f tl
                | None => map_option f tl
                end
  | [] => []
  end.

Definition with_default {A : Type} (default : A) (o : option A) : A :=
  match o with
  | Some v => v
  | None => default
  end.

Definition unpack_option {A : Type} (a : option A) :=
  match a return match a with
                  | Some _ => A
                  | None => unit
                  end with
  | Some x => x
  | None => tt
  end.

Fixpoint sumZ {A : Type} (f : A -> Z) (xs : list A) : Z :=
  match xs with
  | [] => 0
  | x :: xs' => f x + sumZ f xs'
  end.

Fixpoint sumnat {A : Type} (f : A -> nat) (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => f x + sumnat f xs'
  end.

Fixpoint sumN {A : Type} (f : A -> N) (xs : list A) : N :=
  match xs with
  | [] => 0
  | x :: xs' => f x + sumN f xs'
  end.

Lemma sumnat_permutation
      {A : Type} {f : A -> nat} {xs ys : list A}
      (perm_eq : Permutation xs ys) :
  sumnat f xs = sumnat f ys.
Proof. induction perm_eq; perm_simplify; lia. Qed.

#[export]
Instance sumnat_perm_proper {A : Type} :
  Proper (eq ==> Permutation (A := A) ==> eq) sumnat.
Proof. repeat intro. subst. now apply sumnat_permutation. Qed.

Lemma sumnat_map {A B : Type} (f : A -> B) (g : B -> nat) (xs : list A) :
  sumnat g (map f xs) =
  sumnat (fun a => g (f a)) xs.
Proof.
  induction xs as [|hd tl IH]; auto.
  cbn.
  now rewrite IH.
Qed.

Lemma sumZ_permutation
      {A : Type} {f : A -> Z} {xs ys : list A}
      (perm_eq : Permutation xs ys) :
  sumZ f xs = sumZ f ys.
Proof. induction perm_eq; perm_simplify; lia. Qed.

#[export]
Instance sumZ_perm_proper {A : Type} :
  Proper (eq ==> Permutation (A := A) ==> eq) sumZ.
Proof. repeat intro. subst. now apply sumZ_permutation. Qed.

Local Open Scope Z.
Lemma sumZ_app {A : Type} {f : A -> Z} {xs ys : list A} :
  sumZ f (xs ++ ys) = sumZ f xs + sumZ f ys.
Proof.
  revert ys.
  induction xs as [| x xs IH]; intros ys; auto.
  cbn.
  rewrite IH.
  lia.
Qed.

Lemma sumZ_map {A B : Type} (f : A -> B) (g : B -> Z) (xs : list A) :
  sumZ g (map f xs) =
  sumZ (fun a => g (f a)) xs.
Proof.
  induction xs as [|hd tl IH]; auto.
  cbn.
  now rewrite IH.
Qed.

Lemma sumZ_filter {A : Type} (f : A -> Z) (pred : A -> bool) (xs : list A) :
  sumZ f (filter pred xs) =
  sumZ (fun a => if pred a then f a else 0) xs.
Proof.
  induction xs as [|hd tl IH]; auto.
  cbn.
  destruct (pred hd); auto.
  cbn.
  now rewrite IH.
Qed.

Lemma sumZ_mul (f : Z -> Z) (l : list Z) (z : Z) :
  z * sumZ f l = sumZ (fun z' => z * f z') l.
Proof.
  induction l; auto; cbn in *; lia.
Qed.

Local Hint Resolve in_or_app : core.

Lemma incl_split {A : Type} (l m n : list A) :
  incl (l ++ m) n -> incl l n /\ incl m n.
Proof.
  intros H.
  unfold incl in *.
  auto.
Qed.

Lemma NoDup_incl_reorganize {A : Type} (l l' : list A) :
  NoDup l' ->
  incl l' l ->
  exists suf, Permutation (l' ++ suf) l.
Proof.
  revert l.
  induction l' as [| x xs IH]; intros l nodup_l' incl_l'_l.
  - exists l.
    apply Permutation_refl.
  - assert (x_in_l: In x l).
    + apply (incl_l'_l x).
      left. constructor.
    + destruct (in_split _ _ x_in_l) as [pref [suf eq]]; subst.
      inversion nodup_l'; subst.
      assert (incl xs (pref ++ suf)).
      * intros a a_in.
        apply in_or_app.
        apply (incl_split [x] xs _) in incl_l'_l.
        destruct incl_l'_l as [incl_x incl_xs].
        specialize (incl_xs a a_in).
        apply in_app_or in incl_xs.
        destruct incl_xs as [in_pref | [in_x | in_suf]]; auto.
        congruence.
      * destruct (IH _ H2 H) as [suf' perm_suf'].
        exists suf'.
        perm_simplify.
Qed.

Lemma in_NoDup_app {A : Type} (x : A) (l m : list A) :
  In x l -> NoDup (l ++ m) -> ~In x m.
Proof.
  intros in_x_l nodup_l_app_m in_x_m.
  destruct (in_split _ _ in_x_l) as [l1 [l2 eq]]; subst.
  replace ((l1 ++ x :: l2) ++ m) with (l1 ++ x :: (l2 ++ m)) in nodup_l_app_m.
  - apply (NoDup_remove_2 _ _ _) in nodup_l_app_m.
    rewrite app_assoc in nodup_l_app_m.
    auto.
  - rewrite app_comm_cons.
    appify.
    now rewrite app_assoc.
Qed.

Lemma seq_app start len1 len2 :
  seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
Proof.
  revert start.
  induction len1 as [| len1 IH]; intros start.
  - now rewrite Nat.add_0_r.
  - cbn.
    rewrite IH.
    f_equal; f_equal; f_equal.
    lia.
Qed.

Lemma forall_respects_permutation {A} (xs ys : list A) P :
  Permutation xs ys -> Forall P xs -> Forall P ys.
Proof.
  intros perm all.
  apply Forall_forall.
  intros y y_in.
  pose proof (proj1 (Forall_forall P xs) all).
  apply H.
  apply Permutation_in with ys; symmetry in perm; auto.
Qed.

#[export]
Instance Forall_Permutation_proper {A} :
  Proper (eq ==> @Permutation A ==> iff) (@Forall A).
Proof.
  intros f f' ? xs ys perm.
  subst f'.
  split; apply forall_respects_permutation; auto; symmetry; auto.
Qed.

#[export]
Instance forallb_Permutation_proper {A} :
  Proper (eq ==> @Permutation A ==> eq) (@forallb A).
Proof.
  assert (H: forall f (xs ys : list A),
             Permutation xs ys -> forallb f xs = true -> forallb f ys = true).
  {
    intros f xs ys perm all.
    apply forallb_forall.
    intros x x_in.
    pose proof (proj1 (forallb_forall f xs) all).
    apply H.
    now rewrite perm.
  }

  intros ? f -> xs ys perm.
  destruct (forallb f xs) eqn:forall1, (forallb f ys) eqn:forall2; auto.
  - pose proof (H _ _ _ perm forall1); congruence.
  - pose proof (H _ _ _ (Permutation_sym perm) forall2); congruence.
Qed.

Lemma Forall_false_filter_nil {A : Type} (pred : A -> bool) (l : list A) :
  Forall (fun a => pred a = false) l -> filter pred l = [].
Proof.
  intros all.
  induction l as [|hd tl IH]; auto.
  inversion_clear all as [|? ? head_false tail_false].
  cbn.
  now rewrite head_false, IH.
Qed.

Lemma Forall_app {A : Type} (P : A -> Prop) (l l' : list A) :
  Forall P l /\ Forall P l' <-> Forall P (l ++ l').
Proof.
  revert l'.
  induction l as [ |hd tl IH].
  - cbn.
    split; intros; auto.
    tauto.
  - intros l'.
    split.
    + intros [all1 all2].
      inversion_clear all1.
      cbn.
      constructor; auto.
      apply -> IH.
      tauto.
    + intros all.
      cbn in all.
      inversion_clear all as [ | ? ? P_phd all_rest].
      enough (P hd /\ Forall P tl /\ Forall P l') by
          (split; try constructor; tauto).
      split; auto.
      now apply IH.
Qed.

Lemma filter_app {A} (pred : A -> bool) (l l' : list A) :
  filter pred (l ++ l') = filter pred l ++ filter pred l'.
Proof.
  induction l as [|hd tl IH]; auto.
  cbn.
  rewrite IH.
  destruct (pred hd); auto.
Qed.

Lemma filter_map {A B : Type} (f : A -> B) (pred : B -> bool) (l : list A) :
  filter pred (map f l) =
  map f (filter (fun a => pred (f a)) l).
Proof.
  induction l as [|hd tl IH]; auto.
  cbn.
  rewrite IH.
  destruct (pred (f hd)); auto.
Qed.

Lemma filter_false {A : Type} (l : list A) :
  filter (fun _ => false) l = [].
Proof. induction l; auto. Qed.

Lemma filter_true {A : Type} (l : list A) :
  filter (fun _ => true) l = l.
Proof.
  induction l as [|? ? IH]; auto.
  cbn.
  now rewrite IH.
Qed.

Lemma Permutation_filter {A : Type} (pred : A -> bool) (l l' : list A) :
  Permutation l l' ->
  Permutation (filter pred l) (filter pred l').
Proof.
  intros perm.
  induction perm; auto.
  - cbn.
    destruct (pred x); auto.
  - cbn.
    destruct (pred x), (pred y); auto.
    constructor.
  - rewrite IHperm1; auto.
Qed.

Fixpoint zip {X Y} (xs : list X) (ys : list Y) : list (X * Y) :=
  match xs, ys with
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | _, _ => []
  end.

Lemma zip_app {X Y} (xs xs' : list X) (ys ys' : list Y) :
  length xs = length ys ->
  zip (xs ++ xs') (ys ++ ys') = zip xs ys ++ zip xs' ys'.
Proof.
  intros len_xs.
  revert xs' ys ys' len_xs.
  induction xs as [|x xs IH]; intros xs' ys ys' len_xs; cbn.
  - destruct ys; cbn in *; congruence.
  - destruct ys as [|y ys]; cbn in *; try lia.
    apply f_equal.
    apply IH; lia.
Qed.

Lemma zip_map {A B C D} (f : A -> B) (g : C -> D) (xs : list A) (ys : list C) :
  zip (map f xs) (map g ys) =
  map (fun '(x, y) => (f x, g y)) (zip xs ys).
Proof.
  revert f g ys.
  induction xs as [|x xs IH]; intros f g ys; cbn; auto.
  destruct ys as [|y ys]; cbn; auto.
  f_equal.
  auto.
Qed.

Lemma existsb_forallb {A} f (l : list A) :
  existsb f l =
  negb (forallb (fun x => negb (f x)) l).
Proof.
  induction l as [|x xs IH]; auto.
  cbn.
  now rewrite IH, Bool.negb_andb, Bool.negb_involutive.
Qed.

Fixpoint All {A} (f : A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: xs => f x /\ All f xs
  end.

Lemma All_app {A} f (l l' : list A) :
  All f (l ++ l') <-> All f l /\ All f l'.
Proof.
  revert l'.
  induction l as [|x xs IH]; intros l'; cbn; firstorder.
Qed.

Lemma All_map {A B} (g : B -> Prop) (f : A -> B) (l : list A) :
  All g (map f l) <-> All (fun a => g (f a)) l.
Proof.
  induction l as [|x xs IH]; cbn; [tauto|].
  tauto.
Qed.

Lemma All_ext_in {A} (f g : A -> Prop) (l : list A) :
  All f l ->
  (forall a, In a l -> f a -> g a) ->
  All g l.
Proof.
  induction l as [|x xs IH]; auto.
  intros all fall.
  cbn in *.
  destruct_and_split; auto.
Qed.

Local Open Scope nat.
Lemma sumZ_seq_n (f : nat -> Z) n len :
  sumZ f (seq n len) =
  sumZ (fun i => f (i + n)) (seq 0 len).
Proof.
  revert n f.
  induction len as [|len IH]; intros n f; auto.
  cbn.
  apply f_equal.
  rewrite (IH 1), (IH (S n)).
  clear.
  induction (seq 0 len); auto.
  cbn.
  rewrite IHl.
  now replace (a + 1 + n) with (a + S n) by lia.
Qed.

Lemma sumZ_zero {A} (l : list A) :
  sumZ (fun _ => 0%Z) l = 0%Z.
Proof. induction l; auto. Qed.

Lemma sumZ_seq_feq (f g : nat -> Z) len :
  (forall i, i < len -> f i = g i)%nat ->
  sumZ g (seq 0 len) =
  sumZ f (seq 0 len).
Proof.
  revert f g.
  induction len as [|len IH]; intros f g all_same; auto.
  cbn.
  rewrite 2!(sumZ_seq_n _ 1).
  rewrite (all_same 0%nat ltac:(lia)).
  apply f_equal.
  apply IH.
  intros i lt.
  now specialize (all_same (i + 1)%nat ltac:(lia)).
Qed.

Lemma sumZ_firstn {A} default (f : A -> Z) n l :
  (n <= length l \/ f default = 0%Z) ->
  sumZ f (firstn n l) =
  sumZ (fun i => f (nth i l default)) (seq 0 n).
Proof.
  revert l.
  induction n as [|n IH]; intros l le; auto.
  cbn.
  rewrite sumZ_seq_n.
  destruct l; cbn in *.
  - destruct le; [lia|].
    rewrite H.
    clear -H.
    rewrite (sumZ_seq_feq (fun i : nat => 0%Z)).
    + now rewrite sumZ_zero.
    + intros i ?; destruct (i + 1); now rewrite H.
  - apply f_equal.
    rewrite IH by lia.
    apply sumZ_seq_feq.
    intros i.
    intros lt.
    destruct (i + 1) eqn:i1; [lia|].
    now replace n0 with i by lia.
Qed.

Lemma sumZ_skipn {A} default (f : A -> Z) n l :
  sumZ f (skipn n l) =
  sumZ (fun i => f (nth (n + i) l default)) (seq 0 (length l - n)).
Proof.
  revert l.
  induction n as [|n IH]; intros l; cbn.
  - rewrite Nat.sub_0_r.
    rewrite <- (sumZ_firstn default).
    + now rewrite firstn_all.
    + left; lia.
  - destruct l; auto.
Qed.

Local Open Scope Z.
Lemma sumZ_add {A} (f g : A -> Z) l :
  sumZ (fun a => f a + g a) l = sumZ f l + sumZ g l.
Proof.
  induction l; auto; cbn in *; lia.
Qed.
Lemma sumZ_sub {A} (f g : A -> Z) l :
  sumZ (fun a => f a - g a) l =
  sumZ f l - sumZ g l.
Proof.
  induction l; auto; cbn; lia.
Qed.

Lemma sumZ_seq_split split_len (f : nat -> Z) start len :
  (split_len <= len)%nat ->
  sumZ f (seq start len) =
  sumZ f (seq start split_len) + sumZ f (seq (start + split_len) (len - split_len)).
Proof.
  rewrite <- sumZ_app.
  rewrite <- seq_app.
  intros le.
  now replace (split_len + (len - split_len))%nat with len by lia.
Qed.

Lemma sumZ_sumZ_swap {A B} (f : A -> B -> Z) (xs : list A) (ys : list B) :
  sumZ (fun a => sumZ (f a) (ys)) xs =
  sumZ (fun b => sumZ (fun a => f a b) xs) ys.
Proof.
  revert ys.
  induction xs as [|x xs IH]; intros ys; cbn.
  - now rewrite sumZ_zero.
  - rewrite IH.
    clear IH.
    induction ys as [|y ys IH]; cbn; auto.
    rewrite <- IH.
    lia.
Qed.

Lemma All_Forall {A} (l : list A) f :
  All f l <-> Forall f l.
Proof.
  induction l.
  - split; cbn; auto.
  - split; cbn.
    + intros [fa all].
      constructor; tauto.
    + intros all.
      inversion all; tauto.
Qed.

Lemma all_incl {A} (l l' : list A) f :
  incl l l' -> All f l' -> All f l.
Proof.
  intros incl all.
  apply All_Forall.
  apply All_Forall in all.
  apply Forall_forall.
  pose proof (Forall_forall f l').
  firstorder.
Qed.

Lemma firstn_incl {A} n (l : list A) : incl (firstn n l) l.
Proof.
  unfold incl.
  intros a.
  revert l.
  induction n as [|n IH]; intros l isin; try contradiction.
  cbn in *.
  destruct l; try contradiction.
  cbn in *.
  destruct isin; try tauto.
  right.
  auto.
Qed.

Lemma skipn_incl {A} n (l : list A) : incl (skipn n l) l.
Proof.
  unfold incl.
  intros a.
  revert l.
  induction n as [|n IH]; intros l isin; auto.
  cbn in *.
  destruct l; try contradiction.
  cbn in *.
  right; auto.
Qed.

Lemma sumZ_seq_feq_rel (f g : nat -> Z) len (R : Z -> Z -> Prop) :
  Reflexive R ->
  Proper (R ==> R ==> R) Z.add ->
  (forall i, i < len -> R (f i) (g i))%nat ->
  R (sumZ f (seq 0 len)) (sumZ g (seq 0 len)).
Proof.
  intros refl proper all_same.
  revert f g all_same.
  induction len as [|len IH]; intros f g all_same; auto.
  cbn.
  rewrite 2!(sumZ_seq_n _ 1).
  apply proper.
  - apply all_same; lia.
  - apply IH.
    intros i ilt.
    now specialize (all_same (i + 1)%nat ltac:(lia)).
Qed.

Lemma sumZ_map_id {A} (f : A -> Z) l :
  sumZ f l = sumZ id (map f l).
Proof.
  induction l; cbn; auto.
  unfold id.
  now rewrite IHl.
Qed.

Lemma sumZ_le : forall {A} (f g : A -> Z) (xs : list A),
  (forall x, In x xs -> f x <= g x) ->
  sumZ f xs <= sumZ g xs.
Proof.
  intros A f g xs Hle.
  induction xs as [|x' xs IH].
  - apply Z.le_refl.
  - apply Z.add_le_mono.
    + apply Hle, in_eq.
    + apply IH.
      intros.
      now apply Hle, in_cons.
Qed.

Lemma sumZ_nonnegative : forall {A} (f : A -> Z) (l : list A),
  (forall x, In x l -> 0 <= f x) ->
  0 <= sumZ f l.
Proof.
  intros.
  erewrite <- sumZ_zero.
  now apply sumZ_le.
Qed.

Lemma sumZ_eq : forall {A} (f g : A -> Z) (l : list A),
  (forall x, In x l -> f x = g x) ->
  sumZ f l = sumZ g l.
Proof.
  intros.
  rewrite sumZ_map_id.
  setoid_rewrite sumZ_map_id at 2.
  f_equal.
  now apply map_ext_in.
Qed.

Lemma sumZ_in_le : forall {A} (x : A) (f : A -> Z) (l : list A),
  (forall y, In y l -> 0 <= f y) ->
  In x l ->
  f x <= sumZ f l.
Proof.
  intros * f_positive Hin.
  induction l.
  - inversion Hin.
  - apply in_inv in Hin as [Hin | Hin].
    + cbn. subst.
      rewrite <- (Z.add_0_r (f x)).
      apply Z.add_le_mono.
      * lia.
      * apply sumZ_nonnegative.
        intros.
        apply f_positive.
        now apply in_cons.
    + cbn.
      rewrite <- (Z.add_0_l (f x)).
      apply Z.add_le_mono.
      * apply f_positive.
        apply in_eq.
      * apply IHl; auto.
        intros.
        apply f_positive.
        now apply in_cons.
Qed.

Lemma firstn_map {A B} (f : A -> B) n l :
  firstn n (map f l) = map f (firstn n l).
Proof.
  revert l.
  induction n; intros l; cbn; auto.
  destruct l; cbn; auto.
  apply f_equal.
  auto.
Qed.

Lemma skipn_map {A B} (f : A -> B) n l :
  skipn n (map f l) = map f (skipn n l).
Proof.
  revert l.
  induction n; intros l; cbn; auto.
  destruct l; cbn; auto.
Qed.

Lemma map_nth_alt {A B} n (l : list A) (f : A -> B) d1 d2 :
  (n < length l)%nat ->
  nth n (map f l) d1 = f (nth n l d2).
Proof.
  revert n.
  induction l as [|x xs IH]; intros n nlt; cbn in *; try lia.
  destruct n as [|n]; auto.
  apply IH.
  lia.
Qed.

Local Open Scope nat.
Lemma sumnat_max {A} (f : A -> nat) l max :
  (forall a, In a l -> f a <= max) ->
  sumnat f l <= max * length l.
Proof.
  intros all.
  induction l as [|x xs IH].
  - cbn.
    lia.
  - cbn.
    unshelve epose proof (IH _) as IH.
    + intros a ain.
      apply all; right; auto.
    + specialize (all x (or_introl eq_refl)).
      lia.
Qed.

Lemma list_eq_nth {A} (xs ys : list A) :
  length xs = length ys ->
  (forall i a a', nth_error xs i = Some a -> nth_error ys i = Some a' -> a = a') ->
  xs = ys.
Proof.
  revert ys.
  induction xs as [|x xs IH]; intros ys len_xs all_eq.
  - destruct ys; cbn in *; auto; lia.
  - cbn.
    destruct ys as [|y ys]; cbn in *; try lia.
    rewrite (all_eq 0 x y); cbn; auto.
    apply f_equal.
    apply IH.
    + lia.
    + intros i a b ntha nthb.
      apply all_eq with (S i); cbn; auto.
Qed.

Lemma nth_error_seq_in i start len :
  i < len ->
  nth_error (seq start len) i = Some (start + i).
Proof.
  revert i start.
  induction len as [|len IH]; intros i start ilt; try lia.
  cbn.
  destruct i as [|i]; cbn.
  - f_equal; lia.
  - rewrite IH by lia.
    f_equal; lia.
Qed.

Lemma nth_error_snoc {B} (l : list B) (x : B) :
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  rewrite nth_error_app2 by lia.
  now replace (length l - length l) with 0 by lia.
Qed.

Lemma NoDup_filter {A} (f : A -> bool) l :
  NoDup l ->
  NoDup (filter f l).
Proof.
  intros nodup.
  induction nodup; cbn.
  - constructor.
  - destruct (f x) eqn:fx; auto.
    constructor; auto.
    rewrite filter_In.
    tauto.
Qed.

Lemma NoDup_map {A B} (f : A -> B) l :
  NoDup l ->
  (forall a a', In a l -> In a' l -> f a = f a' -> a = a') ->
  NoDup (map f l).
Proof.
  intros nodup.
  induction nodup; cbn; intros inj.
  - constructor.
  - constructor; auto.
    rewrite in_map_iff.
    intros ex.
    destruct ex as [x' [fxeq inxl]].
    contradiction H.
    replace x with x'; [assumption|].
    apply inj; auto.
Qed.

Lemma filter_all {A} (f : A -> bool) (l : list A) :
  (forall a, In a l -> f a = true) ->
  filter f l = l.
Proof.
  induction l as [|x xs IH]; [easy|]; intros all.
  cbn.
  rewrite all by (now left).
  apply f_equal; apply IH.
  intros a ain.
  apply all; right; auto.
Qed.



Local Open Scope N.
Lemma sumN_permutation {A : Type}
                       {f : A -> N}
                       {xs ys : list A}
                       (perm_eq : Permutation xs ys) :
  sumN f xs = sumN f ys.
Proof.
  induction perm_eq; perm_simplify; lia.
Qed.

#[export]
Instance sumN_perm_proper {A : Type} :
  Proper (eq ==> Permutation (A := A) ==> eq) sumN.
Proof.
  repeat intro. subst. now apply sumN_permutation.
Qed.

Lemma sumN_map {A B : Type} (f : A -> B) (g : B -> N) (xs : list A) :
  sumN g (map f xs) =
  sumN (fun a => g (f a)) xs.
Proof.
  induction xs as [|hd tl IH]; auto.
  cbn.
  now rewrite IH.
Qed.

Lemma sumN_map_id {A} (f : A -> N) l :
  sumN f l =
  sumN id (map f l).
Proof.
  induction l; cbn; auto.
  unfold id.
  now rewrite IHl.
Qed.

Lemma sumN_app {A : Type} {f : A -> N} {xs ys : list A} :
  sumN f (xs ++ ys) =
  sumN f xs + sumN f ys.
Proof.
  revert ys.
  induction xs as [| x xs IH]; intros ys; auto.
  cbn.
  rewrite IH.
  lia.
Qed.

Lemma sumN_split : forall {A : Type} (f : A -> N) (x y z : A) (xs : list A),
  f z = f x + f y ->
  sumN f (z :: xs) =
  sumN f (x :: y :: xs).
Proof.
  cbn. lia.
Qed.

Lemma sumN_swap : forall {A : Type} (f : A -> N) (x y : A) (xs : list A),
  sumN f (x :: y :: xs) =
  sumN f (y :: x :: xs).
Proof.
  intros.
  apply sumN_permutation, perm_swap.
Qed.

Lemma sumN_in_le : forall {A : Type} (f : A -> N) (x : A) (xs : list A),
  In x xs -> f x <= sumN f xs.
Proof.
  intros A f x xs HIn.
  induction xs.
  - inversion HIn.
  - apply in_inv in HIn as [Heq | HIn].
    + cbn.
      subst.
      lia.
    + cbn.
      rewrite IHxs by assumption.
      lia.
Qed.

Lemma sumN_inv : forall {A : Type} (f : A -> N) (x : A) (xs : list A),
  sumN f xs + f x =
  sumN f (x :: xs).
Proof.
  intros.
  cbn.
  now rewrite N.add_comm.
Qed.


Definition isSome {A : Type} (a : option A) :=
  match a with
  | Some _ => true
  | None => false
  end.
Definition isNone {A : Type} (a : option A) :=
  match a with
  | Some _ => false
  | None => true
  end.

Lemma with_default_is_some : forall {A : Type} (x : option A) (y : A),
  isSome x = false ->
    with_default y x = y.
Proof.
  now destruct x.
Qed.

Lemma with_default_indep {A} (o : option A) d d' v :
  o = Some v ->
  with_default d o =
  with_default d' o.
Proof.
  intros; subst; easy.
Qed.

Lemma isSome_some : forall {A : Type} (x : option A) (y : A),
  x = Some y -> isSome x = true.
Proof.
  intros.
  now subst.
Qed.

Lemma isSome_none : forall {A : Type} (x : option A),
  x = None -> isSome x = false.
Proof.
  intros.
  now subst.
Qed.

Lemma isSome_exists : forall {A : Type} (x : option A),
  isSome x = true <-> exists y : A, x = Some y.
Proof.
  split.
  - intros.
    destruct x; eauto.
    discriminate.
  - intros (y & x_eq).
    eapply isSome_some.
    eauto.
Qed.

Lemma isSome_not_exists : forall {A : Type} (x : option A),
  isSome x = false <-> forall y : A, x <> Some y.
Proof.
  split.
  - now destruct x eqn:x_eq.
  - intros x_eq.
    eapply isSome_none.
    destruct x; auto.
    congruence.
Qed.
