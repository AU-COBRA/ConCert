(* This file implements various helper functions and proofs *)

From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import Morphisms.
From Coq Require Import Psatz.
From Coq Require Import Eqdep_dec.
Require Import Automation.
Import ListNotations.

Fixpoint find_first {A B : Type} (f : A -> option B) (l : list A)
  : option B :=
  match l with
  | hd :: tl => match f hd with
                | Some b => Some b
                | None => find_first f tl
                end
  | [] => None
  end.

Fixpoint map_option {A B : Type} (f : A -> option B) (l : list A)
  : list B :=
  match l with
  | hd :: tl => match f hd with
                  | Some b => b :: map_option f tl
                  | None => map_option f tl
                end
  | [] => []
  end.

Definition with_default {A : Type} (a : A) (o : option A) : A :=
  match o with
  | Some v => v
  | None => a
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

Lemma sumnat_app
      {A : Type} {f : A -> nat} {xs ys : list A} :
  sumnat f (xs ++ ys) = sumnat f xs + sumnat f ys.
Proof.
  revert ys.
  induction xs as [| x xs IH]; intros ys; auto.
  cbn.
  rewrite IH.
  lia.
Qed.

Lemma sumnat_permutation
      {A : Type} {f : A -> nat} {xs ys : list A}
      (perm_eq : Permutation xs ys) :
  sumnat f xs = sumnat f ys.
Proof. induction perm_eq; perm_simplify; lia. Qed.

Instance sumnat_perm_proper {A : Type} :
  Proper (eq ==> Permutation (A:=A) ==> eq) sumnat.
Proof. repeat intro. subst. now apply sumnat_permutation. Qed.

Lemma sumZ_permutation
      {A : Type} {f : A -> Z} {xs ys : list A}
      (perm_eq : Permutation xs ys) :
  sumZ f xs = sumZ f ys.
Proof. induction perm_eq; perm_simplify; lia. Qed.

Instance sumZ_perm_proper {A : Type} :
  Proper (eq ==> Permutation (A:=A) ==> eq) sumZ.
Proof. repeat intro. subst. now apply sumZ_permutation. Qed.

Local Open Scope Z.
Lemma sumZ_app
      {A : Type} {f : A -> Z} {xs ys : list A} :
  sumZ f (xs ++ ys) = sumZ f xs + sumZ f ys.
Proof.
  revert ys.
  induction xs as [| x xs IH]; intros ys; auto.
  cbn.
  rewrite IH.
  lia.
Qed.

Lemma in_app_cons_or {A : Type} (x y : A) (xs ys : list A) :
  x <> y ->
  In x (xs ++ y :: ys) ->
  In x (xs ++ ys).
Proof.
  intros x_neq_y x_in.
  apply in_or_app.
  apply in_app_or in x_in.
  destruct x_in as [?|x_in]; auto.
  destruct x_in; auto; congruence.
Qed.

Lemma incl_split {A : Type} (l m n : list A) :
  incl (l ++ m) n -> incl l n /\ incl m n.
Proof.
  intros H.
  unfold incl in *.
  Hint Resolve in_or_app : core.
  auto.
Qed.

Lemma NoDup_incl_reorganize
      {A : Type}
      (l l' : list A) :
  NoDup l' ->
  incl l' l ->
  exists suf, Permutation (l' ++ suf) l.
Proof.
  revert l.
  induction l' as [| x xs IH]; intros l nodup_l' incl_l'_l.
  - exists l. apply Permutation_refl.
  - assert (x_in_l: In x l).
    + apply (incl_l'_l x). left. constructor.
    + destruct (in_split _ _ x_in_l) as [pref [suf eq]]; subst.
      inversion nodup_l'; subst.
      assert (incl xs (pref ++ suf)).
      * intros a a_in.
        apply in_or_app.
        apply (incl_split [x] xs _) in incl_l'_l.
        destruct incl_l'_l as [incl_x incl_xs].
        intuition.
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

Lemma sumZ_seq_S f start len :
  sumZ f (seq start (S len)) = sumZ f (seq start len) + f (start + len)%nat.
Proof.
  replace (S len) with (len + 1)%nat by lia.
  rewrite (seq_app start len 1).
  rewrite sumZ_app.
  cbn.
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

Instance Forall_Permutation_proper {A} :
  Proper (eq ==> @Permutation A ==> iff) (@Forall A).
Proof.
  intros f f' ? xs ys perm.
  subst f'.
  split; apply forall_respects_permutation; auto; symmetry; auto.
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
