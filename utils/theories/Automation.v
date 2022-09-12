(** * This file implements various helper tactics *)
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import ZArith.
Import ListNotations.

Lemma Permutation_app_middle {A : Type} (xs l1 l2 l3 l4 : list A) :
  Permutation (l1 ++ l2) (l3 ++ l4) ->
  Permutation (l1 ++ xs ++ l2) (l3 ++ xs ++ l4).
Proof.
  intros perm.
  rewrite 2!(Permutation_app_comm xs).
  rewrite 2!app_assoc.
  apply Permutation_app_tail.
  auto.
Qed.

(** Change all x :: l into [x] ++ l *)
Ltac appify :=
  match goal with
  | [|- context[?e :: ?l]] =>
    match l with
    | nil => fail 1
    | _ => change (e :: l) with ([e] ++ l)
    end
  end.

Local Ltac reassoc_right :=
  match goal with
  | [|- Permutation _ (?l1 ++ ?l2 ++ ?l3)] => rewrite (app_assoc l1 l2 l3)
  end.

Local Ltac reassoc_left :=
  match goal with
  | [|- Permutation (?l1 ++ ?l2 ++ ?l3) _] => rewrite (app_assoc l1 l2 l3)
  end.

Local Ltac unassoc_right :=
  repeat
    match goal with
    | [|- Permutation _ ((?l1 ++ ?l2) ++ ?l3)] => rewrite <- (app_assoc l1 l2 l3)
    end.

Local Ltac perm_simplify_once :=
  let rec aux :=
      apply Permutation_app_middle ||
      tryif reassoc_right
      then aux
      else (unassoc_right; reassoc_left; aux) in
  repeat rewrite <- app_assoc;
  aux.

Local Ltac perm_simplify_round :=
  cbn;
  repeat appify;
  (* Change into [] ++ l ++ [] *)
  match goal with
  | [|- Permutation ?l1 ?l2] => change l1 with ([] ++ l1);
                                change l2 with ([] ++ l2);
                                rewrite <- (app_nil_r l1), <- (app_nil_r l2)
  end;
  repeat perm_simplify_once;
  cbn;
  repeat rewrite <- app_assoc;
  repeat rewrite app_nil_r;
  repeat
    match goal with
    | [H: Permutation ?l1 ?l2|-_] => rewrite H
    end.

(** Automatically tries to solve obvious "Permutation x y" goals. *)
Ltac perm_simplify :=
  repeat perm_simplify_round;
  cbn;
  try apply Permutation_refl.

Tactic Notation "destruct_match"
       "as" simple_intropattern(L)
       "eqn" ":" ident(x)
       "in" "*" :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr as L eqn:x
  | [H: context [ match ?expr with _ => _ end ] |- _ ] => destruct expr as L eqn:x
  end.

Tactic Notation "destruct_match"
       "as" simple_intropattern(L)
       "in" "*" :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr as L
  | [H: context [ match ?expr with _ => _ end ] |- _ ] => destruct expr as L
  end.

Tactic Notation "destruct_match"
       "eqn" ":" ident(x)
       "in" "*" :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr eqn:x
  | [H: context [ match ?expr with _ => _ end ] |- _ ] => destruct expr eqn:x
  end.

Tactic Notation "destruct_match"
       "in" "*" :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr
  | [H: context [ match ?expr with _ => _ end ] |- _ ] => destruct expr
  end.

Tactic Notation "destruct_match"
       "as" simple_intropattern(L)
       "in" "*" :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr as L
  | [H: context [ match ?expr with _ => _ end ] |- _ ] => destruct expr as L
  end.

Tactic Notation "destruct_match"
       "eqn" ":" ident(x)
       "in" "*" :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr eqn:x
  | [H: context [ match ?expr with _ => _ end ] |- _ ] => destruct expr eqn:x
  end.

Tactic Notation "destruct_match"
       "in" "*" :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr
  | [H: context [ match ?expr with _ => _ end ] |- _ ] => destruct expr
  end.

Tactic Notation "destruct_match"
       "as" simple_intropattern(L)
       "eqn" ":" ident(x) :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr as L eqn:x
  end.

Tactic Notation "destruct_match"
       "as" simple_intropattern(L) :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr as L
  end.

Tactic Notation "destruct_match"
       "eqn" ":" ident(x) :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr eqn:x
  end.

Tactic Notation "destruct_match" :=
  match goal with
  | [|- context [ match ?expr with _ => _ end ] ] => destruct expr
  end.

Tactic Notation "destruct_match"
       "as" simple_intropattern(L)
       "eqn" ":" ident(x)
       "in" hyp(H) :=
  match goal with
  | [H': context [ match ?expr with _ => _ end ] |- _ ] =>
    match H' with H => destruct expr as L eqn:x
    end
  end.

Tactic Notation "destruct_match"
       "as" simple_intropattern(L)
       "in" hyp(H) :=
  match goal with
  | [H': context [ match ?expr with _ => _ end ] |- _ ] =>
    match H' with H => destruct expr as L end
  end.

Tactic Notation "destruct_match"
       "eqn" ":" ident(x)
       "in" hyp(H) :=
  match goal with
  | [H': context [ match ?expr with _ => _ end ] |- _ ] =>
    match H' with H => destruct expr eqn:x end
  end.

Tactic Notation "destruct_match"
       "in" hyp(H) :=
  match goal with
  | [H': context [ match ?expr with _ => _ end ] |- _ ] =>
    match H' with H => destruct expr
    end
  end.

Ltac destruct_units :=
  repeat
    match goal with
    | [u: unit |- _] => destruct u
    end.

Ltac solve_by_rewrite :=
  match goal with
  | [H: _ |- _] => now rewrite H
  end.

Ltac solve_by_inversion :=
  match goal with
  | [H: _ |- _] => solve [inversion H]
  end.

Ltac specialize_hypotheses :=
  repeat
    match goal with
    | [H: _ -> _ |- _] => specialize (H ltac:(auto))
    end.

Ltac unset_all :=
  repeat
    match goal with
    | [var := ?body : ?T |- _] =>
      pose proof (eq_refl : var = body); clearbody var
    end.

Ltac destruct_or_hyps :=
  repeat
    match goal with
    | [H: _ \/ _ |- _] => destruct H
    end.

Ltac destruct_hyps :=
  repeat
    match goal with
    | [H: _ /\ _ |- _] => destruct H
    | [H: exists _, _ |- _] => destruct H
    | [H: _ * _ |- _] => destruct H
    | [H: { x : _ & _ } |- _] => destruct H
    end.

Ltac destruct_and_split :=
  repeat
    match goal with
    | [H: _ /\ _ |- _] => destruct H
    | [H: exists _, _ |- _] => destruct H
    | [H: _ * _ |- _] => destruct H
    | [H: { x : _ & _ } |- _] => destruct H
    | [|- _ /\ _] => split
    end.

Tactic Notation "tryfalse" :=
  try solve [
    elimtype False;
    try solve [assumption | discriminate | congruence]
  ].

Ltac propify :=
  unfold is_true in *;
  repeat
    match goal with
    | [H: context[Z.eqb _ _ = true] |- _] => rewrite Z.eqb_eq in H
    | [H: context[Z.eqb _ _ = false] |- _] => rewrite Z.eqb_neq in H
    | [H: context[Z.ltb _ _ = false] |- _] => rewrite Z.ltb_ge in H
    | [H: context[Z.ltb _ _ = true] |- _] => rewrite Z.ltb_lt in H
    | [H: context[Z.leb _ _ = false] |- _] => rewrite Z.leb_gt in H
    | [H: context[Z.leb _ _ = true] |- _] => rewrite Z.leb_le in H
    | [H: context[Z.gtb _ _] |- _] => rewrite Z.gtb_ltb in H
    | [H: context[Z.geb _ _] |- _] => rewrite Z.geb_leb in H
    | [H: context[N.eqb _ _ = true] |- _] => rewrite N.eqb_eq in H
    | [H: context[N.eqb _ _ = false] |- _] => rewrite N.eqb_neq in H
    | [H: context[N.ltb _ _ = false] |- _] => rewrite N.ltb_ge in H
    | [H: context[N.ltb _ _ = true] |- _] => rewrite N.ltb_lt in H
    | [H: context[N.leb _ _ = false] |- _] => rewrite N.leb_gt in H
    | [H: context[N.leb _ _ = true] |- _] => rewrite N.leb_le in H
    | [H: context[Nat.eqb _ _ = false] |- _] => rewrite Nat.eqb_neq in H
    | [H: context[Nat.eqb _ _ = true] |- _] => rewrite Nat.eqb_eq in H
    | [H: context[Nat.ltb _ _ = false] |- _] => rewrite Nat.ltb_ge in H
    | [H: context[Nat.ltb _ _ = true] |- _] => rewrite Nat.ltb_lt in H
    | [H: context[Nat.leb _ _ = false] |- _] => rewrite Nat.leb_gt in H
    | [H: context[Nat.leb _ _ = true] |- _] => rewrite Nat.leb_le in H
    | [H: context[andb _ _ = false] |- _] => rewrite Bool.andb_false_iff in H
    | [H: context[andb _ _ = true] |- _] => rewrite Bool.andb_true_iff in H
    | [H: context[negb _ = false] |- _] => rewrite Bool.negb_false_iff in H
    | [H: context[negb _ = true] |- _] => rewrite Bool.negb_true_iff in H
    | [H: context[orb _ _ = false] |- _] => rewrite Bool.orb_false_iff in H
    | [H: context[orb _ _ = true] |- _] => rewrite Bool.orb_true_iff in H
    | [|- context[Z.eqb _ _ = true]] => rewrite Z.eqb_eq
    | [|- context[Z.eqb _ _ = false]] => rewrite Z.eqb_neq
    | [|- context[Z.ltb _ _ = false]] => rewrite Z.ltb_ge
    | [|- context[Z.ltb _ _ = true]] => rewrite Z.ltb_lt
    | [|- context[Z.leb _ _ = false]] => rewrite Z.leb_gt
    | [|- context[Z.leb _ _ = true]] => rewrite Z.leb_le
    | [|- context[Z.gtb _ _]] => rewrite Z.gtb_ltb
    | [|- context[Z.geb _ _]] => rewrite Z.geb_leb
    | [|- context[N.eqb _ _ = true]] => rewrite N.eqb_eq
    | [|- context[N.eqb _ _ = false]] => rewrite N.eqb_neq
    | [|- context[N.ltb _ _ = false]] => rewrite N.ltb_ge
    | [|- context[N.ltb _ _ = true]] => rewrite N.ltb_lt
    | [|- context[N.leb _ _ = false]] => rewrite N.leb_gt
    | [|- context[N.leb _ _ = true]] => rewrite N.leb_le
    | [|- context[Nat.eqb _ _ = false]] => rewrite Nat.eqb_neq
    | [|- context[Nat.eqb _ _ = true]] => rewrite Nat.eqb_eq
    | [|- context[Nat.ltb _ _ = false]] => rewrite Nat.ltb_ge
    | [|- context[Nat.ltb _ _ = true]] => rewrite Nat.ltb_lt
    | [|- context[Nat.leb _ _ = false]] => rewrite Nat.leb_gt
    | [|- context[Nat.leb _ _ = true]] => rewrite Nat.leb_le
    | [|- context[andb _ _ = false]] => rewrite Bool.andb_false_iff
    | [|- context[andb _ _ = true]] => rewrite Bool.andb_true_iff
    | [|- context[negb _ = false]] => rewrite Bool.negb_false_iff
    | [|- context[negb _ = true]] => rewrite Bool.negb_true_iff
    | [|- context[orb _ _ = false]] => rewrite Bool.orb_false_iff
    | [|- context[orb _ _ = true]] => rewrite Bool.orb_true_iff
    end.
