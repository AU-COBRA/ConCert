(* This file implements various helper tactics *)

From Coq Require Import Eqdep List Omega Permutation.
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

(* Change all x :: l into [x] ++ l *)
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

(* Automatically tries to solve obvious "Permutation x y" goals. *)
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
