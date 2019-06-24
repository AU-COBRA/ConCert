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
  simpl;
  repeat appify;
  (* Change into [] ++ l ++ [] *)
  match goal with
  | [|- Permutation ?l1 ?l2] => change l1 with ([] ++ l1);
                                change l2 with ([] ++ l2);
                                rewrite <- (app_nil_r l1), <- (app_nil_r l2)
  end;
  repeat perm_simplify_once;
  simpl;
  repeat rewrite <- app_assoc;
  repeat rewrite app_nil_r;
  repeat
    match goal with
    | [H: Permutation ?l1 ?l2|-_] => rewrite H
    end.

Ltac perm_simplify :=
  repeat perm_simplify_round;
  simpl;
  try apply Permutation_refl.

Ltac destruct_match :=
  match goal with
  | [|- context [ match ?x with _ => _ end ]] => destruct x eqn:?
  | [H: context [ match ?x with _ => _ end ] |- _] => destruct x eqn:?
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
