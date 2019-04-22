From Coq Require Import Eqdep List Omega Permutation.
Import ListNotations.

Set Implicit Arguments.


Ltac inject H := injection H; clear H; intros; try subst.
Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

(** Workhorse tactic to simplify hypotheses for a variety of proofs.
   * Argument [invOne] is a tuple-list of predicates for which we always do inversion automatically. *)
Ltac simplHyp invOne :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert H F :=
    (** We only proceed for those predicates in [invOne]. *)
    inList F invOne;
    (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
      (inversion H; fail)
    (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
      || (inversion H; [idtac]; clear H; try subst) in

  match goal with
    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F

    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

(** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the extra subgoals added by [rewrite]. *)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(** Combine [autorewrite] with automatic hypothesis rewrites. *)
Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Ltac rewriter := autorewrite with core in *; rewriterP.

Hint Rewrite app_ass.
Hint Rewrite app_comm_cons.

Ltac prove' invOne :=
  let sintuition :=
      simpl in *; intuition auto; try subst;
    repeat (simplHyp invOne; intuition auto; try subst); try congruence in

  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] => rewrite H by prove' invOne
            end; autorewrite with core in *) in

  do 3 (sintuition; autounfold; rewriter); try omega; try (elimtype False; omega).

Ltac prove := prove' fail.

Lemma Permutation_app_middle {A : Type} (xs l1 l2 l3 l4 : list A) :
  Permutation (l1 ++ l2) (l3 ++ l4) ->
  Permutation (l1 ++ xs ++ l2) (l3 ++ xs ++ l4).
Proof.
  Hint Rewrite <- Permutation_middle.
  intros perm.
  induction xs; prove.
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

Ltac case_match :=
  match goal with
  | [H: context [ match ?x with _ => _ end ] |- _] => destruct x eqn:?
  | [|- context [ match ?x with _ => _ end ]] => destruct x eqn:?
  end.

Ltac destruct_units :=
  repeat
    match goal with
    | [u: unit |- _] => destruct u
    end.
