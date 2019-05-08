(* A place for various tactic used for the development*)

(** * Tactics taken from the Software Foundations' LibTactics.v *)

Set Implicit Arguments.

(* ================================================================= *)
(** ** Untyped Arguments for Tactics *)

(** Any Coq value can be boxed into the type [Boxer]. This is
    useful to use Coq computations for implementing tactics. *)

Inductive Boxer : Type :=
  | boxer : forall (A:Type), A -> Boxer.


(* ================================================================= *)
(** ** Numbers as Arguments *)

(** When tactic takes a natural number as argument, it may be
    parsed either as a natural number or as a relative number.
    In order for tactics to convert their arguments into natural numbers,
    we provide a conversion tactic. *)

Require BinPos Coq.ZArith.BinInt List.

Require Coq.Numbers.BinNums Coq.ZArith.BinInt.

Import List.ListNotations.

Definition ltac_int_to_nat (x:BinInt.Z) : nat :=
  match x with
  | BinInt.Z0 => 0%nat
  | BinInt.Zpos p => BinPos.nat_of_P p
  | BinInt.Zneg p => 0%nat
  end.

Ltac number_to_nat N :=
  match type of N with
  | nat => constr:(N)
  | BinInt.Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  end.


(* ================================================================= *)
(** ** Absurd Goals *)

(** [false_goal] replaces any goal by the goal [False].
    Contrary to the tactic [false] (below), it does not try to do
    anything else *)

Tactic Notation "false_goal" :=
  elimtype False.

(** [false_post] is the underlying tactic used to prove goals
    of the form [False]. In the default implementation, it proves
    the goal if the context contains [False] or an hypothesis of the
    form [C x1 .. xN  =  D y1 .. yM], or if the [congruence] tactic
    finds a proof of [x <> x] for some [x]. *)

Ltac false_post :=
  solve [ assumption | discriminate | congruence ].

(** [false] replaces any goal by the goal [False], and calls [false_post] *)

Tactic Notation "false" :=
  false_goal; try false_post.

(** [tryfalse] tries to solve a goal by contradiction, and leaves
    the goal unchanged if it cannot solve it.
    It is equivalent to [try solve \[ false \]]. *)

Tactic Notation "tryfalse" :=
  try solve [ false ].

Ltac some_inv := repeat (match goal with
                         | [H: Some _ = Some _ |- _] => inversion H; clear H
                         end).

(* ================================================================= *)
(** ** Deconstructing Terms *)

(** [get_head E] is a tactic that returns the head constant of the
    term [E], ie, when applied to a term of the form [P x1 ... xN]
    it returns [P]. If [E] is not an application, it returns [E].
    Warning: the tactic seems to loop in some cases when the goal is
    a product and one uses the result of this function. *)

Ltac get_head E :=
  match E with
  | ?P _ _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ => constr:(P)
  | ?P _ _ _ => constr:(P)
  | ?P _ _ => constr:(P)
  | ?P _ => constr:(P)
  | ?P => constr:(P)
  end.


(* ================================================================= *)
(** ** Unfolding *)

(** [unfolds] unfolds the head definition in the goal, i.e. if the
    goal has form [P x1 ... xN] then it calls [unfold P].
    If the goal is an equality, it tries to unfold the head constant
    on the left-hand side, and otherwise tries on the right-hand side.
    If the goal is a product, it calls [intros] first.
    -- warning: this tactic is overriden in LibReflect. *)

Ltac apply_to_head_of E cont :=
  let go E :=
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.

Ltac unfolds_base :=
  match goal with |- ?G =>
   apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
  unfolds_base.

(** [unfolds in H] unfolds the head definition of hypothesis [H], i.e. if
    [H] has type [P x1 ... xN] then it calls [unfold P in H]. *)

Ltac unfolds_in_base H :=
  match type of H with ?G =>
   apply_to_head_of G ltac:(fun P => unfold P in H) end.

Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H.

(** [unfolds in H1,H2,..,HN] allows unfolding the head constant
    in several hypotheses at once. *)

Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) :=
  unfolds in H1; unfolds in H2.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) :=
  unfolds in H1; unfolds in H2 H3.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
  unfolds in H1; unfolds in H2 H3 H4.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) :=
  unfolds in H1; unfolds in H2 H3 H4 H5.


(* ################################################################# *)
(** * N-ary Conjunctions and Disjunctions *)

(** N-ary Conjunctions Splitting in Goals *)

(** Underlying implementation of [splits]. *)

Ltac splits_tactic N :=
  match N with
  | O => fail
  | S O => idtac
  | S ?N' => split; [| splits_tactic N']
  end.

Ltac unfold_goal_until_conjunction :=
  match goal with
  | |- _ /\ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_conjunction
  end.

Ltac get_term_conjunction_arity T :=
  match T with
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(8)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(7)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(6)
  | _ /\ _ /\ _ /\ _ /\ _ => constr:(5)
  | _ /\ _ /\ _ /\ _ => constr:(4)
  | _ /\ _ /\ _ => constr:(3)
  | _ /\ _ => constr:(2)
  | _ -> ?T' => get_term_conjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_conjunction_arity T'
         end
         (* --TODO: warning this can loop... *)
  end.

Ltac get_goal_conjunction_arity :=
  match goal with |- ?T => get_term_conjunction_arity T end.

(** [splits] applies to a goal of the form [(T1 /\ .. /\ TN)] and
    destruct it into [N] subgoals [T1] .. [TN]. If the goal is not a
    conjunction, then it unfolds the head definition. *)

Tactic Notation "splits" :=
  unfold_goal_until_conjunction;
  let N := get_goal_conjunction_arity in
  splits_tactic N.

(** [splits N] is similar to [splits], except that it will unfold as many
    definitions as necessary to obtain an [N]-ary conjunction. *)

Tactic Notation "splits" constr(N) :=
  let N := number_to_nat N in
  splits_tactic N.

(** N-ary Conjunctions Deconstruction *)

(** Underlying implementation of [destructs]. *)

Ltac destructs_conjunction_tactic N T :=
  match N with
  | 2 => destruct T as [? ?]
  | 3 => destruct T as [? [? ?]]
  | 4 => destruct T as [? [? [? ?]]]
  | 5 => destruct T as [? [? [? [? ?]]]]
  | 6 => destruct T as [? [? [? [? [? ?]]]]]
  | 7 => destruct T as [? [? [? [? [? [? ?]]]]]]
  end.

(** [destructs T] allows destructing a term [T] which is a N-ary
    conjunction. It is equivalent to [destruct T as (H1 .. HN)],
    except that it does not require to manually specify N different
    names. *)

Tactic Notation "destructs" constr(T) :=
  let TT := type of T in
  let N := get_term_conjunction_arity TT in
  destructs_conjunction_tactic N T.

(** [destructs N T] is equivalent to [destruct T as (H1 .. HN)],
    except that it does not require to manually specify N different
    names. Remark that it is not restricted to N-ary conjunctions. *)

Tactic Notation "destructs" constr(N) constr(T) :=
  let N := number_to_nat N in
  destructs_conjunction_tactic N T.




Section equatesLemma.
Variables (A0 A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).

Lemma equates_0 : forall (P Q:Prop),
  P -> P = Q -> Q.
Proof. intros. subst. auto. Qed.

Lemma equates_1 :
  forall (P:A0->Prop) x1 y1,
  P y1 -> x1 = y1 -> P x1.
Proof. intros. subst. auto. Qed.

Lemma equates_2 :
  forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
  P y1 x2 -> x1 = y1 -> P x1 x2.
Proof. intros. subst. auto. Qed.

Lemma equates_3 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
  P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.
Proof. intros. subst. auto. Qed.

Lemma equates_4 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
  P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.
Proof. intros. subst. auto. Qed.


(* Ltac apply_eq H n := *)
(*   match number_to_nat n with *)
(*   | 0 => eapply equates_0;[eapply H | ] *)
(*   | 1 => eapply equates_1;[eapply H | ] *)
(*   | 2 => eapply equates_2;[eapply H | ] *)
(*   end. *)

End equatesLemma.