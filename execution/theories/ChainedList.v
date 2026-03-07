(* This file implements a 'chained list'. This can essentially be
thought of as the proof-relevant transitive reflexive closure of
a relation. That is, each link (element) has a "from" point that
must match the previous element's "to" point. *)
From ConCert.Utils Require Import Automation.
Section ChainedList.
  Context {Point : Type} {Link : Point -> Point -> Type}.

  Inductive ChainedList : Point -> Point -> Type :=
    | clnil : forall {p}, ChainedList p p
    | snoc : forall {from mid to},
        ChainedList from mid -> Link mid to -> ChainedList from to.

  Fixpoint clist_app
            {from mid to}
            (xs : ChainedList from mid)
            (ys : ChainedList mid to) : ChainedList from to :=
    match ys with
    | clnil => fun xs => xs
    | snoc ys' y => fun xs => snoc (clist_app xs ys') y
    end xs.

  Infix "++" := clist_app (right associativity, at level 60).

  Definition clist_prefix
            {from mid to}
            (prefix : ChainedList from mid)
            (full : ChainedList from to) : Prop :=
    exists suffix, full = prefix ++ suffix.

  Definition clist_suffix
            {from mid to}
            (suffix : ChainedList mid to)
            (full : ChainedList from to) : Prop :=
    exists prefix, full = prefix ++ suffix.

  Infix "`prefix_of`" := clist_prefix (at level 70).
  Infix "`suffix_of`" := clist_suffix (at level 70).

  Section Theories.
  Lemma app_clnil_l {from to} (xs : ChainedList from to) :
    clnil ++ xs = xs.
  Proof. induction xs; auto; cbn; solve_by_rewrite. Qed.

  Lemma clist_app_assoc
        {c1 c2 c3 c4}
        (xs : ChainedList c1 c2)
        (ys : ChainedList c2 c3)
        (zs : ChainedList c3 c4) :
    xs ++ ys ++ zs = (xs ++ ys) ++ zs.
  Proof. induction zs; intros; auto; cbn; solve_by_rewrite. Qed.
  End Theories.

  Lemma prefix_of_app
        {from mid to to'}
        {prefix : ChainedList from mid}
        {xs : ChainedList from to}
        {suffix : ChainedList to to'} :
    prefix `prefix_of` xs ->
    prefix `prefix_of` xs ++ suffix.
  Proof.
    intros [ex_suffix ex_suffix_eq_app].
    exists (ex_suffix ++ suffix).
    rewrite clist_app_assoc; congruence.
  Qed.
End ChainedList.

Declare Scope clist_scope.
Delimit Scope clist_scope with trace.
Bind Scope clist_scope with ChainedList.
Infix "++" := clist_app (right associativity, at level 60) : clist_scope.

Infix "`prefix_of`" := clist_prefix (at level 70) : clist_scope.
Infix "`suffix_of`" := clist_suffix (at level 70) : clist_scope.

Arguments ChainedList : clear implicits.
