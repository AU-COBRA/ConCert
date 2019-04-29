(* This file implements, for lack of a better name, a cursor list.
This is a list for which each element contains a "cursor" type: each
element is parameterized over a 'from' and 'to' element of this type,
which must match with the previous element. For that reason this is
also a snoc list. Note that this is not unlike fhlist from CPDT,
except we place further restrictions on it. *)
From SmartContracts Require Import Automation.
Section CursorList.
Context {cursor_type : Type} {elm_type : cursor_type -> cursor_type -> Type}.

Inductive CursorList : cursor_type -> cursor_type -> Type :=
  | nil : forall {elm}, CursorList elm elm
  | snoc : forall {from mid to}, CursorList from mid -> elm_type mid to -> CursorList from to.

Definition snoc_eq
           {from mid mid' to}
           (xs : CursorList from mid)
           (x : elm_type mid' to) :
  mid' = mid -> CursorList from to :=
  fun eq =>
    snoc xs (match eq with eq_refl => x end).

Fixpoint clist_app
           {from mid to}
           (xs : CursorList from mid)
           (ys : CursorList mid to) : CursorList from to :=
  match ys with
  | nil => fun xs => xs
  | snoc ys' y => fun xs => snoc (clist_app xs ys') y
  end xs.

Infix "++" := clist_app (right associativity, at level 60).

Definition clist_prefix
           {from mid to}
           (prefix : CursorList from mid)
           (full : CursorList from to) : Prop :=
  exists suffix, full = prefix ++ suffix.

Definition clist_suffix
           {from mid to}
           (suffix : CursorList mid to)
           (full : CursorList from to) : Prop :=
  exists prefix, full = prefix ++ suffix.

Infix "`prefix_of`" := clist_prefix (at level 70).
Infix "`suffix_of`" := clist_suffix (at level 70).

Section Theories.
Lemma clist_app_nil_l {from to} (xs : CursorList from to) :
  nil ++ xs = xs.
Proof. induction xs; auto; cbn; solve_by_rewrite. Qed.

Lemma clist_app_assoc
      {c1 c2 c3 c4}
      (xs : CursorList c1 c2)
      (ys : CursorList c2 c3)
      (zs : CursorList c3 c4) :
  xs ++ ys ++ zs = (xs ++ ys) ++ zs.
Proof. induction zs; intros; auto; cbn; solve_by_rewrite. Qed.
End Theories.

Lemma prefix_of_app
      {from mid to to'}
      {prefix : CursorList from mid}
      {xs : CursorList from to}
      {suffix : CursorList to to'} :
  prefix `prefix_of` xs ->
  prefix `prefix_of` xs ++ suffix.
Proof.
  intros [ex_suffix ex_suffix_eq_app].
  exists (ex_suffix ++ suffix).
  rewrite clist_app_assoc; congruence.
Qed.
End CursorList.

Delimit Scope clist_scope with trace.
Bind Scope clist_scope with CursorList.
Infix "++" := clist_app (right associativity, at level 60) : clist_scope.

Infix "`prefix_of`" := clist_prefix (at level 70) : clist_scope.
Infix "`suffix_of`" := clist_suffix (at level 70) : clist_scope.

Arguments CursorList : clear implicits.
