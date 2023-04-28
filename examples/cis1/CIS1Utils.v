From Coq Require Import List.

Import ListNotations.

Module RemoveProperties.

  Lemma not_in_remove_same {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A):
    ~ In x l -> remove eq_dec x l = l.
  Proof.
    induction l.
    + auto.
    + intros Hnotin. cbn in *.
      destruct (eq_dec x a); intuition; congruence.
  Qed.

    Lemma not_in_remove {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A):
    ~ In x l -> ~ In x (remove eq_dec y l).
  Proof.
    induction l.
    + auto.
    + intros Hnotin. cbn in *.
      destruct (eq_dec y a); cbn in *; intuition; auto.
  Qed.

  Lemma remove_remove {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A) :
    ~ In x (remove eq_dec y (remove eq_dec x l)).
  Proof.
    induction l; auto; simpl in *.
    destruct (eq_dec x a); subst; intuition; simpl in *.
    destruct (eq_dec y a); subst; intuition; simpl in *.
    intuition; simpl in *.
  Qed.

  Lemma In_remove {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A) :
    x <> y -> In x (remove eq_dec y l) -> In x l.
  Proof.
    induction l; intros Hneq Hin; auto; simpl in *.
    subst. destruct (eq_dec y a); subst; cbn in *; auto; intuition; auto.
  Qed.

  Lemma neq_not_removed {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A) :
    x <> y -> In x l -> In x (remove eq_dec y l).
  Proof.
    induction l; intros Hneq Hin; auto; simpl in *.
    destruct Hin.
    + subst. destruct (eq_dec y x); subst; cbn; auto; try congruence.
    + destruct (eq_dec y a); cbn; auto.
  Qed.

  #[local]
  Hint Constructors NoDup : hints.
  #[local]
  Hint Resolve In_remove remove_In not_in_remove_same not_in_remove remove_remove neq_not_removed : hints.

  Fixpoint remove_all {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (to_remove : list A) (xs : list A) :=
    match to_remove with
    | [] => xs
    | x :: tl => remove eq_dec x (remove_all eq_dec tl xs)
    end.

  Lemma remove_all_In {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (to_remove : list A) (xs : list A) :
    Forall (fun x => ~ In x (remove_all eq_dec to_remove xs)) to_remove.
  Proof.
    revert dependent xs.
    induction to_remove; simpl; auto.
    constructor; eauto with hints.
    unshelve eapply (@Forall_impl _ _ _ _ _ (IHto_remove xs)).
    intros x H HH.
    apply (not_in_remove _ _ _ _ H HH).
  Qed.

  Lemma In_remove_all {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (to_remove : list A) (xs : list A) (x : A):
    ~ (In x to_remove) -> In x (remove_all eq_dec to_remove xs) -> In x xs.
  Proof.
    induction to_remove; cbn in *; intuition; eauto with hints.
  Qed.

  Lemma remove_all_not_in_to_remove {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (to_remove : list A) (xs : list A) (x : A):
    ~ (In x to_remove) -> In x xs -> In x (remove_all eq_dec to_remove xs).
  Proof.
    intros H1 H2.
    induction to_remove; cbn in *; intuition auto with *; eauto with hints.
  Qed.

  Lemma NoDup_remove {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A) :
    NoDup l -> NoDup (remove eq_dec x l).
  Proof.
    induction l; intros H0; auto; simpl.
    inversion H0; destruct (eq_dec x a); subst; intuition auto with *; simpl in *; eauto with hints.
  Qed.

  #[local]
  Hint Resolve NoDup_remove : hints.
  #[local]
  Hint Resolve In_remove : hints.

  Lemma remove_extensional {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) (y : A) :
    (forall x, In x l1 <-> In x l2 ) -> (forall x, In x (remove eq_dec y l1) <-> In x (remove eq_dec y l2)).
  Proof.
    intros H x.
    split.
    + intros Hin.
      destruct (eq_dec x y); subst.
      * exfalso. apply (remove_In _ _ _ Hin).
      * destruct (H x); intuition; eauto with hints.
    + intros Hin.
      destruct (eq_dec x y); subst.
      * exfalso. apply (remove_In _ _ _ Hin).
      * destruct (H x); intuition; eauto with hints.
  Qed.

End RemoveProperties.
