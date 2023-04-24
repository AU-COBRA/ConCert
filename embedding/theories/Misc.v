(** * Some facts not found in the standard library *)
From ConCert.Utils Require Import Automation.
From MetaCoq Require Import utils.
From Coq Require Import List.
From Coq Require Import Lia.

Import ListNotations.

Definition fun_prod {A B C D} (f : A -> C) (g : B -> D) : A * B -> C * D :=
  fun x => (f (fst x), g (snd x)).

Lemma forallb_Forall_iff {A} (p : A -> bool) (l : list A):
  Forall (fun x => p x = true) l <-> forallb p l = true.
Proof.
  split.
  + induction l; intros H.
    * reflexivity.
    * simpl. inversion H as [H1 | a1 l1 Heq]. subst. rewrite Heq. simpl.
      now eapply IHl.
  + induction l; intros H.
    * constructor.
    * simpl in *. rewrite Bool.andb_true_iff in *. destruct H.
      constructor; auto.
Qed.

Lemma Forall_impl_inner {A} (P Q : A -> Prop) l :
  Forall P l -> Forall (fun x => P x -> Q x) l ->
  Forall Q l.
Proof.
  intros HP. induction HP; intros HQ.
  + constructor.
  + constructor; inversion HQ; auto.
Qed.


Lemma All_impl_inner {A} (P Q : A -> Type) l :
  All P l -> All (fun x => P x -> Q x) l ->
  All Q l.
Proof.
  intros HP. induction HP; intros HQ.
  + constructor.
  + constructor; inversion HQ; auto.
Qed.

Lemma forallb_impl_inner {A} {p q} {l : list A} :
  forallb p l -> (forall x, p x = true -> q x = true) -> forallb q l.
Proof.
  revert p q.
  induction l; simpl; intros p q Hfa H; auto.
  now propify.
Qed.

Lemma Forall_In {A} x (xs : list A) P :
  In x xs ->
  Forall P xs ->
  P x.
Proof.
  revert x.
  induction xs; intros x Hin Hfa; auto.
  * inversion Hin.
  * simpl in *. destruct Hin; subst; inversion Hfa; eauto.
Qed.

Lemma forallb_In {A} x (xs : list A) p :
  In x xs ->
  forallb p xs ->
  p x.
Proof.
  revert x.
  induction xs; intros x Hin Hfa; auto.
  simpl in *. propify.
  now destruct_or_hyps.
Qed.


Section CombineProp.

  Lemma combine_app : forall A B (l2 l2': list B) (l1 l1' : list A),
    #|l1| = #|l2| ->
    combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
  Proof.
    induction l2.
    + simpl. intros l2' l1 l1' Heq. destruct l1; try discriminate; reflexivity.
    + simpl. intros l2' l1 l1' Heq. destruct l1; cbn; inversion Heq.
      simpl. apply f_equal2; eauto.
  Qed.

  Lemma combine_rev : forall A B (l2 : list B) (l1 : list A),
    #|l1| = #|l2| ->
    combine (rev l1) (rev l2) = rev (combine l1 l2).
  Proof.
    intros A B.
    induction l2 using rev_ind.
    + simpl. intros l1 Heq. destruct l1; eauto.
      simpl; destruct (rev l1 ++ [a]); reflexivity.
    + simpl. intros l1 Heq. destruct l1 using rev_ind; auto.
      repeat rewrite app_length in Heq; simpl in *.
      assert (#|l1| = #|l2|) by lia.
      repeat rewrite rev_unit. simpl.
      rewrite IHl2 by auto.
      rewrite combine_app by auto.
      simpl. now rewrite rev_unit.
  Qed.

  Lemma map_combine_snd : forall A B (l2 : list B) (l1 : list A),
    #|l1| = #|l2| ->
   map snd (combine l1 l2) = l2.
  Proof.
    induction l2.
    + simpl. intros l1 Heq. destruct l1; reflexivity.
    + simpl. intros l1 Heq. destruct l1; cbn. inversion Heq.
      simpl. apply f_equal2; eauto.
  Qed.


  Lemma map_map_combine_snd : forall A B C (f : B -> C) (l2 : list B) (l1 : list A),
      #|l1| = #|l2| ->
      (map f l2) = map f (map snd (combine l1 l2)).
  Proof.
    intros; now rewrite map_combine_snd.
  Qed.

  Lemma map_combine_snd_funprod :
    forall A B C (f : B -> C) (l1 : list A) (l2 : list B),
      map (fun_prod id f) (combine l1 l2) = combine l1 (map f l2).
  Proof.
    induction l1; intros.
    + reflexivity.
    + destruct l2.
      * reflexivity.
      * cbn. f_equal. apply IHl1.
  Qed.

End CombineProp.
