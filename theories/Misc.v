From ConCert Require Import CustomTactics.
From MetaCoq Require Import utils.
Require Import List.


Lemma forallb_Forall_iff {A} (p : A -> bool) (l : list A):
  Forall (fun x => p x = true) l <-> forallb p l = true.
Proof.
  split.
  + induction l;intros H.
    * reflexivity.
    * simpl. inversion H as [H1 | a1 l1 Heq]. subst. rewrite Heq. simpl.
      now eapply IHl.
  + induction l;intros H.
    * constructor.
    * simpl in *. rewrite Bool.andb_true_iff in *. destruct H.
      constructor;auto.
Qed.

Lemma Forall_impl_inner {A} (P Q : A -> Prop) l :
  Forall P l -> Forall (fun x => P x -> Q x) l ->
  Forall Q l.
Proof.
  intros HP. induction HP;intros HQ.
  + constructor.
  + constructor;inversion HQ;auto.
Qed.


Lemma All_impl_inner {A} (P Q : A -> Type) l :
  All P l -> All (fun x => P x -> Q x) l ->
  All Q l.
Proof.
  intros HP. induction HP;intros HQ.
  + constructor.
  + constructor;inversion HQ;auto.
Qed.

Lemma forallb_impl_inner {A} {p q} {l : list A} :
  forallb p l -> (forall x, p x = true -> q x = true) -> forallb q l.
Proof.
  revert p q.
  induction l;simpl;intros p q Hfa H;auto.
  inv_andb Hfa. split_andb;try eapply IHl;eauto.
Qed.
