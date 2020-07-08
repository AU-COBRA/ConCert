From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import WcbvEvalAux.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import Morphisms.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import RelationClasses.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Import EAstUtils.

Reserved Infix "β=" (at level 70, right associativity).

Inductive betaeq : term -> term -> Prop :=
| betaeq_beta na body arg : tApp (tLambda na body) arg β= body{0 := arg}
| betaeq_evar i ts ts' :
    betaeq_terms ts ts' ->
    tEvar i ts β= tEvar i ts'
| betaeq_lambda na body body' :
    body β= body' ->
    tLambda na body β= tLambda na body'
| betaeq_let_in na val val' body body' :
    val β= val' ->
    body β= body' ->
    tLetIn na val body β= tLetIn na val' body'
| betaeq_app hd hd' arg arg' :
    hd β= hd' ->
    arg β= arg' ->
    tApp hd arg β= tApp hd' arg'
| betaeq_case p disc disc' brs brs' :
    disc β= disc' ->
    betaeq_branches brs brs' ->
    tCase p disc brs β= tCase p disc' brs'
| betaeq_proj p t t' :
    t β= t' ->
    tProj p t β= tProj p t'
| betaeq_fix defs defs' i :
    betaeq_defs defs defs' ->
    tFix defs i β= tFix defs' i
| betaeq_cofix defs defs' i :
    betaeq_defs defs defs' ->
    tCoFix defs i β= tCoFix defs' i
| betaeq_refl t : t β= t
| betaeq_sym t t' : t β= t' -> t' β= t
| betaeq_trans a b c :
    a β= b ->
    b β= c ->
    a β= c

with betaeq_terms : list term -> list term -> Prop :=
| betaeq_terms_nil : betaeq_terms [] []
| betaeq_terms_cons t t' ts ts' :
    t β= t' ->
    betaeq_terms ts ts' ->
    betaeq_terms (t :: ts) (t' :: ts')

with betaeq_branches : list (nat × term) -> list (nat × term) -> Prop :=
| betaeq_branches_nil : betaeq_branches [] []
| betaeq_branches_cons b b' brs brs' :
    b.1 = b'.1 ->
    b.2 β= b'.2 ->
    betaeq_branches brs brs' ->
    betaeq_branches (b :: brs) (b' :: brs')

with betaeq_defs : mfixpoint term -> mfixpoint term -> Prop :=
| betaeq_defs_nil : betaeq_defs [] []
| betaeq_defs_cons d d' defs defs' :
    dname d = dname d' ->
    dbody d β= dbody d' ->
    rarg d = rarg d' ->
    betaeq_defs defs defs' ->
    betaeq_defs
      (d :: defs)
      (d' :: defs')

where "t β= t'" := (betaeq t t').

Derive Signature for betaeq.

Hint Constructors betaeq betaeq_terms betaeq_branches betaeq_defs : beta.

Lemma betaeq_terms_Forall2 ts ts' :
  betaeq_terms ts ts' <-> Forall2 betaeq ts ts'.
Proof. split; induction 1; eauto with beta. Qed.

Lemma betaeq_branches_Forall2 brs brs' :
  betaeq_branches brs brs' <->
  Forall2 (fun b b' => b.1 = b'.1 /\ b.2 β= b'.2) brs brs'.
Proof.
  split; induction 1; eauto with beta.
  destruct H.
  eauto with beta.
Qed.

Lemma betaeq_defs_Forall2 defs defs' :
  betaeq_defs defs defs' <->
  Forall2 (fun d d' => dname d = dname d' /\
                       dbody d β= dbody d' /\
                       rarg d = rarg d') defs defs'.
Proof.
  split; induction 1; eauto with beta.
  destruct H as (? & ? & ?); eauto with beta.
Qed.

Ltac beta_to_all :=
  rewrite -> ?betaeq_terms_Forall2 in *;
  rewrite -> ?betaeq_branches_Forall2 in *;
  rewrite -> ?betaeq_defs_Forall2 in *.

Ltac all_to_beta :=
  rewrite <- ?betaeq_terms_Forall2 in *;
  rewrite <- ?betaeq_branches_Forall2 in *;
  rewrite <- ?betaeq_defs_Forall2 in *.

Scheme betaeq_mind := Induction for betaeq Sort Prop
  with betaeq_terms_mind := Induction for betaeq_terms Sort Prop
  with betaeq_branches_mind := Induction for betaeq_branches Sort Prop
  with betaeq_defs_mind := Induction for betaeq_defs Sort Prop.

(*
Definition betaeq_forall_list_ind
           (P : term -> term -> Prop)
           (Hbetal : forall (na : name) (body arg sub : term),
               body{0 := arg} β= sub ->
               P (body {0 := arg}) sub ->
               P (tApp (tLambda na body) arg) sub)
           (Hbetar : forall (na : name) (body arg sub : term),
               sub β= body {0 := arg} ->
               P sub (body {0 := arg}) ->
               P sub (tApp (tLambda na body) arg))
           (Hbox : P tBox tBox)
           (Hrel : forall i : nat, P (tRel i) (tRel i))
           (Hvar : forall id : ident, P (tVar id) (tVar id))
           (Hevar : forall (i : nat) (ts ts' : list term),
               Forall2 (fun t t' => t β= t' /\ P t t') ts ts' ->
               P (tEvar i ts) (tEvar i ts'))
           (Hlambda : forall (na : name) (body body' : term),
               body β= body' ->
               P body body' ->
               P (tLambda na body) (tLambda na body'))
           (Hletin : forall (na : name) (val val' body body' : term),
               val β= val' ->
               P val val' ->
               body β= body' ->
               P body body' ->
               P (tLetIn na val body) (tLetIn na val' body'))
           (Happ : forall hd hd' arg arg' : term,
               hd β= hd' ->
               P hd hd' ->
               arg β= arg' ->
               P arg arg' ->
               P (tApp hd arg) (tApp hd' arg'))
           (Hconst : forall kn : kername, P (tConst kn) (tConst kn))
           (Hconstruct : forall (ind : inductive) (c : nat),
               P (tConstruct ind c) (tConstruct ind c))
           (Hcase : forall (p : inductive × nat) (disc disc' : term)
                           (brs brs' : list (nat × term)),
               disc β= disc' ->
               P disc disc' ->
               Forall2 (fun '(ar, t) '(ar', t') => ar = ar' /\ t β= t' /\ P t t') brs brs' ->
               P (tCase p disc brs) (tCase p disc' brs'))
           (Hproj : forall (p : projection) (t t' : term),
               t β= t' ->
               P t t' ->
               P (tProj p t) (tProj p t'))
           (Hfix : forall (defs defs' : list (def term)) (i : nat),
               Forall2
                 (fun d d' =>
                    dname d = dname d' /\
                    rarg d = rarg d' /\
                    dbody d β= dbody d' /\
                    P (dbody d) (dbody d')) defs defs' ->
               P (tFix defs i) (tFix defs' i))
           (Hcofix : forall (defs defs' : list (def term)) (i : nat),
               Forall2
                 (fun d d' =>
                    dname d = dname d' /\
                    rarg d = rarg d' /\
                    dbody d β= dbody d' /\
                    P (dbody d) (dbody d')) defs defs' ->
               P (tCoFix defs i) (tCoFix defs' i)) :
  forall t t', t β= t' -> P t t'.
Proof.
  fix ind 3.
  intros t t' beq.
  destruct beq;
    try solve [match goal with [ H : _ |- _ ] =>
                               match type of H with
                                 forall t t', t β= t' -> _ => fail 1
                               | _ => eapply H
                               end end; eauto].
  - apply Hevar.
    clear -H ind.
    revert ts ts' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    split; [assumption|].
    apply ind; auto.
  - apply Hcase; [assumption|apply ind; auto|].
    clear -H ind.
    revert brs brs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    destruct b, b'.
    split; [assumption|].
    split; [assumption|].
    apply ind; auto.
  - apply Hfix.
    clear -H ind.
    revert defs defs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    split; [assumption|].
    split; [assumption|].
    split; [assumption|].
    apply ind; auto.
  - apply Hcofix.
    clear -H ind.
    revert defs defs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    cbn.
    split; [assumption|].
    split; [assumption|].
    split; [assumption|].
    apply ind; auto.
Defined.
*)

Instance Equivalence_betaeq : Equivalence betaeq.
Proof. constructor; eauto with beta. Qed.
