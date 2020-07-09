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
| betaeq_beta_l na body arg :
    tApp (tLambda na body) arg β= body{0 := arg}
| betaeq_beta_r na body arg :
    body{0 := arg} β= tApp (tLambda na body) arg
| betaeq_box : tBox β= tBox
| betaeq_rel i : tRel i β= tRel i
| betaeq_var id : tVar id β= tVar id
| betaeq_evar i ts ts' :
    Forall2 betaeq ts ts' ->
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
| betaeq_const kn : tConst kn β= tConst kn
| betaeq_construct ind c : tConstruct ind c β= tConstruct ind c
| betaeq_case p disc disc' brs brs' :
    disc β= disc' ->
    Forall2 (fun p p' => fst p = fst p' /\ snd p β= snd p') brs brs' ->
    tCase p disc brs β= tCase p disc' brs'
| betaeq_proj p t t' :
    t β= t' ->
    tProj p t β= tProj p t'
| betaeq_fix defs defs' i :
    Forall2 (fun d d' => dname d = dname d' /\ dbody d β= dbody d' /\ rarg d = rarg d')
            defs defs' ->
    tFix defs i β= tFix defs' i
| betaeq_cofix defs defs' i :
    Forall2 (fun d d' => dname d = dname d' /\ dbody d β= dbody d' /\ rarg d = rarg d')
            defs defs' ->
    tCoFix defs i β= tCoFix defs' i
| betaeq_trans a b c :
    a β= b ->
    b β= c ->
    a β= c
where "t β= t'" := (betaeq t t').

Lemma betaeq_refl t : t β= t.
Proof.
  induction t using term_forall_list_ind; eauto using betaeq.
  - constructor.
    now induction H.
  - constructor.
    now induction H.

Derive Signature for betaeq.

Definition betaeq_forall_list_ind
           (P : term -> term -> Prop)
           (Hbeta : forall (na : name) (body arg : term),
               P (tApp (tLambda na body) arg) (body {0 := arg}))
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
               P (tCoFix defs i) (tCoFix defs' i))
           (Hrefl : forall t, P t t)
           (Hsym : forall t t',
               t β= t' ->
               P t t' ->
               P t' t)
           (Htrans : forall t t' t'',
               t β= t' ->
               P t t' ->
               t' β= t'' ->
               P t' t'' ->
               P t t'') :
  forall t t', t β= t' -> P t t'.
Proof.
  fix ind 3.
  intros t t' beq.
  destruct beq;
    try solve [
          clear Hrefl Hsym Htrans;
          match goal with [ H : _ |- _ ] =>
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
  - apply Hrefl.
  - apply Hsym; auto.
  - eapply Htrans; eauto.
Defined.

Instance Equivalence_betaeq : Equivalence betaeq.
Proof. constructor; eauto with beta. Qed.
