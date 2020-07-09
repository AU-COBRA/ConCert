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

Inductive betanorm : term -> term -> Prop :=
| betanorm_box : betanorm tBox tBox
| betanorm_rel i : betanorm (tRel i) (tRel i)
| betanorm_var id : betanorm (tVar id) (tVar id)
| betanorm_evar i ts ts' :
    Forall2 betanorm ts ts' ->
    betanorm (tEvar i ts) (tEvar i ts')
| betanorm_lambda na body body' :
    betanorm body body' ->
    betanorm (tLambda na body) (tLambda na body')
| betanorm_let_in na val val' body body' :
    betanorm val val' ->
    betanorm body body' ->
    betanorm (tLetIn na val body) (tLetIn na val' body')
| betanorm_app hd hd' arg arg' :
    betanorm hd hd' ->
    isLambda hd' = false ->
    betanorm arg arg' ->
    betanorm (tApp hd arg) (tApp hd' arg')
| betanorm_const kn : betanorm (tConst kn) (tConst kn)
| betanorm_construct ind c : betanorm (tConstruct ind c) (tConstruct ind c)
| betanorm_case ind discr discr' brs brs' :
    betanorm discr discr' ->
    Forall2 (fun br br' => br.1 = br'.1 /\ betanorm br.2 br'.2) brs brs' ->
    betanorm (tCase ind discr brs) (tCase ind discr' brs')
| betanorm_proj proj t t' :
    betanorm t t' ->
    betanorm (tProj proj t) (tProj proj t')
| betanorm_fix defs defs' i :
    Forall2 (fun d d' => dname d = dname d' /\
                         betanorm (dbody d) (dbody d') /\
                         rarg d = rarg d') defs defs' ->
    betanorm (tFix defs i) (tFix defs' i)
| betanorm_cofix defs defs' i :
    Forall2 (fun d d' => dname d = dname d' /\
                         betanorm (dbody d) (dbody d') /\
                         rarg d = rarg d') defs defs' ->
    betanorm (tCoFix defs i) (tCoFix defs' i)
| betanorm_beta na body arg res :
    betanorm (body{0 := arg}) res ->
    betanorm (tApp (tLambda na body) arg) res.

Derive Signature for betanorm.

Lemma no_sn :
  exists t,
    forall v,
      betanorm t v -> False.
Proof.
  set (Ω := tLambda nAnon (tApp (tRel 0) (tRel 0))).
  exists (tApp Ω Ω).
  subst Ω.
  intros v norm.
  depind norm.
  - now depelim norm1.
  - cbn in *.
    easy.
Qed.

Open Scope string.
Definition example_tree :=
  tApp (tLambda nAnon (tApp (tLambda nAnon (tRel 1))
                            (tVar "inner")))
       (tVar "outer").

Example reduce_twice : betanorm example_tree (tVar "outer").
Proof. repeat constructor. Qed.

Example reduce_in_lam :
  betanorm
    (tLambda nAnon example_tree)
    (tLambda nAnon (tVar "outer")).
Proof. repeat constructor. Qed.

Definition betanorm_forall_list_ind
           (P : term -> term -> Prop)
           (Hbox : P tBox tBox)
           (Hrel : forall i : nat, P (tRel i) (tRel i))
           (Hvar : forall id : ident, P (tVar id) (tVar id))
           (Hevar : forall (i : nat) (ts ts' : list term),
               Forall2 betanorm ts ts' ->
               Forall2 P ts ts' ->
               P (tEvar i ts) (tEvar i ts'))
           (Hlam : forall (na : name) (body body' : term),
               betanorm body body' ->
               P body body' ->
               P (tLambda na body) (tLambda na body'))
           (Hletin : forall (na : name) (val val' body body' : term),
               betanorm val val' ->
               P val val' ->
               betanorm body body' ->
               P body body' ->
               P (tLetIn na val body) (tLetIn na val' body'))
           (Happ : forall hd hd' arg arg' : term,
               betanorm hd hd' ->
               P hd hd' ->
               isLambda hd' = false ->
               betanorm arg arg' ->
               P arg arg' ->
               P (tApp hd arg) (tApp hd' arg'))
           (Hconst : forall kn : kername, P (tConst kn) (tConst kn))
           (Hconstruct : forall (ind : inductive) (c : nat),
               P (tConstruct ind c) (tConstruct ind c))
           (Hcase : forall (ind : inductive × nat)
                           (discr discr' : term)
                           (brs brs' : list (nat × term)),
               betanorm discr discr' ->
               P discr discr' ->
               Forall2 (fun br br' => br.1 = br'.1 /\ betanorm br.2 br'.2) brs brs' ->
               Forall2 (fun br br' => P br.2 br'.2) brs brs' ->
               P (tCase ind discr brs) (tCase ind discr' brs'))
           (Hproj : forall (proj : projection) (t t' : term),
               betanorm t t' ->
               P t t' ->
               P (tProj proj t) (tProj proj t'))
           (Hfix : forall (defs defs' : list (def term)) (i : nat),
               Forall2
                 (fun d d' => dname d = dname d' /\
                              betanorm (dbody d) (dbody d') /\
                              rarg d = rarg d')
                 defs defs' ->
               Forall2 (fun d d' => P (dbody d) (dbody d')) defs defs' ->
               P (tFix defs i) (tFix defs' i))
           (Hcofix : forall (defs defs' : list (def term)) (i : nat),
               Forall2
                 (fun d d' => dname d = dname d' /\
                              betanorm (dbody d) (dbody d') /\
                              rarg d = rarg d')
                 defs defs' ->
               Forall2 (fun d d' => P (dbody d) (dbody d')) defs defs' ->
               P (tCoFix defs i) (tCoFix defs' i))
           (Hbeta : forall (na : name) (body arg res : term),
               betanorm (body {0 := arg}) res ->
               P (body {0 := arg}) res ->
               P (tApp (tLambda na body) arg) res) :
  forall t t', betanorm t t' -> P t t'.
Proof.
  fix ind 3.
  intros t t' beq.
  destruct beq;
    try solve [
          match goal with [ H : _ |- _ ] =>
                               match type of H with
                                 forall t t', betanorm t t' -> _ => fail 1
                               | _ => eapply H
                               end end; eauto].
  - apply Hevar; [assumption|].
    clear -H ind.
    revert ts ts' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    now apply ind.
  - apply Hcase; [assumption|now apply ind|assumption|].
    clear -H ind.
    revert brs brs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    destruct H.
    now apply ind.
  - apply Hfix; [assumption|].
    clear -H ind.
    revert defs defs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    destruct H as (? & ? & ?).
    now apply ind.
  - apply Hcofix; [assumption|].
    clear -H ind.
    revert defs defs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    destruct H as (? & ? & ?).
    now apply ind.
Defined.

Lemma betanorm_deterministic t v v' :
  betanorm t v ->
  betanorm t v' ->
  v = v'.
Proof.
  intros n1 n2.
  induction n1 using betanorm_forall_list_ind in t, v, v', n1, n2 |- *;
    try solve [depelim n2; auto; f_equal; auto].
  - depelim n2.
    f_equal.
    induction H in ts, ts', ts'0, H, H0, H1 |- *.
    + now depelim H1.
    + depelim H0.
      depelim H3.
      now f_equal.
  - depelim n2.
    + now erewrite IHn1_1, IHn1_2 by easy.
    + now depelim n1_1.
  - depelim n2.
    f_equal; auto.
    clear ind discr'0 discr discr' n1 n2 IHn1.
    induction H in brs, brs', brs'0, H, H0, H1 |- *.
    + now depelim H1.
    + depelim H0.
      depelim H3.
      destruct y0, x, y.
      cbn in *.
      destruct H, H3.
      erewrite H0 by easy.
      now f_equal.
  - depelim n2.
    f_equal.
    induction H in defs, defs', defs'0, H, H0, H1 |- *.
    + now depelim H1.
    + depelim H0.
      depelim H3.
      destruct y0, x, y, H as (? & ? & ?), H3 as (? & ? & ?).
      cbn in *.
      erewrite H0 by easy.
      f_equal; [f_equal|]; try congruence.
      easy.
  - depelim n2.
    f_equal.
    induction H in defs, defs', defs'0, H, H0, H1 |- *.
    + now depelim H1.
    + depelim H0.
      depelim H3.
      destruct y0, x, y, H as (? & ? & ?), H3 as (? & ? & ?).
      cbn in *.
      erewrite H0 by easy.
      f_equal; [f_equal|]; try congruence.
      easy.
  - depelim n2.
    + now depelim n2_1.
    + now apply IHn1.
Qed.

Definition betaeq (t1 t2 : term) : Prop :=
  forall v, betanorm t1 v <-> betanorm t2 v.

Infix "β=" := betaeq (at level 70, right associativity).

Instance Equivalence_betaeq : Equivalence betaeq.
Proof. constructor; repeat intro; firstorder. Qed.

Fixpoint has_beta_redex (t : term) : bool :=
  match t with
  | tBox => false
  | tRel _ => false
  | tVar _ => false
  | tEvar _ ts => fold_right orb false (map has_beta_redex ts)
  | tLambda na body => has_beta_redex body
  | tLetIn na val body => has_beta_redex val || has_beta_redex body
  | tApp hd arg => isLambda hd || has_beta_redex hd || has_beta_redex arg
  | tConst _ => false
  | tConstruct _ _ => false
  | tCase _ discr brs =>
    has_beta_redex discr || fold_right orb false (map (has_beta_redex ∘ snd) brs)
  | tProj _ t => has_beta_redex t
  | tFix defs _ => fold_right orb false (map (has_beta_redex ∘ dbody) defs)
  | tCoFix defs _ => fold_right orb false (map (has_beta_redex ∘ dbody) defs)
  end.

Lemma betanorm_normalizes t v :
  betanorm t v ->
  has_beta_redex v = false.
Proof.
  intros bn.
  induction bn using betanorm_forall_list_ind;
    cbn in *; propify; auto.
  - induction H; depelim H0; [easy|].
    cbn in *.
    now propify.
  - split; [easy|].
    induction H; depelim H0; [easy|].
    cbn in *.
    now propify.
  - induction H; depelim H0; [easy|].
    cbn in *.
    now propify.
  - induction H; depelim H0; [easy|].
    cbn in *.
    now propify.
Qed.
