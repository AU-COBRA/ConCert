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
From Coq Require Import Relation_Operators.
From Coq Require Import Operators_Properties.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Import EAstUtils.

Inductive betaeq1 : term -> term -> Prop :=
| betaeq_evar i ts ts' :
    OnOne2 betaeq1 ts ts' ->
    betaeq1 (tEvar i ts) (tEvar i ts')
| betaeq_lambda na body body' :
    betaeq1 body body' ->
    betaeq1 (tLambda na body) (tLambda na body')
| betaeq_let_in_l na val val' body :
    betaeq1 val val' ->
    betaeq1 (tLetIn na val body) (tLetIn na val' body)
| betaeq_let_in_r na val body body' :
    betaeq1 body body' ->
    betaeq1 (tLetIn na val body) (tLetIn na val body')
| betaeq_app_l hd hd' arg :
    betaeq1 hd hd' ->
    betaeq1 (tApp hd arg) (tApp hd' arg)
| betaeq_app_r hd arg arg' :
    betaeq1 arg arg' ->
    betaeq1 (tApp hd arg) (tApp hd arg')
| betaeq_case_discr ind discr discr' brs :
    betaeq1 discr discr' ->
    betaeq1 (tCase ind discr brs) (tCase ind discr' brs)
| betaeq_case_brs ind discr brs brs' :
    OnOne2 (fun br br' => br.1 = br'.1 /\ betaeq1 br.2 br'.2) brs brs' ->
    betaeq1 (tCase ind discr brs) (tCase ind discr brs')
| betaeq_proj proj t t' :
    betaeq1 t t' ->
    betaeq1 (tProj proj t) (tProj proj t')
| betaeq_fix defs defs' i :
    OnOne2 (fun d d' => dname d = dname d' /\
                        betaeq1 (dbody d) (dbody d') /\
                        rarg d = rarg d') defs defs' ->
    betaeq1 (tFix defs i) (tFix defs' i)
| betaeq_cofix defs defs' i :
    OnOne2 (fun d d' => dname d = dname d' /\
                        betaeq1 (dbody d) (dbody d') /\
                        rarg d = rarg d') defs defs' ->
    betaeq1 (tCoFix defs i) (tCoFix defs' i)
| betaeq_beta_l na body arg :
    betaeq1 (tApp (tLambda na body) arg) (body{0 := arg})
| betaeq_beta_r na body arg :
    betaeq1 (body{0 := arg}) (tApp (tLambda na body) arg).

Derive Signature for betaeq1.
Derive Signature for OnOne2.

Derive Subterm for term.
Derive NoConfusionHom for term.

Definition betaeq1_forall_list_ind
           (P : term -> term -> Prop)
           (Hevar : forall (i : nat) (ts ts' : list term),
               OnOne2 (fun t t' => betaeq1 t t' /\ P t t') ts ts' ->
               P (tEvar i ts) (tEvar i ts'))
           (Hlam : forall (na : name) (body body' : term),
               betaeq1 body body' ->
               P body body' ->
               P (tLambda na body) (tLambda na body'))
           (Hletinval : forall (na : name) (val val' body : term),
               betaeq1 val val' ->
               P val val' ->
               P (tLetIn na val body) (tLetIn na val' body))
           (Hletinbody : forall (na : name) (val body body' : term),
               betaeq1 body body' ->
               P body body' ->
               P (tLetIn na val body) (tLetIn na val body'))
           (Happhd : forall hd hd' arg : term,
               betaeq1 hd hd' ->
               P hd hd' ->
               P (tApp hd arg) (tApp hd' arg))
           (Happarg : forall hd arg arg' : term,
               betaeq1 arg arg' ->
               P arg arg' ->
               P (tApp hd arg) (tApp hd arg'))
           (Hcasediscr : forall (ind : inductive × nat)
                                (discr discr' : term)
                                (brs : list (nat × term)),
               betaeq1 discr discr' ->
               P discr discr' ->
               P (tCase ind discr brs) (tCase ind discr' brs))
           (Hcasebr : forall (ind : inductive × nat) (discr : term) (brs brs' : list (nat × term)),
               OnOne2 (fun br br' =>
                         br.1 = br'.1 /\ betaeq1 br.2 br'.2 /\ P br.2 br'.2) brs brs' ->
               P (tCase ind discr brs) (tCase ind discr brs'))
           (Hproj : forall (proj : projection) (t t' : term),
               betaeq1 t t' ->
               P t t' ->
               P (tProj proj t) (tProj proj t'))
           (Hfix : forall (defs defs' : list (def term)) (i : nat),
               OnOne2
                 (fun d d' =>
                    dname d = dname d' /\
                    betaeq1 (dbody d) (dbody d') /\
                    P (dbody d) (dbody d') /\
                    rarg d = rarg d') defs defs' ->
               P (tFix defs i) (tFix defs' i))
           (Hcofix : forall (defs defs' : list (def term)) (i : nat),
               OnOne2
                 (fun d d' =>
                    dname d = dname d' /\
                    betaeq1 (dbody d) (dbody d') /\
                    P (dbody d) (dbody d') /\
                    rarg d = rarg d') defs defs' ->
               P (tCoFix defs i) (tCoFix defs' i))
           (Hbetal : forall (na : name) (body arg : term),
               P (tApp (tLambda na body) arg) (body {0 := arg}))
           (Hbetar : forall (na : name) (body arg : term),
               P (body {0 := arg}) (tApp (tLambda na body) arg)) :
  forall t t', betaeq1 t t' -> P t t'.
Proof.
  fix ind 3.
  intros t t' beq.
  destruct beq;
    try solve [
          match goal with [ H : _ |- _ ] =>
                               match type of H with
                                 forall t t', betaeq1 t t' -> _ => fail 1
                               | _ => eapply H
                               end end; eauto].
  - apply Hevar.
    clear -H ind.
    revert ts ts' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    split; [assumption|].
    now apply ind.
  - apply Hcasebr.
    clear -H ind.
    revert brs brs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    destruct a.
    split; [assumption|].
    split; [assumption|].
    now apply ind.
  - apply Hfix.
    clear -H ind.
    revert defs defs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    destruct a as (? & ? & ?).
    split; [assumption|].
    split; [assumption|].
    split; [|assumption].
    now apply ind.
  - apply Hcofix.
    clear -H ind.
    revert defs defs' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    destruct a as (? & ? & ?).
    split; [assumption|].
    split; [assumption|].
    split; [|assumption].
    now apply ind.
Defined.

(*
Lemma not_eq_lift_sub t app n k :
  term_direct_subterm t app ->
  app = lift n k t ->
  False.
Proof.
  intros sub eq.
  induction t in t, app, n, k, sub, eq |- * using term_forall_list_ind; subst; cbn in *.
  - depelim sub.
  - destruct (_ <=? _); depelim sub.
  - depelim sub.
  - depelim sub.
  - depelim sub.
    eapply (IHt (tLambda n0 t)); [constructor|].
    easy.
  - depelim sub.
    + eapply (IHt2 (tLetIn n0 t1 t2)); [constructor|].
      easy.
    + eapply (IHt1 (tLetIn n0 t1 t2)); [constructor|].
      easy.
  - depelim sub.
    + eapply (IHt2 (tApp t1 t2)); [constructor|].
      easy.
    + inversion H.
      subst.
      eapply (IHt1 (tApp t1 t2)); [constructor|].
      easy.
  - depelim sub.
  - depelim sub.
  - depelim sub.
    eapply (IHt (tCase p t l)); [constructor|].
    easy.
  - depelim sub.
    eapply (IHt (tProj s t)); [constructor|].
    easy.
  - depelim sub.
  - depelim sub.
Qed.

(*
Lemma not_eq_subst_sub body lam app arg k :
  term_direct_subterm body lam ->
  term_direct_subterm arg app ->
  term_direct_subterm lam app ->
  app = body{k := arg} ->
  False.
Proof.
  intros sub1 sub2 sub3 eq.
  induction body in body, lam, app, arg, k, sub1, sub2, sub3, eq |- * using term_forall_list_ind;
    subst; cbn in *; try easy.
  - destruct (_ <=? _); [|easy].
    destruct (nth_error _ _) eqn:nth; [|subst; now depelim sub1].
    apply nth_error_In in nth.
    destruct nth; [|easy]; subst arg.
    eapply not_eq_lift_sub; [|easy].
    easy.
  - depelim sub2; depelim sub3.

  - easy.
  - easy.
  induction s in h, a, s, sub, eq |- * using term_forall_list_ind; try easy.
  - cbn in *.
    destruct (nth_error _ _) eqn:nth; [|easy].
    apply nth_error_In in nth.
    destruct nth; try easy.
    subst.
    now eapply not_eq_lift_sub.
  - cbn in *.
    inversion eq.
    subst.
    specialize (IHs1 s1).
*)

*)

(*
Lemma not_eq_subst_sub na body t k :
  tApp (tLambda na body) t = body{k := t} ->
  False.
Proof.
  intros eq.
  induction body in k, eq |- * using term_forall_list_ind; try easy.
  - cbn in *.
    destruct (_ <=? _); [|easy].
    destruct (nth_error _ _) eqn:nth; [|easy].
    apply nth_error_In in nth.
    destruct nth; try easy.
    subst.
    now eapply not_eq_lift_sub.
  - cbn in *.
    inversion eq.
    destruct (subst [t] k body1) eqn:s; try easy.
    inversion eq.
    destruct t0; try easy.
    cbn in *.
    destruct t0_1; try easy.
    cbn in *.
    destruct t0_1; try easy.
    cbn in *.
*)

Lemma betaeq1_irreflexive t :
  betaeq1 t t -> False.
Proof.
  intros beq.
  induction t using term_forall_list_ind.
  - depelim beq.
  - depelim beq.
  - depelim beq.
  - depelim beq.
    now induction H; depelim H0.
  - now depelim beq.
  - now depelim beq.
  - depelim beq.
    + easy.
    + easy.
    + admit.
    + admit.
  - depelim beq.
  - depelim beq.
  - depelim beq; [easy|].
    now induction X; depelim H.
  - now depelim beq.
  - depelim beq.
    now induction H; depelim H0.
  - depelim beq.
    now induction H; depelim H0.
Admitted.

Lemma betaeq1_symmetric t t' :
  betaeq1 t t' ->
  betaeq1 t' t.
Proof.
  intros beq.
  induction beq using betaeq1_forall_list_ind; try now constructor.
  - constructor.
    eapply OnOne2_sym, OnOne2_impl; [eassumption|].
    cbn.
    easy.
  - constructor.
    eapply OnOne2_sym, OnOne2_impl; [eassumption|].
    cbn.
    easy.
  - constructor.
    eapply OnOne2_sym, OnOne2_impl; [eassumption|].
    cbn.
    easy.
  - constructor.
    eapply OnOne2_sym, OnOne2_impl; [eassumption|].
    cbn.
    easy.
Qed.

Inductive betaeq : term -> term -> Prop :=
| betaeq_refl t : betaeq t t
| betaeq_trans x y z :
    betaeq x y ->
    betaeq1 y z ->
    betaeq x z.

Infix "β=" := betaeq (at level 70, right associativity).

Lemma betaeq_alt t t' :
  t β= t' <-> clos_refl_trans _ betaeq1 t t'.
Proof.
  split.
  - intros beq.
    apply clos_rt_rtn1_iff.
    now induction beq; econstructor.
  - intros beq.
    apply clos_rt_rtn1_iff in beq.
    now induction beq; econstructor.
Qed.

Instance Equivalence_betaeq : Equivalence betaeq.
Proof.
  constructor.
  - intros t; apply betaeq_refl.
  - intros t t' beq.
    induction beq; [apply betaeq_refl|].
    apply betaeq1_symmetric in H.
    rewrite !betaeq_alt in *.
    apply rt_trans with y; [|easy].
    now apply rt_step.
  - intros x y z xy yz.
    rewrite !betaeq_alt in *.
    now eapply rt_trans.
Qed.

(*
Inductive betaeq : term -> term -> Prop :=
| betaeq_box : betaeq tBox tBox
| betaeq_rel i : betaeq (tRel i) (tRel i)
| betaeq_var id : betaeq (tVar id) (tVar id)
| betaeq_evar i ts ts' :
    Forall2 betaeq ts ts' ->
    betaeq (tEvar i ts) (tEvar i ts')
| betaeq_lambda na body body' :
    betaeq body body' ->
    betaeq (tLambda na body) (tLambda na body')
| betaeq_let_in na val val' body body' :
    betaeq val val' ->
    betaeq body body' ->
    betaeq (tLetIn na val body) (tLetIn na val' body')
| betaeq_app hd hd' arg arg' :
    betaeq hd hd' ->
    betaeq arg arg' ->
    betaeq (tApp hd arg) (tApp hd' arg')
| betaeq_const kn : betaeq (tConst kn) (tConst kn)
| betaeq_construct ind c : betaeq (tConstruct ind c) (tConstruct ind c)
| betaeq_case ind discr discr' brs brs' :
    betaeq discr discr' ->
    Forall2 (fun br br' => br.1 = br'.1 /\ betaeq br.2 br'.2) brs brs' ->
    betaeq (tCase ind discr brs) (tCase ind discr' brs')
| betaeq_proj proj t t' :
    betaeq t t' ->
    betaeq (tProj proj t) (tProj proj t')
| betaeq_fix defs defs' i :
    Forall2 (fun d d' => dname d = dname d' /\
                         betaeq (dbody d) (dbody d') /\
                         rarg d = rarg d') defs defs' ->
    betaeq (tFix defs i) (tFix defs' i)
| betaeq_cofix defs defs' i :
    Forall2 (fun d d' => dname d = dname d' /\
                         betaeq (dbody d) (dbody d') /\
                         rarg d = rarg d') defs defs' ->
    betaeq (tCoFix defs i) (tCoFix defs' i)
| betaeq_beta_left hd na body arg arg' r :
    betaeq hd (tLambda na body) ->
    betaeq arg arg' ->
    betaeq (body{0 := arg'}) r ->
    betaeq (tApp hd arg) r
| betaeq_beta_right hd na body arg arg' l :
    betaeq hd (tLambda na body) ->
    betaeq arg arg' ->
    betaeq l (body{0 := arg'}) ->
    betaeq l (tApp hd arg).

Derive Signature for betaeq.

Definition betaeq_forall_list_ind
           (P : term -> term -> Prop)
           (Hbox : P tBox tBox)
           (Hrel : forall i : nat, P (tRel i) (tRel i))
           (Hvar : forall id : ident, P (tVar id) (tVar id))
           (Hevar : forall (i : nat) (ts ts' : list term),
               Forall2 betaeq ts ts' ->
               Forall2 P ts ts' ->
               P (tEvar i ts) (tEvar i ts'))
           (Hlam : forall (na : name) (body body' : term),
               betaeq body body' ->
               P body body' ->
               P (tLambda na body) (tLambda na body'))
           (Hletin : forall (na : name) (val val' body body' : term),
               betaeq val val' ->
               P val val' ->
               betaeq body body' ->
               P body body' ->
               P (tLetIn na val body) (tLetIn na val' body'))
           (Happ : forall hd hd' arg arg' : term,
               betaeq hd hd' ->
               P hd hd' ->
               betaeq arg arg' ->
               P arg arg' ->
               P (tApp hd arg) (tApp hd' arg'))
           (Hconst : forall kn : kername, P (tConst kn) (tConst kn))
           (Hconstruct : forall (ind : inductive) (c : nat),
               P (tConstruct ind c) (tConstruct ind c))
           (Hcase : forall (ind : inductive × nat)
                           (discr discr' : term)
                           (brs brs' : list (nat × term)),
               betaeq discr discr' ->
               P discr discr' ->
               Forall2 (fun br br' => br.1 = br'.1 /\ betaeq br.2 br'.2) brs brs' ->
               Forall2 (fun br br' => P br.2 br'.2) brs brs' ->
               P (tCase ind discr brs) (tCase ind discr' brs'))
           (Hproj : forall (proj : projection) (t t' : term),
               betaeq t t' ->
               P t t' ->
               P (tProj proj t) (tProj proj t'))
           (Hfix : forall (defs defs' : list (def term)) (i : nat),
               Forall2
                 (fun d d' => dname d = dname d' /\
                              betaeq (dbody d) (dbody d') /\
                              rarg d = rarg d')
                 defs defs' ->
               Forall2 (fun d d' => P (dbody d) (dbody d')) defs defs' ->
               P (tFix defs i) (tFix defs' i))
           (Hcofix : forall (defs defs' : list (def term)) (i : nat),
               Forall2
                 (fun d d' => dname d = dname d' /\
                              betaeq (dbody d) (dbody d') /\
                              rarg d = rarg d')
                 defs defs' ->
               Forall2 (fun d d' => P (dbody d) (dbody d')) defs defs' ->
               P (tCoFix defs i) (tCoFix defs' i))
           (Hbetal : forall (hd : term) (na : name) (body arg arg' r : term),
               betaeq hd (tLambda na body) ->
               P hd (tLambda na body) ->
               betaeq arg arg' ->
               P arg arg' ->
               betaeq (body{0 := arg'}) r ->
               P (body{0 := arg'}) r ->
               P (tApp hd arg) r)
           (Hbetar : forall (hd : term) (na : name) (body arg arg' l : term),
               betaeq hd (tLambda na body) ->
               P hd (tLambda na body) ->
               betaeq arg arg' ->
               P arg arg' ->
               betaeq l (body{0 := arg'}) ->
               P l (body{0 := arg'}) ->
               P l (tApp hd arg)) :
  forall t t', betaeq t t' -> P t t'.
Proof.
  fix ind 3.
  intros t t' beq.
  destruct beq;
    try solve [
          match goal with [ H : _ |- _ ] =>
                               match type of H with
                                 forall t t', betaeq t t' -> _ => fail 1
                               | _ => eapply H
                               end end; eauto].
  - apply Hevar; [assumption|].
    clear -H ind.
    revert ts ts' H.
    fix f 3.
    destruct 1; constructor; [|auto].
    now apply ind.
  - now apply Happ.
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

Infix "β=" := betaeq (at level 70, right associativity).

Lemma betaeq_refl t : t β= t.
Proof.
  induction t using term_forall_list_ind; eauto using betaeq.
  - constructor.
    now apply Forall_Forall2 in H.
  - constructor; [easy|].
    now induction X.
  - constructor.
    induction H; [easy|].
    now constructor.
  - constructor.
    induction H; [easy|].
    now constructor.
Qed.

Lemma betaeq_sym t t' :
  t β= t' ->
  t' β= t.
Proof.
  intros beq.
  induction beq using betaeq_forall_list_ind; eauto using betaeq.
  - constructor.
    now induction H0; depelim H.
  - constructor; [easy|].
    now induction H0; depelim H.
  - constructor.
    induction H0; depelim H; [easy|].
    now constructor.
  - constructor.
    induction H0; depelim H; [easy|].
    now constructor.
Qed.

(*
Lemma betaeq_lift t t' n k :
  t β= t' ->
  lift n k t β= lift n k t'.
Proof.
  intros beq.
  induction beq using betaeq_forall_list_ind in t, t', n, k, beq |- *;
    eauto using betaeq; cbn.
  - destruct ?; eauto using betaeq.
  - constructor.
    apply Forall2_map.
    now induction H0; depelim H.
  - constructor; [easy|].
    apply Forall2_map.
    induction H0; depelim H; [easy|].
    cbn.
    now constructor.
  - constructor.
    apply Forall2_map.
    induction H0 in n, k, defs, defs', H, H0 |- *; depelim H; [easy|].
    cbn in *.
    constructor; [now rewrite (Forall2_length H2)|].
    now rewrite <- !Nat.add_succ_r.
  - constructor.
    apply Forall2_map.
    induction H0 in n, k, defs, defs', H, H0 |- *; depelim H; [easy|].
    cbn in *.
    constructor; [now rewrite (Forall2_length H2)|].
    now rewrite <- !Nat.add_succ_r.
  - constructor.
    rewrite <- distr_lift_subst10.
    apply IHbeq.
  - constructor.
    rewrite <- distr_lift_subst10.
    apply IHbeq.
Qed.

Lemma distr_subst1 s k t a :
  (subst s (S k) t){0 := subst s k a} = subst s k (t{0 := a}).
Proof.
  symmetry.
  apply distr_subst.
Qed.

Lemma betaeq_subst s s' k t t' :
  Forall2 betaeq s s' ->
  t β= t' ->
  subst s k t β= subst s' k t'.
Proof.
  intros all beq.
  induction beq using betaeq_forall_list_ind in k, t, t', beq |- *;
    eauto using betaeq.
  - cbn.
    destruct (_ <=? _); eauto using betaeq.
    destruct (nth_error _ _) eqn:nth.
    + eapply Forall2_nth_error_Some in all as (t' & -> & ?); [|eassumption].
      now apply betaeq_lift.
    + rewrite (Forall2_length all).
      eapply Forall2_nth_error_None_l in all as ->; [|eassumption].
      constructor.
  - cbn.
    constructor.
    apply Forall2_map.
    now induction H; depelim H0.
  - cbn.
    constructor; [easy|].
    apply Forall2_map.
    induction H0; depelim H; [easy|].
    constructor; [|easy].
    cbn in *.
    intuition.
  - cbn.
    constructor.
    apply Forall2_map.
    induction H0 in k, defs, defs', H, H0 |- *; depelim H; [easy|].
    cbn in *.
    constructor; [now rewrite (Forall2_length H2)|].
    now rewrite <- !Nat.add_succ_r.
  - cbn.
    constructor.
    apply Forall2_map.
    induction H0 in k, defs, defs', H, H0 |- *; depelim H; [easy|].
    cbn in *.
    constructor; [now rewrite (Forall2_length H2)|].
    now rewrite <- !Nat.add_succ_r.
  - cbn.
    constructor.
    now rewrite distr_subst1.
  - cbn.
    constructor.
    now rewrite distr_subst1.
Qed.

(*
Lemma betaeq_substl s s' k t t' :
  Forall2 betaeq s s' ->
  subst s k t β= t' ->
  subst s k t β= subst s' k t'.
Proof.
  intros all beq.
  induction beq using betaeq_forall_list_ind in k, t, t', beq |- *;
    eauto using betaeq.
  - cbn.
    destruct (_ <=? _); eauto using betaeq.
    destruct (nth_error _ _) eqn:nth.
    + eapply Forall2_nth_error_Some in all as (t' & -> & ?); [|eassumption].
      now apply betaeq_lift.
    + rewrite (Forall2_length all).
      eapply Forall2_nth_error_None_l in all as ->; [|eassumption].
      constructor.
  - cbn.
    constructor.
    apply Forall2_map.
    now induction H; depelim H0.
  - cbn.
    constructor; [easy|].
    apply Forall2_map.
    induction H0; depelim H; [easy|].
    constructor; [|easy].
    cbn in *.
    intuition.
  - cbn.
    constructor.
    apply Forall2_map.
    induction H0 in k, defs, defs', H, H0 |- *; depelim H; [easy|].
    cbn in *.
    constructor; [now rewrite (Forall2_length H2)|].
    now rewrite <- !Nat.add_succ_r.
  - cbn.
    constructor.
    apply Forall2_map.
    induction H0 in k, defs, defs', H, H0 |- *; depelim H; [easy|].
    cbn in *.
    constructor; [now rewrite (Forall2_length H2)|].
    now rewrite <- !Nat.add_succ_r.
  - cbn.
    constructor.
    now rewrite distr_subst1.
  - cbn.
    constructor.
    now rewrite distr_subst1.
Qed.
*)
*)

Lemma betaeq_trans x y z :
  x β= y ->
  y β= z ->
  x β= z.
Proof.
  intros beq1 beq2.
  induction x in x, y, z, beq1, beq2 |- * using term_forall_list_ind.
  -
    depelim beq1; [easy|].
    depelim beq2; eauto using betaeq.
  revert z.
  induction beq1 using betaeq_forall_list_ind; intros z beq2; eauto using betaeq.
  - depind beq2; [|now econstructor].
    constructor.
    induction H0 in ts, ts', ts0, H, H0, H1 |- *; [easy|].
    depelim H.
    depelim H3.
    now constructor.
  - depind beq2; [|now econstructor].
    now constructor.
  - depind beq2; [|now econstructor].
    now constructor.
  - depind beq2; [now econstructor| |now econstructor].
    econstructor.
    + now eapply IHbeq1_1.
    + now eapply IHbeq1_2.
    + eassumption.
  - depind beq2; [|now econstructor].
    constructor; [easy|].
    induction H0 in brs, brs', H, H0, H1 |- *; [easy|].
    depelim H.
    depelim H3.
    now constructor.
  - depind beq2; [|now econstructor].
    now constructor.
  - depind beq2; [|now econstructor].
    constructor.
    induction H0 in defs, defs0, defs', H, H0, H1 |- *; [easy|].
    depelim H.
    depelim H3.
    constructor; [|easy].
    intuition try congruence.
    easy.
  - depind beq2; [|now econstructor].
    constructor.
    induction H0 in defs, defs0, defs', H, H0, H1 |- *; [easy|].
    depelim H.
    depelim H3.
    constructor; [|easy].
    intuition try congruence.
    easy.
  -
    depind beq2.
    + depind beq1_1.
      * econstructor.
        now apply betaeq_sym.
        now apply betaeq_sym.
        apply IHbeq1_3.
        admit.
      *
        eauto.
    + admit.
    + now econstructor.
      eapply IHbeq1_3.
      eapply IHbeq2_1.
      eapply IHbeq2_2.
      refle
      specialize (IHbeq2_2 _ _ _ _ _ _ beq1_1 beq1_2 beq1_3 ltac:(easy) ltac:(easy) ltac:(easy)).
      specialize (IHbeq1_2 beq2_1).
      eapply IHbeq2_2.
      * now eapply IHbeq1_1.
    apply H3.
    auto.
    induction
    easy.
    depind beq2_1.
    + econstructor.
      easy.
      easy.
    apply (betaeq_beta_left _ na body).
    +
    econstructor.
    depelim beq1_1.
    + clear IHbeq2.
      constructor.
      admit.
    +
    depelim beq1_1.
    + constructor.
    + eapply IHbeq2.
      constructor.

  intros beq1.
  revert z.

(*
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
*)

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

*)
