From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Psatz.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Import EAstUtils.
Import Erasure.
Import ExAst.

Reserved Notation "Σ ⊢ s ▷ t" (at level 50, s, t at next level).

Definition is_ctor_or_box (t : term) : bool :=
  match t with
  | tBox => true
  | t => match decompose_app t with
         | (tConstruct _ _, _) => true
         | _ => false
         end
  end.

Inductive aeval Σ : term -> term -> Prop :=
| aeval_box a t t' :
    Σ ⊢ a ▷ tBox ->
    Σ ⊢ t ▷ t' ->
    Σ ⊢ tApp a t ▷ tBox

| aeval_beta f na b a a' res :
    Σ ⊢ f ▷ tLambda na b ->
    Σ ⊢ a ▷ a' ->
    Σ ⊢ csubst a' 0 b ▷ res ->
    Σ ⊢ tApp f a ▷ res

| aeval_zeta na b0 b0' b1 res :
    Σ ⊢ b0 ▷ b0' ->
    Σ ⊢ csubst b0' 0 b1 ▷ res ->
    Σ ⊢ tLetIn na b0 b1 ▷ res

| aeval_iota ind pars discr c args brs res :
    Σ ⊢ discr ▷ mkApps (tConstruct ind c) args ->
    Σ ⊢ ETyping.iota_red pars c args brs ▷ res ->
    Σ ⊢ tCase (ind, pars) discr brs ▷ res

| aeval_iota_sing ind pars discr brs n f res :
    Σ ⊢ discr ▷ tBox ->
    brs = [(n, f)] ->
    Σ ⊢ mkApps f (repeat tBox n) ▷ res ->
    Σ ⊢ tCase (ind, pars) discr brs ▷ res

| aeval_stuck_fix f mfix idx args narg fn a av :
    Σ ⊢ f ▷ mkApps (tFix mfix idx) args ->
    Σ ⊢ a ▷ av ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    (#|args| < narg \/
     (#|args| = narg /\ ~is_ctor_or_box av)) ->
    Σ ⊢ tApp f a ▷ mkApps (tFix mfix idx) (args ++ [av])

| aeval_fix f mfix idx args narg fn a av v :
    Σ ⊢ f ▷ mkApps (tFix mfix idx) args ->
    Σ ⊢ a ▷ av ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    #|args| = narg ->
    is_ctor_or_box av ->
    Σ ⊢ mkApps fn (args ++ [av]) ▷ v ->
    Σ ⊢ tApp f a ▷ v

| ared_cofix_case ip mfix idx args narg fn brs res :
    cunfold_cofix mfix idx = Some (narg, fn) ->
    Σ ⊢ tCase ip (mkApps fn args) brs ▷ res ->
    Σ ⊢ tCase ip (mkApps (tCoFix mfix idx) args) brs ▷ res

| ared_cofix_proj p mfix idx args narg fn res :
    cunfold_cofix mfix idx = Some (narg, fn) ->
    Σ ⊢ tProj p (mkApps fn args) ▷ res ->
    Σ ⊢ tProj p (mkApps (tCoFix mfix idx) args) ▷ res

| aeval_delta c decl body :
    ETyping.declared_constant Σ c decl ->
    forall res : term,
      EAst.cst_body decl = Some body ->
      Σ ⊢ body ▷ res ->
      Σ ⊢ tConst c ▷ res

| aeval_proj i pars arg discr args k res :
    Σ ⊢ discr ▷ mkApps (tConstruct i k) args ->
    Σ ⊢ nth (pars + arg) args ETyping.tDummy ▷ res ->
    Σ ⊢ tProj (i, pars, arg) discr ▷ res

| aeval_proj_box i pars arg discr :
    Σ ⊢ discr ▷ tBox ->
    Σ ⊢ tProj (i, pars, arg) discr ▷ tBox

| aeval_app_cong f f' a a' :
    Σ ⊢ f ▷ f' ->
    negb (isLambda f' || isFixApp f' || isBox f') ->
    Σ ⊢ a ▷ a' ->
    Σ ⊢ tApp f a ▷ tApp f' a'

| aeval_atom t : atom t -> Σ ⊢ t ▷ t

where "Σ ⊢ t ▷ v" := (aeval Σ t v) : aeval_scope.

Derive Signature for aeval.
Derive NoConfusionHom for term.

Open Scope aeval_scope.

Lemma aeval_tApp_head Σ hd arg v :
  Σ ⊢ tApp hd arg ▷ v ->
  exists hdv,
    Σ ⊢ hd ▷ hdv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma aeval_tApp_arg Σ hd arg v :
  Σ ⊢ tApp hd arg ▷ v ->
  exists argv,
    Σ ⊢ arg ▷ argv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma aeval_mkApps_head Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists hdv,
    Σ ⊢ hd ▷ hdv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  specialize (IHargs _ _ ev) as (? & ?).
  now apply aeval_tApp_head in H.
Qed.

Lemma aeval_mkApps_args Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists argsv,
    Forall2 (aeval Σ) args argsv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  apply aeval_mkApps_head in ev as ev_hd.
  destruct ev_hd as (hdv & ev_hd).
  specialize (IHargs _ _ ev) as (argsv & all).
  apply aeval_tApp_arg in ev_hd as (argv & ev_arg).
  exists (argv :: argsv).
  now constructor.
Qed.

Lemma aeval_mkApps_tCoFix Σ mfix idx args v :
  Σ ⊢ mkApps (tCoFix mfix idx) args ▷ v ->
  exists args', v = mkApps (tCoFix mfix idx) args'.
Proof.
  revert v.
  induction args using List.rev_ind; intros v ev.
  + exists [].
    now depelim ev.
  + rewrite mkApps_app in ev.
    cbn in *.
    depelim ev.
    * apply IHargs in ev1 as (? & ?).
      solve_discr.
    * apply IHargs in ev1 as (? & ?).
      solve_discr.
    * apply IHargs in ev1 as (? & ?).
      solve_discr.
    * apply IHargs in ev1 as (? & ?).
      solve_discr.
    * apply IHargs in ev1 as (argsv & ->).
      exists (argsv ++ [a']).
      now rewrite mkApps_app.
    * easy.
Qed.

Derive NoConfusionHom for EAst.global_decl.

Lemma aeval_deterministic Σ t v v' :
  Σ ⊢ t ▷ v ->
  Σ ⊢ t ▷ v' ->
  v = v'.
Proof.
  intros ev.
  revert v'.
  depind ev; intros v' ev'.
  - depelim ev'.
    + easy.
    + now apply IHev1 in ev'1.
    + apply IHev1 in ev'1.
      solve_discr.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; subst; easy.
    + easy.
  - depelim ev'.
    + now apply IHev1 in ev'1.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      subst.
      noconf ev'1.
      now apply IHev3 in ev'3.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; subst; easy.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      subst.
      now apply IHev2 in ev'2.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      apply mkApps_eq_inj in ev'1; try easy.
      depelim ev'1.
      noconf H.
      noconf H0.
      now apply IHev2 in ev'2.
    + apply IHev1 in ev'1; solve_discr.
    + apply aeval_mkApps_tCoFix in ev1 as (? & ?).
      solve_discr.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      solve_discr.
    + subst brs.
      noconf H0.
      now apply IHev2 in ev'2.
    + apply aeval_mkApps_tCoFix in ev1 as (? & ?).
      solve_discr.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      solve_discr.
    + apply IHev1 in ev'1.
      solve_discr.
    + apply IHev1 in ev'1.
      apply mkApps_eq_inj in ev'1; try easy.
      depelim ev'1.
      noconf H1.
      noconf H2.
      apply IHev2 in ev'2.
      now subst.
    + apply IHev1 in ev'1.
      apply mkApps_eq_inj in ev'1; try easy.
      depelim ev'1.
      noconf H1.
      noconf H2.
      apply IHev2 in ev'2.
      subst.
      rewrite H3 in H.
      noconf H.
      destruct H0 as [|(_ & ?)]; [easy|].
      easy.
    + apply IHev1 in ev'1.
      subst.
      rewrite isFixApp_mkApps in H1 by easy.
      cbn in H1.
      now rewrite orb_true_r in H1.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      solve_discr.
    + apply IHev1 in ev'1.
      solve_discr.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      apply mkApps_eq_inj in ev'1 as (ev'1 & <-); try easy.
      noconf ev'1.
      subst.
      rewrite H2 in H.
      noconf H.
      now destruct H3.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      apply mkApps_eq_inj in ev'1 as (ev'1 & <-); try easy.
      noconf ev'1.
      subst.
      rewrite H2 in H.
      noconf H.
      now apply IHev3 in ev'3.
    + apply IHev1 in ev'1.
      subst.
      rewrite isFixApp_mkApps in H2 by easy.
      cbn in H2.
      now rewrite orb_true_r in H2.
    + easy.
  - depelim ev'.
    + apply aeval_mkApps_tCoFix in ev'1 as (? & ?).
      solve_discr.
    + apply aeval_mkApps_tCoFix in ev'1 as (? & ?).
      solve_discr.
    + apply mkApps_eq_inj in H1 as (H1 & <-); try easy.
      noconf H1.
      rewrite H0 in H.
      noconf H.
      now apply IHev in ev'.
    + easy.
  - depelim ev'.
    + apply mkApps_eq_inj in H1 as (H1 & <-); try easy.
      noconf H1.
      rewrite H0 in H.
      noconf H.
      now apply IHev in ev'.
    + apply aeval_mkApps_tCoFix in ev'1 as (? & ?).
      solve_discr.
    + apply aeval_mkApps_tCoFix in ev' as (? & ?).
      solve_discr.
    + easy.
  - depelim ev'.
    + unfold ETyping.declared_constant in *.
      rewrite H1 in H.
      cbn in *.
      noconf H.
      rewrite H2 in H0.
      noconf H0.
      now apply IHev in ev'.
    + easy.
  - depelim ev'.
    + apply aeval_mkApps_tCoFix in ev1 as (? & ?); solve_discr.
    + apply IHev1 in ev'1.
      now apply mkApps_eq_inj in ev'1 as (ev'1 & <-).
    + apply IHev1 in ev'.
      solve_discr.
    + easy.
  - depelim ev'.
    + apply aeval_mkApps_tCoFix in ev as (? & ?); solve_discr.
    + apply IHev in ev'1.
      solve_discr.
    + easy.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      subst.
      easy.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      subst.
      easy.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      subst.
      now rewrite mkApps_app.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      subst.
      rewrite isFixApp_mkApps in H by easy.
      cbn in H.
      now rewrite orb_true_r in H.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      congruence.
    + easy.
  - now depelim ev'.
Qed.

Lemma eval_aeval Σ t v :
  eval Σ t v ->
  Σ ⊢ t ▷ v.
Proof.
  intros ev.
  induction ev using eval_evals_ind; try now econstructor.
  - destruct args as [|a args _] using List.rev_ind; [easy|].
    destruct args' as [|a' args' _] using List.rev_ind;
      [now apply Forall2_length in H3; rewrite app_length in *; cbn in *|].
    rewrite !mkApps_app in *.
    cbn in *.
    apply Forall2_app_r in H2 as (H2 & ev_a).
    apply Forall2_app_r in H3 as (H3 & aev_a).
    apply (aeval_fix Σ (mkApps f args) mfix idx args' narg fn a a' res); try easy.
    + admit.
    +
    induction args.
    + destruct args'; cbn in *.
      2: { apply Forall2_length in H2.
           cbn in *.
           rewrite app_length in H2.
           now cbn in *. }
      replace narg with 0 in * by easy.
      depelim H2.
      depelim H4.
      cbn in *.
      now eapply (aeval_fix _ _ mfix idx []).
    + cbn.
  - now eapply aeval_box.
  -
