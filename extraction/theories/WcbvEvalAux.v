From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import EInversion.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.
Set Equations Transparent.

Notation "Σ ⊢ s ▷ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma eval_tApp_head Σ hd arg v :
  Σ ⊢ tApp hd arg ▷ v ->
  ∑ hdv, Σ ⊢ hd ▷ hdv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma eval_tApp_arg Σ hd arg v :
  Σ ⊢ tApp hd arg ▷ v ->
  ∑ argv, Σ ⊢ arg ▷ argv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma eval_mkApps_head Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  ∑ hdv, Σ ⊢ hd ▷ hdv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  specialize (IHargs _ _ ev) as (? & ?).
  now apply eval_tApp_head in e.
Qed.

Lemma eval_mkApps_args Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  ∑ argsv, All2 (eval Σ) args argsv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  apply eval_mkApps_head in ev as ev_hd.
  destruct ev_hd as (hdv & ev_hd).
  specialize (IHargs _ _ ev) as (argsv & all).
  apply eval_tApp_arg in ev_hd as (argv & ev_arg).
  exists (argv :: argsv).
  now constructor.
Qed.

Lemma eval_tApp_heads Σ hd hd' hdv arg v :
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ tApp hd arg ▷ v ->
  Σ ⊢ tApp hd' arg ▷ v.
Proof.
  intros ev_hd ev_hd' ev_app.
  depind ev_app.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_box.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_beta.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix_value.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_app_cong.
  - easy.
Qed.

Derive Signature for eval.
Derive NoConfusionHom for term.

Lemma eval_tLetIn_inv Σ na val body res :
  Σ ⊢ tLetIn na val body ▷ res ->
  ∑ val_res,
    Σ ⊢ val ▷ val_res ×
    Σ ⊢ csubst val_res 0 body ▷ res.
Proof. intros ev; depelim ev; easy. Qed.

Lemma eval_tLambda_inv Σ na body v :
  Σ ⊢ tLambda na body ▷ v ->
  v = tLambda na body.
Proof. now intros ev; depelim ev. Qed.

Lemma eval_tApp_tLambda_inv Σ na body a v :
  Σ ⊢ tApp (tLambda na body) a ▷ v ->
  ∑ av,
    Σ ⊢ a ▷ av ×
    Σ ⊢ csubst av 0 body ▷ v.
Proof.
  intros ev.
  depelim ev.
  - now apply eval_tLambda_inv in ev1.
  - apply eval_tLambda_inv in ev1.
    inversion ev1; subst; clear ev1.
    easy.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - now apply eval_tLambda_inv in ev1 as ->.
  - easy.
Qed.

Lemma eval_mkApps_heads Σ hd hd' hdv args v :
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ mkApps hd args ▷ v ->
  Σ ⊢ mkApps hd' args ▷ v.
Proof.
  revert hd hd' hdv v.
  induction args as [|a args]; intros hd hd' hdv v ev_hd ev_hd' ev.
  - cbn in *.
    now rewrite (eval_deterministic ev ev_hd) in *.
  - cbn in *.
    apply eval_mkApps_head in ev as ev_app_hd.
    destruct ev_app_hd as (app_hdv & ev_app_hd).
    eapply IHargs.
    2: {
      eapply eval_tApp_heads; [| |exact ev_app_hd].
      all: easy.
    }
    + easy.
    + easy.
Qed.

Definition env_closed (Σ : EAst.global_declarations) :=
  Forall (decl_closed ∘ snd) Σ.

Lemma closed_constant Σ kn cst body :
  env_closed Σ ->
  ETyping.declared_constant Σ kn cst ->
  EAst.cst_body cst = Some body ->
  closed body.
Proof.
  intros env_clos decl_const body_eq.
  unfold ETyping.declared_constant in decl_const.
  rewrite lookup_env_find in decl_const.
  destruct (find _ _) eqn:find; [|easy].
  apply find_some in find.
  unfold env_closed in env_clos.
  rewrite Forall_forall in env_clos.
  specialize (env_clos _ (proj1 find)).
  destruct p.
  cbn in *.
  noconf decl_const.
  cbn in *.
  now rewrite body_eq in env_clos.
Qed.

Lemma closed_unfold_fix mfix idx narg fn :
  closed (tFix mfix idx) ->
  ETyping.unfold_fix mfix idx = Some (narg, fn) ->
  closed fn.
Proof.
  cbn.
  intros clos_fix fix_eq.
  rewrite Nat.add_0_r in *.
  unfold ETyping.unfold_fix in *.
  destruct (nth_error mfix idx) eqn:Heq; [|easy].
  noconf fix_eq.
  eapply closedn_subst0.
  - clear Heq.
    unfold ETyping.fix_subst.
    generalize #|mfix|.
    induction n as [|n IH]; [easy|].
    constructor.
    + cbn.
      now rewrite Nat.add_0_r.
    + easy.
  - apply nth_error_In in Heq.
    apply forallb_Forall in clos_fix.
    rewrite Forall_forall in clos_fix.
    now rewrite ETyping.fix_subst_length.
Qed.

Lemma closed_unfold_cofix mfix idx narg fn :
  closed (tFix mfix idx) ->
  ETyping.unfold_cofix mfix idx = Some (narg, fn) ->
  closed fn.
Proof.
  cbn.
  intros clos_fix fix_eq.
  rewrite Nat.add_0_r in *.
  unfold ETyping.unfold_cofix in *.
  destruct (nth_error mfix idx) eqn:Heq; [|easy].
  noconf fix_eq.
  eapply closedn_subst0.
  - clear Heq.
    unfold ETyping.cofix_subst.
    generalize #|mfix|.
    induction n as [|n IH]; [easy|].
    constructor.
    + cbn.
      now rewrite Nat.add_0_r.
    + easy.
  - apply nth_error_In in Heq.
    apply forallb_Forall in clos_fix.
    rewrite Forall_forall in clos_fix.
    now rewrite ETyping.cofix_subst_length.
Qed.

Lemma all_closed Σ args args' :
  Forall (closedn 0) args ->
  All2 (eval Σ) args args' ->
  Forall2 (fun t v => closed t -> closed v) args args' ->
  Forall (closedn 0) args'.
Proof.
  intros args_clos args_eval impl_clos.
  induction args_eval; [easy|].
  depelim args_clos.
  depelim impl_clos.
  easy.
Qed.

Lemma closed_iota_red pars c args brs :
  Forall (fun a => closed a) args ->
  Forall (fun t => closed t.2) brs ->
  closed (ETyping.iota_red pars c args brs).
Proof.
  intros clos_args clos_brs.
  unfold ETyping.iota_red.
  apply closed_mkApps.
  - rewrite nth_nth_error.
    destruct (nth_error _ _) eqn:nth; [|easy].
    now eapply nth_error_forall in nth; [|eassumption].
  - now apply Forall_skipn.
Qed.

Lemma closed_cunfold_fix defs n narg f :
  cunfold_fix defs n = Some (narg, f) ->
  closed (tFix defs n) ->
  closed f.
Proof.
  intros eq clos.
  rewrite <- closed_unfold_fix_cunfold_eq in eq by easy.
  now eapply closed_unfold_fix.
Qed.

Lemma closed_cunfold_cofix defs n narg f :
  cunfold_cofix defs n = Some (narg, f) ->
  closed (tCoFix defs n) ->
  closed f.
Proof.
  intros eq clos.
  rewrite <- closed_unfold_cofix_cunfold_eq in eq by easy.
  now eapply closed_unfold_cofix.
Qed.

Lemma eval_closed Σ t v :
  Σ ⊢ t ▷ v ->
  env_closed Σ ->
  closed t ->
  closed v.
Proof.
  intros ev env_clos clos.
  induction ev; cbn in *; propify.
  - easy.
  - apply IHev3.
    now apply closed_csubst.
  - apply IHev2.
    now apply closed_csubst.
  - apply IHev2.
    apply closed_iota_red.
    + now eapply closed_mkApps_args.
    + now apply forallb_Forall.
  - subst brs.
    cbn in *.
    propify.
    apply IHev2.
    apply closed_mkApps; [easy|].
    clear.
    induction n; [constructor|].
    constructor; easy.
  - apply IHev3.
    split; [|easy].
    destruct clos as (clos & _).
    specialize (IHev1 clos).
    apply closed_mkApps_inv in IHev1 as (? & ?).
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_fix.
  - easy.
  - apply IHev.
    split; [|easy].
    destruct clos as (clos & _).
    apply closed_mkApps_inv in clos.
    cbn in *.
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_cofix.
  - apply IHev.
    apply closed_mkApps_inv in clos.
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_cofix.
  - apply IHev.
    now eapply closed_constant.
  - apply IHev2.
    apply closed_mkApps_args in IHev1; [|easy].
    rewrite nth_nth_error in *.
    destruct (nth_error _ _) eqn:nth_eq.
    + apply nth_error_In in nth_eq.
      rewrite Forall_forall in IHev1.
      now apply IHev1.
    + easy.
  - easy.
  - easy.
  - easy.
Qed.

Lemma eval_stuck_fix Σ args argsv mfix idx :
  All2 (eval Σ) args argsv ->
  isStuckFix (tFix mfix idx) argsv ->
  Σ ⊢ (mkApps (tFix mfix idx) args) ▷ (mkApps (tFix mfix idx) argsv).
Proof.
  revert argsv.
  induction args as [|a args IH] using MCList.rev_ind;
    intros argsv all stuck.
  - apply All2_length in all.
    destruct argsv; [|easy].
    now apply eval_atom.
  - destruct argsv as [|? ? _] using MCList.rev_ind;
      [apply All2_length in all; rewrite app_length in all; now cbn in *|].
    apply All2_app_r in all as (all & ev_a).
    rewrite <- !mkApps_nested.
    cbn in *.
    destruct (cunfold_fix mfix idx) as [(? & ?)|] eqn:cuf; [|easy].
    eapply eval_fix_value.
    + apply IH; [easy|].
      destruct (cunfold_fix mfix idx) as [(? & ?)|]; [|easy].
      unfold ETyping.is_nth_constructor_app_or_box in *.
      destruct (nth_error argsv _) eqn:nth; [|easy].
      now erewrite nth_error_app_left in stuck.
    + easy.
    + easy.
    + destruct (Nat.eqb_spec #|argsv| n) as [<-|].
      * unfold ETyping.is_nth_constructor_app_or_box in *.
        now rewrite nth_error_snoc in stuck.
      * now left.
Qed.

Lemma value_final Σ e : value e -> Σ ⊢ e ▷ e.
Proof.
  induction 1 using value_values_rect; cbn in *.
  - now apply eval_atom.
  - induction l using MCList.rev_ind.
    + cbn in *.
      destruct t; cbn in *; propify; try easy; now apply eval_atom.
    + rewrite mkApps_app.
      cbn.
      apply All_app in H0 as (? & ?).
      apply All_app in H1 as (? & ?).
      depelim a0.
      depelim a2.
      apply eval_app_cong.
      * now apply IHl.
      * rewrite isFixApp_mkApps by (now destruct t).
        destruct l using List.rev_ind; [now destruct t|].
        rewrite mkApps_app.
        now destruct t.
      * easy.
  - destruct f; try easy.
    apply All_All2_refl in H0.
    now apply eval_stuck_fix.
Qed.
