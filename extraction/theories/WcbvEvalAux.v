From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require WcbvEvalAlt.
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

Derive Signature for eval.
Derive NoConfusionHom for term.

Lemma eval_tLetIn_inv Σ na val body res :
  Σ ⊢ tLetIn na val body ▷ res ->
  exists val_res,
    Σ ⊢ val ▷ val_res /\
    Σ ⊢ csubst val_res 0 body ▷ res.
Proof.
  intros ev.
  depind ev; try easy.
  - destruct args using List.rev_ind; [easy|].
    rewrite mkApps_app in *.
    cbn in *.
    congruence.
  - destruct args using List.rev_ind.
    + cbn in *.
      depelim H.
      subst f.
      now eapply IHev.
    + rewrite mkApps_app in *.
      cbn in *.
      congruence.
Qed.

Lemma eval_tLambda_inv Σ na body v :
  Σ ⊢ tLambda na body ▷ v ->
  v = tLambda na body.
Proof.
  intros ev.
  depind ev.
  - destruct args as [|? ? _] using List.rev_ind; [easy|].
    now rewrite mkApps_app in *.
  - destruct args as [|? ? _] using List.rev_ind.
    + cbn in *.
      subst f.
      erewrite <- IHev; [|easy].
      destruct args'; [easy|].
      now apply Forall2_length in H.
    + now rewrite mkApps_app in *.
  - easy.
Qed.

Lemma eval_tApp_tLambda_inv Σ na body a v :
  Σ ⊢ tApp (tLambda na body) a ▷ v ->
  exists av,
    Σ ⊢ a ▷ av /\
    Σ ⊢ csubst av 0 body ▷ v.
Proof.
  intros ev.
  depind ev.
  - now apply eval_tLambda_inv in ev1.
  - apply eval_tLambda_inv in ev1.
    inversion ev1; subst; clear ev1.
    easy.
  - destruct args as [|? ? _] using List.rev_ind; [easy|].
    rewrite mkApps_app in *.
    cbn in *.
    inversion H3; subst; clear H3.
    destruct args using List.rev_ind; [|now rewrite mkApps_app in *].
    cbn in *.
    subst f.
    now apply eval_tLambda_inv in ev1.
  - destruct args as [|? ? _] using List.rev_ind.
    + cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      easy.
    + rewrite mkApps_app in *.
      cbn in *.
      inversion H1; subst; clear H1.
      destruct args using List.rev_ind; [|now rewrite mkApps_app in *].
      cbn in *.
      subst f.
      now apply eval_tLambda_inv in ev.
  - apply eval_tLambda_inv in ev1.
    now subst f'.
  - easy.
Qed.

Lemma eval_tEvar_inv Σ n ts v :
  Σ ⊢ tEvar n ts ▷ v ->
  False.
Proof.
  intros ev.
  depind ev.
  - destruct args using List.rev_ind; [easy|].
    now rewrite mkApps_app in *.
  - destruct args using List.rev_ind; [|now rewrite mkApps_app in *].
    cbn in *.
    subst.
    easy.
  - easy.
Qed.

Lemma eval_value Σ v :
  value v ->
  Σ ⊢ v ▷ v.
Proof.
  Admitted.

Inductive eval_app Σ hd arg : term -> Prop :=
| eval_app_box argv :
    Σ ⊢ hd ▷ tBox ->
    Σ ⊢ arg ▷ argv ->
    eval_app Σ hd arg tBox
| eval_app_lambda na body argv v :
    Σ ⊢ hd ▷ tLambda na body ->
    Σ ⊢ arg ▷ argv ->
    Σ ⊢ csubst argv 0 body ▷ v ->
    eval_app Σ hd arg v
| eval_app_ctor ind c args argv v :
    Σ ⊢ hd ▷ mkApps (tConstruct ind c) args ->
    Σ ⊢ arg ▷ argv ->
    Forall value args ->
    eval_app Σ hd arg v
| eval_app_fix defs idx args argv v :
    Σ ⊢ hd ▷ mkApps (tFix defs idx) args ->
    Σ ⊢ arg ▷ argv ->
    isStuckFix (tFix defs idx) args ->
    Forall value args ->
    eval_app Σ hd arg v
| eval_app_cofix defs idx args argv v :
    Σ ⊢ hd ▷ mkApps (tCoFix defs idx) args ->
    Σ ⊢ arg ▷ argv ->
    Forall value args ->
    eval_app Σ hd arg v.

Arguments isStuckFix : simpl nomatch.

Lemma eval_tApp_inv {Σ hd arg v} :
  Σ ⊢ tApp hd arg ▷ v ->
  eval_app Σ hd arg v.
Proof.
  intros ev.
  depind ev.
  - now econstructor.
  - now eapply eval_app_lambda.
  - destruct args using List.rev_ind; [easy|].
    clear IHargs.
    rewrite mkApps_app in H3.
    cbn in *.
    apply Forall2_length in H2 as args_len.
    rewrite !app_length in *.
    cbn in *.
    destruct args' as [|a' args' _] using List.rev_ind; [cbn in *; abstract lia|].
    inversion H3; subst; clear H3.
    assert (stuck: isStuckFix (tFix mfix idx) args').
    { unfold isStuckFix, cunfold_fix, ETyping.unfold_fix in *.
      destruct (nth_error mfix idx) as [f'|]; [|easy].
      replace (rarg f') with narg by congruence.
      unfold ETyping.is_constructor_or_box.
      rewrite !app_length in *.
      cbn in *.
      rewrite (proj2 (nth_error_None _ _)) by abstract lia.
      easy. }
    apply (eval_app_fix Σ _ _ mfix idx args' a' _).
    + apply eval_fix_value.
      * easy.
      * apply Forall2_app_r in H2.
        easy.
      * easy.
    + now apply Forall2_app_r in H2.
    + easy.
    + apply Forall2_app_r in H2.
      destruct H2 as (all_eval & _).
      clear -all_eval.
      induction all_eval; [easy|].
      constructor; [|easy].
      now eapply eval_to_value.
  - destruct args as [|a args _] using List.rev_ind.
    + cbn in *.
      apply Forall2_length in H.
      destruct args'; [|easy].
      eapply IHev.
      now f_equal.
    + rewrite mkApps_app in H1.
      apply Forall2_length in H as args_len.
      rewrite !app_length in *.
      cbn in *.
      destruct args' as [|a' args' _] using List.rev_ind; [cbn in *; abstract lia|].
      inversion H1; subst; clear H1.
      assert (stuck: isStuckFix (tFix mfix idx) args').
      { unfold isStuckFix in *.
        destruct (ETyping.unfold_fix mfix idx) as [(? & ?)|]; [|easy].
        unfold ETyping.is_constructor_or_box in H0.
        destruct (Nat.ltb_spec n #|args'|).
        - rewrite nth_error_app_lt in H0 by easy.
          apply H0.
        - unfold ETyping.is_constructor_or_box.
          now rewrite (proj2 (nth_error_None _ _)) by abstract lia. }
      apply (eval_app_fix Σ _ _ mfix idx args' a' _).
      * apply eval_fix_value; [easy| |easy].
        now apply Forall2_app_r in H.
      * now apply Forall2_app_r in H.
      * easy.
      * apply Forall2_app_r in H.
        destruct H as (all_eval & _).
        clear -all_eval.
        induction all_eval; [easy|].
        constructor; [|easy].
        now eapply eval_to_value.
  - apply eval_to_value in ev1 as f'value.
    destruct f'value.
    + destruct t; cbn in *; try congruence.
      * now eapply (eval_app_ctor _ _ _ _ _ []).
      * now eapply (eval_app_cofix _ _ _ _ _ []).
    + destruct t; cbn in *; try congruence.
      * now econstructor.
      * now econstructor.
    + clear -H1 H.
      exfalso.
      destruct f0; try easy.
      propify.
      destruct H as ((_ & not_fix) & _).
      now rewrite isFixApp_mkApps in not_fix.
  - easy.
Qed.

Lemma eval_tApp_head Σ hd arg v :
  Σ ⊢ tApp hd arg ▷ v ->
  exists hdv, Σ ⊢ hd ▷ hdv.
Proof.
  intros ev.
  now destruct (eval_tApp_inv ev).
Qed.

Lemma eval_tApp_arg Σ hd arg v :
  Σ ⊢ tApp hd arg ▷ v ->
  exists argv, Σ ⊢ arg ▷ argv.
Proof.
  intros ev.
  now destruct (eval_tApp_inv ev).
Qed.

Lemma eval_mkApps_head Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists hdv, Σ ⊢ hd ▷ hdv.
Proof.
  revert hd v.
  induction args using List.rev_ind; intros hd v ev; [easy|].
  rewrite mkApps_app in ev.
  cbn in *.
  apply eval_tApp_head in ev as (hdv & ev_hd).
  now apply IHargs in ev_hd.
Qed.

Lemma eval_mkApps_args Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists argsv, Forall2 (eval Σ) args argsv.
Proof.
  revert hd v.
  induction args using List.rev_ind; intros hd v ev; [easy|].
  rewrite mkApps_app in ev.
  cbn in *.
  apply eval_tApp_head in ev as ev_hd.
  destruct ev_hd as (hd' & ev_hd').
  apply eval_tApp_arg in ev as ev_arg.
  destruct ev_arg as (arg & ev_arg).
  destruct (IHargs _ _ ev_hd') as (args' & args'_all).
  exists (args' ++ [arg]).
  now apply Forall2_app.
Qed.

Lemma eval_deterministic {Σ a v v'} :
  Σ ⊢ a ▷ v ->
  Σ ⊢ a ▷ v' ->
  v = v'.
Proof.
  intros ev ev'.
  apply WcbvEvalAlt.eval_aeval in ev.
  apply WcbvEvalAlt.eval_aeval in ev'.
  now eapply WcbvEvalAlt.aeval_deterministic.
Qed.

Lemma decompose_app_ex hd :
  exists hd' args',
    hd = mkApps hd' args' /\
    negb (isApp hd').
Proof.
  destruct (decompose_app hd) as [hd' args'] eqn:decomp_eq.
  exists hd', args'.
  split.
  - now apply decompose_app_inv.
  - now eapply decompose_app_notApp.
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
  - admit.
  - destruct (mkApps_elim f args).
    admit.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_app_cong.
  - easy.
Admitted.

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

Lemma mkApps_csubst Σ a av na body args v :
  Σ ⊢ a ▷ av ->
  Σ ⊢ mkApps (tApp (tLambda na body) a) args ▷ v ->
  Σ ⊢ mkApps (csubst av 0 body) args ▷ v.
Proof.
  Admitted.

Definition env_closed (Σ : EAst.global_declarations) :=
  Forall (decl_closed ∘ snd) Σ.

Lemma closed_constant Σ kn cst :
  env_closed Σ ->
  ETyping.declared_constant Σ kn cst ->
  match EAst.cst_body cst with
  | Some val => closed val = true
  | None => True
  end.
Proof.
  intros env_clos decl_const.
  unfold ETyping.declared_constant in decl_const.
  rewrite lookup_env_find in decl_const.
  destruct (find _ _) eqn:find; [|easy].
  apply find_some in find.
  unfold env_closed in env_clos.
  rewrite Forall_forall in env_clos.
  specialize (env_clos _ (proj1 find)).
  destruct p.
  cbn in *.
  now inversion decl_const; subst.
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
  Forall2 (eval Σ) args args' ->
  Forall2 (fun t v => closed t -> closed v) args args' ->
  Forall (closedn 0) args'.
Proof.
  intros args_clos args_eval impl_clos.
  induction args_eval; [easy|].
  depelim args_clos.
  depelim impl_clos.
  easy.
Qed.

Lemma eval_closed Σ t v :
  env_closed Σ ->
  closed t ->
  Σ ⊢ t ▷ v ->
  closed v.
Proof.
  intros env_clos clos ev.
  induction ev using eval_evals_ind; cbn in *; propify.
  - easy.
  - apply IHev3.
    now apply closed_csubst.
  - apply IHev2.
    now apply closed_csubst.
  - apply IHev.
    pose proof (closed_constant _ _ _ env_clos H).
    now rewrite H0 in *.
  - apply IHev2.
    unfold ETyping.iota_red.
    apply closed_mkApps.
    + destruct clos as (_ & clos).
      clear -clos.
      rewrite forallb_forall in clos.
      rewrite nth_nth_error.
      destruct (nth_error _ _) eqn:nth; [|easy].
      apply nth_error_In in nth.
      now apply clos.
    + apply Forall_skipn.
      eapply closed_mkApps_args.
      apply IHev1.
      easy.
  - subst brs.
    cbn in *.
    propify.
    apply IHev2.
    apply closed_mkApps; [easy|].
    clear.
    induction n; [constructor|].
    constructor; easy.
  - apply IHev2.
    specialize (IHev1 clos).
    apply closed_mkApps_args in IHev1.
    rewrite nth_nth_error in *.
    destruct (nth_error _ _) eqn:nth_eq.
    + apply nth_error_In in nth_eq.
      rewrite Forall_forall in IHev1.
      now apply IHev1.
    + easy.
  - easy.
  - apply IHev2.
    apply closed_mkApps_inv in clos.
    apply closed_mkApps.
    + rewrite <- closed_unfold_fix_cunfold_eq in * by easy.
      now eapply closed_unfold_fix.
    + now eapply (all_closed _ args args').
  - apply closed_mkApps_inv in clos as (? & ?).
    apply closed_mkApps; [easy|].
    now eapply (all_closed _ args args').
  - apply IHev.
    split; [|easy].
    destruct clos as (clos & _).
    apply closed_mkApps_inv in clos.
    cbn in *.
    apply closed_mkApps; [|easy].
    rewrite <- closed_unfold_cofix_cunfold_eq in * by easy.
    now eapply closed_unfold_cofix.
  - apply IHev.
    apply closed_mkApps_inv in clos.
    apply closed_mkApps; [|easy].
    rewrite <- closed_unfold_cofix_cunfold_eq in * by easy.
    now eapply closed_unfold_cofix.
  - easy.
  - easy.
Qed.

Fixpoint f (a b : nat) {struct b} := b.
Definition prog := (fun x => f x) 0 0.

Definition f' := tFix [{| dname := nAnon;
                          dbody := tLambda nAnon (tLambda nAnon (tRel 0));
                          rarg := 1 |}] 0.

Definition prog' := tApp (tApp (tLambda nAnon (tApp f' (tRel 0))) tBox) tBox.

Lemma stuck_fix_eval Σ f a v :
  Σ ⊢ tApp (tFix [f] 0) a ▷ v ->
  Extract.E.rarg f = 1 ->
  (forall av, v = tApp (tFix [f] 0) av -> False) ->
  False.
Proof.
  intros ev is_1 is_false.
  apply eval_tApp_arg in ev as arg.
  destruct arg as (arg & ev_arg).
  apply (is_false arg).
  eapply eval_deterministic.
  - easy.
  - eapply (eval_fix_value _ _ _ _ [a] [arg]).
    + now constructor.
    + easy.
    + cbn.
      now rewrite is_1.
Qed.

Lemma no_eval Σ v :
  Σ ⊢ prog' ▷ v ->
  False.
Proof.
  intros ev.
  unfold prog' in ev.
  depind ev.
  + apply eval_tApp_tLambda_inv in ev1 as (av & ev_a & ev_sub).
    cbn in *.
    now eapply stuck_fix_eval in ev_sub.
  + apply eval_tApp_tLambda_inv in ev1 as (av & ev_a & ev_sub).
    cbn in *.
    now eapply stuck_fix_eval in ev_sub.
  + change (tApp (tApp (tLambda nAnon (tApp f' (tRel 0))) tBox) tBox)
      with (mkApps (tLambda nAnon (tApp f' (tRel 0))) [tBox; tBox]) in H3.
    destruct (mkApps_elim f0 args).
    apply mkApps_eq_inj in H3 as (<- & <-); try easy.
    clear i.
    destruct n as [|[]].
    * cbn in *.
      now apply eval_tLambda_inv in ev1.
    * cbn in *.
      apply eval_tApp_tLambda_inv in ev1 as (av & ev_a & ev_sub).
      cbn in *.
      now eapply stuck_fix_eval in ev_sub.
    * now rewrite !skipn_cons, skipn_nil in H1.
  + change (tApp (tApp (tLambda nAnon (tApp f' (tRel 0))) tBox) tBox)
      with (mkApps (tLambda nAnon (tApp f' (tRel 0))) [tBox; tBox]) in H1.
    destruct (mkApps_elim f0 args).
    apply mkApps_eq_inj in H1 as (<- & <-); try easy.
    clear i.
    destruct n as [|[]].
    * cbn in *.
      now apply eval_tLambda_inv in ev.
    * cbn in *.
      apply eval_tApp_tLambda_inv in ev as (av & ev_a & ev_sub).
      cbn in *.
      now eapply stuck_fix_eval in ev_sub.
    * cbn in *.
      rewrite firstn_nil in *.
      cbn in *.
      easy.
  + apply eval_tApp_tLambda_inv in ev1 as (av & ev_a & ev_sub).
    cbn in *.
    unfold map_def in *.
    cbn in *.
    apply stuck_fix_eval in ev_sub; try easy.
    intros.
    now subst.
  + easy.
Qed.

Print Assumptions no_eval.
