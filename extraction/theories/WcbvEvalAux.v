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

(*
Lemma eval_csubst_commute Σ t tv s v :
  Σ ⊢ t ▷ tv ->
  Σ ⊢ csubst tv 0 s ▷ v ->
  Σ ⊢ csubst t 0 s ▷ v .
Proof.
  revert t tv v.
  induction s using term_forall_list_ind; intros t tv v ev_t ev_tv.
  - depelim ev_tv.
    + admit.
    + admit.
    + cbn in *.
*)

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
      unfold ETyping.is_constructor.
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
        unfold ETyping.is_constructor in H0.
        destruct (Nat.ltb_spec n #|args'|).
        - rewrite nth_error_app_lt in H0 by easy.
          apply H0.
        - unfold ETyping.is_constructor.
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

Lemma isLambda_mkApps t args :
  isLambda t = false -> isLambda (mkApps t args) = false.
Proof.
  induction args using List.rev_ind; [easy|].
  now rewrite mkApps_app.
Qed.

Lemma isFixApp_mkApps t args :
  isFixApp t = false -> isFixApp (mkApps t args) = false.
Proof.
  induction args using List.rev_ind; [easy|].
  rewrite mkApps_app.
  cbn.
  unfold isFixApp.
  cbn.
  rewrite Prelim.fst_decompose_app_rec.
  easy.
Qed.

Lemma isBox_mkApps t args :
  isBox t = false -> isBox (mkApps t args) = false.
Proof.
  induction args using List.rev_ind; [easy|].
  now rewrite mkApps_app.
Qed.

Ltac gen_equalities :=
  repeat
    match goal with
    | [H: ?Σ ⊢ ?a ▷ ?v, IH: forall _ : term, ?Σ ⊢ ?a ▷ _ -> _ |- _ = _] =>
      let t := constr:(IH _ H) in
      let tty := type of t in
      (match goal with
       | [H: tty |- _] => fail 2
       end || pose proof t)
    end;
  repeat
    match goal with
    | [H: ?a = ?a |- _] => clear H
    end.

Lemma eval_mkApps_tCoFix Σ mfix idx args v :
  Σ ⊢ mkApps (tCoFix mfix idx) args ▷ v ->
  exists argsv,
  Σ ⊢ mkApps (tCoFix mfix idx) args ▷ mkApps (tCoFix mfix idx) argsv.
Proof.
  intros ev.
  apply eval_mkApps_args in ev as (argsv & ev_argsv).
  exists argsv.
  revert argsv ev_argsv.
  induction args using List.rev_ind; intros argsv ev_argsv.
  - apply Forall2_length in ev_argsv.
    destruct argsv; [|easy].
    now apply eval_atom.
  - apply Forall2_length in ev_argsv as argsv_len.
    rewrite app_length in *.
    destruct argsv using List.rev_ind; [now cbn in *|].
    rewrite !mkApps_app.
    cbn.
    apply eval_app_cong.
    + apply IHargs.
      now apply Forall2_app_r in ev_argsv.
    + now rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps.
    + now apply Forall2_app_r in ev_argsv.
Qed.

Lemma eval_tApp_heads Σ hd hd' hdv arg v :
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ tApp hd arg ▷ v ->
  Σ ⊢ tApp hd' arg ▷ v.
Proof.
  Admitted.

Lemma eval_mkApps_heads Σ hd hd' hdv args v :
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ mkApps hd args ▷ v ->
  Σ ⊢ mkApps hd' args ▷ v.
Proof.
  Admitted.

Lemma eval_deterministic Σ a v v' :
  Σ ⊢ a ▷ v ->
  Σ ⊢ a ▷ v' ->
  v = v'.
Proof.
  intros ev1.
  revert v'.
  induction ev1 using eval_evals_ind; intros v' ev2.
  - apply eval_tApp_inv in ev2.
    depelim ev2; try easy.
    + now gen_equalities.
    + gen_equalities; solve_discr.
    + gen_equalities; solve_discr.
    + gen_equalities; solve_discr.
  - apply eval_tApp_inv in ev2.
    depelim ev2; gen_equalities; try congruence; try solve_discr.
    subst; gen_equalities.
    inversion H5; subst.
    now gen_equalities.
  - apply eval_tLetIn_inv in ev2.
    destruct ev2 as (? & ? & ?).
    gen_equalities.
    subst.
    now gen_equalities.
  - depind ev2.
    + destruct args using List.rev_ind; [easy|].
      now rewrite mkApps_app in H5.
    + destruct args using List.rev_ind; [|now rewrite mkApps_app in *].
      cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      cbn in *.
      eapply IHev2; easy.
    + unfold ETyping.declared_constant in *.
      replace body0 with body in * by congruence.
      now gen_equalities.
    + easy.
  - depind ev2.
    + gen_equalities.
      solve_discr.
      inversion H; subst; clear H.
      now gen_equalities.
    + gen_equalities.
      solve_discr.
    + destruct args using List.rev_ind; [easy|].
      rewrite mkApps_app in H3.
      solve_discr.
    + destruct args using List.rev_ind; cycle 1.
      { now rewrite mkApps_app in H1. }
      cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      cbn in *.
      easy.
    + destruct (eval_mkApps_tCoFix _ _ _ _ _ ev1_1).
      gen_equalities; solve_discr.
    + easy.
  - depind ev2.
    + gen_equalities.
      solve_discr.
    + inversion H; subst.
      now gen_equalities.
    + destruct args using List.rev_ind; [easy|].
      now rewrite mkApps_app in *.
    + destruct args using List.rev_ind; cycle 1.
      { now rewrite mkApps_app in H1. }
      cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      easy.
    + destruct (eval_mkApps_tCoFix _ _ _ _ _ ev1_1).
      gen_equalities; solve_discr.
    + easy.
  - depind ev2.
    + destruct args using List.rev_ind; [easy|].
      now rewrite mkApps_app in H3.
    + destruct args using List.rev_ind; cycle 1.
      { now rewrite mkApps_app in H1. }
      cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      easy.
    + destruct (eval_mkApps_tCoFix _ _ _ _ _ ev1_1).
      gen_equalities; solve_discr.
    + gen_equalities.
      solve_discr.
      inversion H; subst.
      now gen_equalities.
    + gen_equalities.
      solve_discr.
    + easy.
  - depind ev2.
    + destruct args using List.rev_ind; [easy|].
      now rewrite mkApps_app in H3.
    + destruct args using List.rev_ind; cycle 1.
      { now rewrite mkApps_app in H1. }
      cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      easy.
    + destruct (eval_mkApps_tCoFix _ _ _ _ _ ev1_1).
      gen_equalities; solve_discr.
    + gen_equalities.
      solve_discr.
    + easy.
    + easy.
  - destruct args as [|rarg args _] using List.rev_ind; [easy|].
    destruct args' as [|rargv args' _] using List.rev_ind;
      [apply Forall2_length in H2;
       rewrite app_length in *;
       now cbn in *|].
    rewrite mkApps_app in ev2.
    cbn in *.
    depelim ev2.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma mkApps_csubst Σ a av na body args v :
  Σ ⊢ a ▷ av ->
  Σ ⊢ mkApps (tApp (tLambda na body) a) args ▷ v ->
  Σ ⊢ mkApps (csubst av 0 body) args ▷ v.
Proof.
  Admitted.

  (*revert na body av v.
  induction args using List.rev_ind; intros na body av v ev; cbn in *.
  - apply eval_
    depelim ev.
    + destruct args using List.rev_ind; [easy|].
      rewrite mkApps_app in H3; easy.
    + destruct args using List.rev_ind; [easy|].
      rewrite mkApps_app in H3; easy.
*)
(*
Lemma eval_mkApps_inv Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists hdv argsv,
    Σ ⊢ hd ▷ hdv /\
    Forall2 (eval Σ) args argsv /\
    match args with
    |
    (args = [] \/ head_of_app_cases hdv).
Proof.
  revert hd v.
  induction args; intros hd v ev.
  - cbn in *.
    now exists v, [].
  - cbn in *.
    specialize (IHargs _ _ ev).
    destruct IHargs as (app_hdv & app_argsv & ev_app & ? & ?).
    apply eval_tApp_inv in ev_app.
    destruct ev_app as (hdv & argv & ev_hd & ev_arg & head_hdv).
    exists hdv, (argv :: app_argsv).
    easy.
Qed.

Inductive eval_mkApps Σ hd : list term -> term -> Prop :=
| eval_mkApps_nil v : Σ ⊢ hd ▷ v -> eval_mkApps Σ hd [] v
| eval_mkApps_snoc args v a av appv :
    eval_mkApps Σ hd args v ->
    Σ ⊢ a ▷ av ->
    Σ ⊢ tApp (mkApps hd args) a ▷ appv ->
    eval_mkApps Σ hd (args ++ [a]) appv.

Derive Signature for eval_mkApps.

(*
Lemma eval_spine_app Σ hd args args' v :
  eval_spine Σ v hd (args ++ args') ->
  exists v',
    eval_spine Σ v' hd args /\
    eval_spine Σ v v' args'.
Proof.
  revert hd args' v.
  induction args; intros hd args' v eval_app; cbn in *.
  - depelim eval_app.
    + exists v.

    exists hd.
    split; [constructor|easy].
*)

Lemma eval_mkApps_inv Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  eval_mkApps Σ hd args v.
Proof.
  revert hd v.
  induction args using List.rev_ind; intros hd v ev.
  - now constructor.
  - rewrite mkApps_app in ev.
    cbn in *.
    apply eval_tApp_arg in ev as ev_x.
    apply eval_tApp_head in ev as ev_hd.
    destruct ev_x as (xv & ev_x).
    destruct ev_hd as (hdv & ev_hd).
    specialize (IHargs _ _ ev_hd).
    apply (eval_mkApps_snoc Σ hd args hdv x xv v); easy.
Qed.

(*
Lemma eval_mkApps_head Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists hdv, Σ ⊢ hd ▷ hdv.
Proof.
  intros ev.
  apply eval_mkApps_inv in ev.
  destruct (eval_mkApps_inv _ _ _ _ ev); eexists.
  -
  eexists.
  easy.
Qed.

Lemma eval_mkApps_args Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists argsv, Forall2 (eval Σ) args argsv.
Proof.
  intros ev.
  now destruct (eval_mkApps_inv _ _ _ _ ev) as (? & ? & ?).
Qed.
*)
*)

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

Lemma eval_closed Σ t v :
  env_closed Σ ->
  closed t ->
  Σ ⊢ t ▷ v ->
  closed v.
Proof.
  intros env_clos clos ev.
  induction ev using eval_evals_ind; cbn in *.
  - easy.
  - propify.
    apply IHev3.
    now apply closed_csubst.
  - propify.
    apply IHev2.
    now apply closed_csubst.
  - apply IHev.
    pose proof (closed_constant _ _ _ env_clos H).
    now rewrite H0 in *.
  - propify.
    apply IHev2.
    unfold ETyping.iota_red.
    apply closed_mkApps.
    + destruct clos as (_ & clos).
      clear -clos.
      revert c.
      induction brs; intros c.
      * now rewrite nth_nth_error, nth_error_nil.
      * cbn in *.
        propify.
        now destruct a, c.
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
      now rewrite Forall_forall in IHev1.
    + easy.
  - easy.
  - apply IHev2.
    specialize (IHev1 (closed_mkApps_head _ _ clos)).
    apply closed_mkApps.
    + apply forallb_Forall in IHev1.
      unfold cunfold_fix in H.
      destruct (nth_error mfix idx) eqn:nth_eq; [|easy].
      apply nth_error_In in nth_eq.
      rewrite Forall_forall in IHev1.
      exact (todo "Fixpoint unfold").
    + exact (todo "Fixpoint args").
  - apply closed_mkApps.
    + cbn.
      apply IHev.
      now eapply closed_mkApps_head.
    + exact (todo "Stuck fixpoint unfold").
  - exact (todo "CoFix").
  - exact (todo "CoFix").
  - propify.
    easy.
  - easy.
Qed.


(*
Lemma eval_deterministic Σ t v v' :
  Σ ⊢ t ▷ v ->
  Σ ⊢ t ▷ v' ->
  v = v'.
Proof.
  intros ev1.
  revert v'.
  induction ev1 using eval_evals_ind; intros v' ev2.
  - admit.
  - apply eval_tApp_inv in ev2.
    destruct ev2 as (hdv & argv & ev_hd & ev_arg & hd_app).
    inversion hd_app; subst; clear hd_app;
      gen_equalities; try congruence; try solve_discr.
    inversion H2; subst.
    admit.
  - apply eval_tLetIn in ev2.
    destruct ev2 as (? & ? & ?).
    gen_equalities.
    subst.
    now gen_equalities.
  - depind ev2.
    + destruct args using List.rev_ind; [easy|].
      now rewrite mkApps_app in H5.
    + destruct args using List.rev_ind; [|now rewrite mkApps_app in *].
      cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      cbn in *.
      eapply IHev2; easy.
    + unfold ETyping.declared_constant in *.
      replace body0 with body in * by congruence.
      now gen_equalities.
    + easy.
  - depind ev2.
    + gen_equalities.
      solve_discr.
      inversion H; subst; clear H.
      now gen_equalities.
    + gen_equalities.
      solve_discr.
    + destruct args using List.rev_ind; [easy|].
      rewrite mkApps_app in H3.
      solve_discr.
    + destruct args using List.rev_ind; cycle 1.
      { now rewrite mkApps_app in H1. }
      cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      cbn in *.
      easy.
    + admit.
    + easy.
  - depind ev2; subst.
    + gen_equalities.
      solve_discr.
    + inversion H; subst.
      now gen_equalities.
    + destruct args using List.rev_ind; [easy|].
      now rewrite mkApps_app in *.
    + destruct args using List.rev_ind; cycle 1.
      { now rewrite mkApps_app in H1. }
      cbn in *.
      subst f.
      apply Forall2_length in H.
      destruct args'; [|easy].
      easy.
    + apply eval_mkApps_inv in ev1_1.
      destruct ev1_1 as (hdv & argsv & ev_hd & ev_args & disc).
      destruct disc as [->|].
      * cbn in *.
        gen_equalities.
        subst.
        assert (Σ ⊢ tCoFix mfix idx ▷ tCoFix mfix idx); [|gen_equalities; easy].
        now apply eval_atom.
      * admit.
    + easy.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
    assert (Σ ⊢ tProj (i, pars, arg) discr ▷ tBox).
    { now apply eval_proj_box. }
    gen_equalities.
      eapply IHev2
      subst brs.
      cbn in *.
      easy.
      apply IHev1.
      subst f.
      2: {
      gen_equalities; try congruence; try solve_discr.

    +
    + gen_equalities; congruence.
    + gen_equalities; subst.
      inversion H2; subst.
      gen_equalities.
      admit.
    + gen_equalities.
      solve_discr.
    + gen_equalities.
      solve_discr.
    + gen_equai
    depelim ev2.
    + gen_equalities; congruence.
    + gen_equalities.
      inversion H2.
      subst.
      now gen_equalities.
    + destruct args as [|a'' args _] using List.rev_ind; [easy|].
      rewrite mkApps_app in H3.
      cbn in *.
      inversion H3; subst; clear H3.

      replace f with (mkApps f0 args) in * by congruence.
      apply eval_mkApps_inv in ev2_2.
      destruct ev2_2 as (? & ? & ? & ? & ?).

      gen_equalities.
      subst a'0.
      inversion H2; subst; clear H2.
      apply IHev1_3.
      let x := (has_hypothesis_of_type term) in
      match x with
      | 0 => idtac "foo"
      | 1 => idtac "bar"
      end.
      gen_equalities.
      gen_equalities.
    +
    apply eval_tApp_inv in ev2 as (hdv & argv & ev_hd & ev_arg & hd_cases).
    apply IHev1_3.
    depelim hd_cases; try solve_congr.
    + apply IHev1_3.
    +
    inversion hd_cases; subst.
    apply eval_tApp_head in ev2.
    destruct ev2 as (hdv & ev_hd & hdv_cases).
    depelim hdv_cases;
      specialize (IHev1_1 _ ev_hd); try congruence.
*)

(*
Lemma eval_tLambda_to_tBox Σ na body :
  Σ ⊢ tLambda na body ▷ tBox ->
  False.
Proof.
  intros.
  depelim H.
  - destruct args using List.rev_ind; [easy|now rewrite mkApps_app in *].
  - destruct args' using List.rev_ind; [easy|now rewrite mkApps_app in *].
Qed.

Lemma eval_tApp_tLambda Σ na body hd v :
  Σ ⊢ tApp (tLambda na body) hd ▷ v ->
  Σ ⊢ csubst hd 0 body ▷ v.
Proof.
  intros.
  depelim H.
  - now apply eval_tLambda_to_tBox in H.
  - easy.
*)
