From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import EDeps.
From MetaCoq.Erasure Require Import ErasureCorrectness.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.Erasure Require Import ESubstitution.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import SafeErasureFunction.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICInduction.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICSR.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICWcbvEval.
From MetaCoq.PCUIC Require Import PCUICWeakeningEnv.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import utils.

Open Scope string.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma erases_deps_recursive Σ Σer t T et :
  wf_ext Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ et ->
  (forall k,
      KernameSet.In k (term_global_deps et) ->
      match P.lookup_env Σ k with
      | Some (P.ConstantDecl _) => erases_deps Σ Σer (E.tConst k)
      | _ => True
      end) ->
  erases_deps Σ Σer et.
Proof.
  intros wf wt er deps_er.
  induction er in t, T, et, wf, wt, er, deps_er |- * using erases_forall_list_ind; cbn in *.
  - now constructor.
  - now constructor.
  - now apply inversion_Evar in wt.
  - constructor.
    apply inversion_Lambda in wt as (? & ? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & ? & ? & ? & ? & ?); eauto.
    constructor.
    + eapply IHer1; eauto.
      intros.
      apply deps_er.
      apply KernameSet.union_spec; eauto.
    + eapply IHer2; eauto.
      intros.
      apply deps_er.
      apply KernameSet.union_spec; eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
    constructor.
    + eapply IHer1; eauto.
      intros.
      apply deps_er.
      apply KernameSet.union_spec; eauto.
    + eapply IHer2; eauto.
      intros.
      apply deps_er.
      apply KernameSet.union_spec; eauto.
  - apply inversion_Const in wt as (? & ? & ? & ? & ?); eauto.
    unshelve epose proof (deps_er kn _) as deps_er; [now apply KernameSet.singleton_spec|].
    unfold declared_constant in d.
    unfold PCUICAst.fst_ctx, fst_ctx in *.
    now rewrite d in deps_er.
  - now constructor.
  - apply inversion_Case in wt
      as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
    constructor.
    + eapply IHer; eauto.
      intros.
      eapply deps_er.
      apply KernameSet.union_spec; right.
      apply knset_in_fold_left; auto.
    + clear -wf a X H0 deps_er.
      revert brs' x5 a X H0 deps_er.
      induction brs; intros brs' x5 brtys typ er deps.
      { now depelim er. }
      depelim brtys.
      depelim typ.
      depelim er.
      destruct p as ((? & ?) & ?).
      destruct p0.
      constructor.
      * eapply H; eauto.
        intros.
        apply deps.
        cbn.
        destruct y0; cbn in *.
        apply KernameSet.union_spec; right.
        apply knset_in_fold_left.
        left.
        apply KernameSet.union_spec; auto.
      * eapply IHbrs; eauto.
        intros.
        apply deps.
        cbn.
        destruct y0; cbn in *.
        apply KernameSet.union_spec.
        apply KernameSet.union_spec in H0 as [|]; [tauto|].
        right.
        apply knset_in_fold_left.
        apply knset_in_fold_left in H0 as [|]; [|tauto].
        left.
        apply KernameSet.union_spec; auto.
  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?); eauto.
    constructor.
    eapply IHer; eauto.
    intros; apply deps_er.
    destruct p as ((? & ?) & ?).
    apply KernameSet.union_spec; auto.
  - constructor.
    apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    clear -wf a0 X H deps_er.
    revert a0 X H deps_er.
    generalize mfix at 1 2 4 6.
    intros mfix_gen.
    revert mfix'.
    induction mfix; cbn in *; intros mfix' typ er all_deps deps.
    { now depelim er. }
    depelim typ.
    depelim er.
    depelim all_deps.
    destruct p.
    destruct p0 as (?&?&?).
    constructor.
    + eapply H; eauto.
      intros.
      apply deps.
      cbn in *.
      apply knset_in_fold_left.
      left.
      apply KernameSet.union_spec; auto.
    + apply IHmfix; eauto.
      intros.
      apply deps.
      cbn in *.
      apply knset_in_fold_left.
      apply knset_in_fold_left in H0 as [|]; [|tauto].
      now apply KernameSet.empty_spec in H0.
  - constructor.
    apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    clear -wf a0 X H deps_er.
    revert a0 X H deps_er.
    generalize mfix at 1 2 4 6.
    intros mfix_gen.
    revert mfix'.
    induction mfix; cbn in *; intros mfix' typ er all_deps deps.
    { now depelim er. }
    depelim typ.
    depelim er.
    depelim all_deps.
    destruct p as (?&?&?).
    constructor.
    + eapply H; eauto.
      intros.
      apply deps.
      cbn in *.
      apply knset_in_fold_left.
      left.
      apply KernameSet.union_spec; auto.
    + apply IHmfix; eauto.
      intros.
      apply deps.
      cbn in *.
      apply knset_in_fold_left.
      apply knset_in_fold_left in H0 as [|]; [|tauto].
      now apply KernameSet.empty_spec in H0.
  - now constructor.
Qed.

Opaque erase_type flag_of_type SafeErasureFunction.wf_reduction.
Lemma erase_global_decls_deps_recursive_correct Σ wfΣ include ignore Σex :
  (forall k, ignore k = false) ->
  erase_global_decls_deps_recursive Σ wfΣ include ignore = Ok Σex ->
  (forall k,
      KernameSet.In k include ->
      match P.lookup_env Σ k with
      | Some (P.ConstantDecl cst) =>
        erases_deps Σ (trans_env Σex) (E.tConst k)
      | _ => True
      end).
Proof.
  intros no_ignores er.
  induction Σ as [|(kn, decl) Σ IH] in wfΣ, include, Σex, er |- *; [easy|].
  simpl in *.
  match goal with
  | [H: context[erase_global_decl _ ?wfΣarg _ _ ?wfdeclarg] |- _] =>
      set (wfΣext := wfΣarg) in *; clearbody wfΣext;
        set (wfdecl := wfdeclarg) in *; clearbody wfdecl
  end.
  match goal with
  | [H: context[erase_global_decls_deps_recursive _ ?wfΣarg] |- _] =>
    set (wfΣprev := wfΣarg) in *; clearbody wfΣprev
  end.

  rewrite no_ignores in er.
  destruct (KernameSet.mem kn include) eqn:mem; cycle 1.
  - cbn in *.
    intros.
    eapply IH with (k := k) in er; eauto.
    unfold eq_kername.
    destruct kername_eq_dec as [->|].
    + now apply KernameSet.mem_spec in H.
    + destruct P.lookup_env; [|easy].
      destruct g; [|easy].
      destruct wfΣ.
      now apply erases_deps_weaken.
  - cbn in *.
    destruct erase_global_decl eqn:erdecl; cbn in *; [|congruence].
    destruct erase_global_decls_deps_recursive eqn:errec; [|congruence].
    inversion er; subst; clear er.
    intros k isin.
    unfold eq_kername.
    destruct kername_eq_dec as [->|]; cycle 1.
    { cbn in *.
      eapply IH with (k := k) in errec; eauto.
      destruct P.lookup_env; [|easy].
      destruct g; [|easy].
      destruct wfΣ.
      destruct t;
        eauto using erases_deps_cons, erases_deps_weaken.
      now apply KernameSet.union_spec. }
    destruct decl; [|easy].
    cbn -[erase_constant_decl] in *.
    destruct erase_constant_decl eqn:erconst; cbn -[erase_constant_decl] in *; [|congruence].
    unfold erase_constant_decl in erconst.
    destruct flag_of_type; cbn in *.
    destruct is_arity; cbn in *.
    + destruct is_sort; [|congruence].
      destruct c.
      destruct cst_body; cbn in *; [|congruence].
      destruct erase_type; cbn in *.
      inversion erconst; subst; clear erconst.
      inversion erdecl; subst; clear erdecl.
      cbn in *.
      econstructor.
      * unfold declared_constant; cbn; rewrite eq_kername_refl.
        reflexivity.
      * unfold ETyping.declared_constant; cbn.
        destruct kername_eq_dec; [|congruence].
        reflexivity.
      * cbn.
        destruct wfΣ as [wfΣ].
        destruct wfdecl as [wfdecl].
        destruct i0 as (u & [redu]).
        eapply type_reduction in wfdecl; eauto.
        2: now inversion wfΣ.
        constructor.
        eapply (Is_type_extends (Σ, _)).
        2: now eauto.
        2: eexists [_]; reflexivity.
        1: now eauto.
        eexists _.
        split; [eassumption|].
        now left.
      * intros.
        cbn in *.
        inversion H; subst; clear H.
        now constructor.
    + destruct erase_type; cbn in *.
      destruct c; cbn in *.
      destruct cst_body; cycle 1.
      { inversion erconst; subst; clear erconst.
        inversion erdecl; subst; clear erdecl.
        cbn in *.
        econstructor.
        - unfold declared_constant; cbn; rewrite eq_kername_refl; reflexivity.
        - unfold ETyping.declared_constant; cbn.
          destruct kername_eq_dec; [|congruence].
          reflexivity.
        - easy.
        - intros.
          cbn in *.
          congruence. }

      match goal with
      | [H: context[SafeErasureFunction.erase _ _ _ _ ?p] |- _] =>
        set (twt := p) in *; clearbody twt
      end.
      inversion erconst; subst; clear erconst.
      inversion erdecl; subst; clear erdecl.
      cbn in *.
      specialize (IH _ _ _ errec).
      destruct wfΣ as [wfΣ].
      destruct wfdecl as [wfdecl].
      econstructor.
      * unfold declared_constant; cbn; rewrite eq_kername_refl; reflexivity.
      * unfold ETyping.declared_constant; cbn.
        destruct kername_eq_dec; [|congruence].
        reflexivity.
      * cbn.
        eapply type_reduction in wfdecl; eauto.
        2: now inversion wfΣ.
        eapply (erases_extends (_, _)).
        2: now eauto.
        1: now inversion wfΣ.
        2: eexists [_]; reflexivity.
        1: now eauto.
        apply SafeErasureFunction.erases_erase.
      * intros.
        cbn in *.
        noconf H.
        destruct wfΣext.
        apply erases_deps_cons; eauto.
        eapply (erases_deps_recursive (Σ, cst_universes)); eauto.
        { apply SafeErasureFunction.erases_erase. }
        intros.
        apply IH.
        apply KernameSet.union_spec; left.
        apply KernameSet.union_spec; auto.
Qed.
