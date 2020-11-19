From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Extraction.
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
From MetaCoq.Erasure Require Import ErasureFunction.
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

Lemma map_map_In {X Y Z} xs (f : forall (x : X), In x xs -> Y) (g : Y -> Z) :
  map g (map_In xs f) = map_In xs (fun x isin => g (f x isin)).
Proof.
  induction xs in xs, f |- *; [easy|].
  cbn.
  f_equal.
  apply IHxs.
Qed.

Lemma map_In_ext {X Y : Type} {xs : list X} {f : forall x, In x xs -> Y} g :
  (forall x isin, f x isin = g x isin) ->
  map_In xs f = map_In xs g.
Proof.
  induction xs in xs, f, g |- *; intros all_eq; [easy|].
  cbn.
  f_equal.
  - apply all_eq.
  - apply IHxs.
    intros; apply all_eq.
Qed.

Lemma erase_ind_body_correct Σ wfΣ kn mib oib wf :
  erases_one_inductive_body oib (trans_oib (erase_ind_body Σ wfΣ kn mib oib wf)).
Proof.
  unfold erases_one_inductive_body, trans_oib, erase_ind_body.
  simpl.
  apply and_assoc.
  split; [|intuition auto].
  split.
  - rewrite map_map_In.
    rewrite (map_In_ext (fun x _ => x.1.1)) by (now intros; destruct decompose_arr).
    induction P.ind_ctors; [now constructor|].
    constructor; [easy|].
    apply IHl.
  - induction P.ind_projs; [now constructor|].
    cbn.
    constructor; [easy|].
    apply IHl.
  - destruct wf as [(i & [])].
    unfold isPropositionalArity.
    rewrite ind_arity_eq.
    now rewrite !destArity_it_mkProd_or_LetIn.
Qed.

Lemma erase_ind_correct Σ wfΣ kn mib wf :
  erases_mutual_inductive_body mib (trans_mib (erase_ind Σ wfΣ kn mib wf)).
Proof.
  unfold trans_mib, erase_ind.
  cbn.
  split; [|easy].
  cbn.
  generalize (Erasure.erase_ind_obligation_1 Σ kn mib wf).
  intros wfobl.
  induction P.ind_bodies; [constructor|].
  cbn in *.
  constructor; auto.
  apply erase_ind_body_correct.
Qed.

Opaque erase_type flag_of_type ErasureFunction.wf_reduction.
Lemma erase_global_decls_deps_recursive_correct Σ wfΣ include ignore_deps :
  (forall k, ignore_deps k = false) ->
  (forall k, KernameSet.In k include -> PCUICAst.lookup_env Σ k <> None) ->
  includes_deps Σ (trans_env (erase_global_decls_deps_recursive Σ wfΣ include ignore_deps)) include.
Proof.
  cut (is_true (KernameSet.subset include include)); [|now apply KernameSet.subset_spec].
  generalize include at 1 3 5 as include'.
  intros include' sub no_ignores all_in.
  induction Σ as [|(kn, decl) Σ IH] in Σ, wfΣ, all_in, include, include', sub |- *.
  { intros kn isin.
    now apply all_in in isin. }
  simpl in *.
  match goal with
  | |- context[erase_global_decl _ ?wfΣarg _ _ ?wfdeclarg] =>
      set (wfΣext := wfΣarg) in *; clearbody wfΣext;
        set (wfdecl := wfdeclarg) in *; clearbody wfdecl
  end.
  match goal with
  | |- context[erase_global_decls_deps_recursive _ ?wfΣarg] =>
    set (wfΣprev := wfΣarg) in *; clearbody wfΣprev
  end.

  destruct wfΣ as [wfΣ].
  rewrite no_ignores.
  destruct KernameSet.mem eqn:mem; cycle 1.
  - intros kn' isin.
    apply global_erases_with_deps_weaken; auto.
    eapply IH; eauto.
    intros k kisin.
    specialize (all_in _ kisin).
    unfold eq_kername in *.
    apply KernameSet.subset_spec in sub.
    apply sub in kisin.
    apply KernameSet.mem_spec in kisin.
    destruct (kername_eq_dec k kn); congruence.
  - cbn in *.
    intros k isin.
    destruct (kername_eq_dec k kn) as [->|]; cycle 1.
    { apply global_erases_with_deps_cons; auto.
      eapply (IH wfΣprev _ (KernameSet.singleton k)).
      - apply KernameSet.subset_spec.
        intros ? ?.
        eapply KernameSet.singleton_spec in H; subst a.
        apply KernameSet.union_spec.
        right.
        apply KernameSet.subset_spec in sub.
        now apply sub.
      - specialize (all_in _ isin).
        intros isink <-%KernameSet.singleton_spec.
        apply KernameSet.mem_spec in isin.
        unfold eq_kername in *.
        destruct kername_eq_dec; congruence.
      - now apply KernameSet.singleton_spec. }

    cbn.
    destruct decl; [left|right].
    all: unfold declared_constant, declared_minductive,
         ETyping.declared_constant, ETyping.declared_minductive; cbn.
    all: unfold eq_kername.
    all: destruct kername_eq_dec; cbn; [|congruence].
    + eexists; split; [reflexivity|].
      unfold erase_constant_decl.
      destruct flag_of_type; cbn in *.
      destruct conv_ar; cbn in *.
      * destruct c; cbn in *.
        destruct cst_body; cbn in *; cycle 1.
        { eexists; split; [reflexivity|]; cbn.
          intuition congruence. }

        eexists; split; [reflexivity|]; cbn.
        split; last first.
        { intros ? H.
          noconf H.
          constructor. }

        destruct wfdecl as [wfdecl].
        destruct c0 as [ctx univ [r]].
        eapply type_reduction in wfdecl; eauto.
        2: now inversion wfΣ.
        constructor.
        eapply (Is_type_extends (Σ, _)).
        2: now eauto.
        2: eexists [_]; reflexivity.
        1: now eauto.
        eexists _.
        split; [eassumption|].
        left.
        apply isArity_mkNormalArity.
      * eexists; split; [reflexivity|]; cbn.
        unfold trans_cst; cbn.
        destruct c; cbn in *.
        destruct cst_body; cbn in *; cycle 1.
        { intuition congruence. }

        match goal with
        | |- context[erase _ _ _ _ ?p] =>
          set (twt := p) in *; clearbody twt
        end.
        destruct wfdecl as [wfdecl].
        split.
        -- eapply type_reduction in wfdecl; eauto.
           2: now inversion wfΣ.
           eapply (erases_extends (_, _)).
           2: now eauto.
           1: now inversion wfΣ.
           2: eexists [_]; reflexivity.
           1: now eauto.
           apply erases_erase.
        -- intros.
           noconf H.
           destruct wfΣext.
           apply erases_deps_cons; auto.
           eapply (@erase_global_erases_deps (Σ, cst_universes)); eauto.
           { apply erases_erase. }
           eapply IH.
           ++ apply KernameSet.subset_spec.
              intros ? isin'.
              apply KernameSet.union_spec; left.
              now apply KernameSet.union_spec; right.
           ++ intros ? isin'.
              eapply term_global_deps_spec in isin' as [(? & ?)]; eauto.
              ** cbn in *. congruence.
              ** apply erases_erase.
    + eexists _, _; split; [reflexivity|]; split; [reflexivity|].
      apply erase_ind_correct.
Qed.
