From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ErasureCorrectness.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import WcbvEvalAux.
From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import ErasureCorrectness.
From MetaCoq.Erasure Require Import SafeErasureFunction.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import Prelim.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require PCUICWcbvEval.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import utils.

Open Scope string.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma eval_const_construct_mask {wfl:WcbvFlags} Σ kn ind c im cm :
  trans_env Σ e⊢ E.tConst kn ▷ E.tConstruct ind c ->
  valid_masks_env im cm Σ ->
  get_const_mask cm kn = [].
Proof.
  intros ev valid.
  depelim ev.
  eapply valid_dearg_mask_constant in valid; eauto.
  enough (#|get_const_mask cm kn| = 0) by (now destruct get_const_mask).
  apply valid_dearg_mask_spec in valid as (Γ & inner & <- & <-).
  clear -ev.
  induction #|Γ| as [|Γlen IH] eqn:eq in Γ, inner, ev |- *.
  - now destruct Γ.
  - destruct Γ as [|[na [body|]] Γ]; cbn in *.
    + easy.
    + depelim ev.
      refold.
      rewrite subst_it_mkLambda_or_LetIn in ev2.
      erewrite <- vasses_subst_context.
      eapply IH; [eassumption|].
      now rewrite length_subst_context.
    + depelim ev.
Qed.

Lemma wf_squash {Σ} :
  ∥wf_ext Σ∥ ->
  ∥wf Σ∥.
Proof. intros []. now constructor. Qed.

Lemma global_erased_with_deps_erases_deps_tConst Σ Σer kn cst :
  declared_constant Σ kn cst ->
  global_erased_with_deps Σ Σer kn ->
  erases_deps Σ Σer (E.tConst kn).
Proof.
  intros decl glob.
  destruct glob as [(?&?&?&?&?&?)|(?&?&?&?&?)].
  - econstructor; eauto.
  - unfold ETyping.declared_constant, ETyping.declared_minductive in *.
    congruence.
Qed.

Theorem extract_correct
        (wfl := default_wcbv_flags)
        (Σ : P.global_env_ext) (wfΣ : ∥wf_ext Σ∥)
        kn ui ind c ui' ignored exΣ :
  axiom_free Σ ->
  welltyped Σ [] (P.tConst kn ui) ->
  Σ p⊢ P.tConst kn ui ▷ P.tConstruct ind c ui' ->
  (isErasable Σ [] (P.tConstruct ind c ui') -> False) ->
  (forall k, ignored k = false) ->
  extract_pcuic_env
    (pcuic_args extract_within_coq)
    Σ (wf_squash wfΣ) (KernameSet.singleton kn) ignored = Ok exΣ ->
  ∥trans_env exΣ e⊢ E.tConst kn ▷ E.tConstruct ind c∥.
Proof.
  intros ax [T wt] ev not_erasable no_ignores ex.
  cbn in *.
  destruct env_closed eqn:closed; cbn in *; [|congruence].
  destruct analyze_env eqn:an; cbn in *.
  destruct is_expanded_env eqn:isexp; cbn in *; [|congruence].
  destruct valid_masks_env eqn:valid; cbn in *; [|congruence].
  inversion_clear ex.
  destruct wfΣ.
  eapply erases_correct in ev as (erv& erase_to & [erev]); eauto.
  2: constructor; auto.
  2: { eapply inversion_Const in wt as (?&?&?&?&?); auto.
       eapply global_erased_with_deps_erases_deps_tConst; eauto.
       eapply (erase_global_decls_deps_recursive_correct
                 _ (wf_squash (sq w))
                 (KernameSet.singleton kn)); eauto.
       - intros ? ->%KernameSet.singleton_spec.
         unfold declared_constant, PCUICAst.fst_ctx, fst_ctx in *.
         congruence.
       - now apply KernameSet.singleton_spec. }

  depelim erase_to; [|easy].
  eapply eval_const_construct_mask in erev as no_mask; eauto.
  assert (ctor_exp := erev).
  eapply eval_is_expanded_aux with (k := 0) in ctor_exp; eauto.
  2: now cbn; rewrite no_mask.
  cbn in *.
  eapply dearg_correct in erev; eauto.
  - cbn in *.
    rewrite no_mask in erev.
    destruct get_ctor_mask; [|easy].
    cbn in *.
    constructor.
    now apply eval_debox_env_types.
  - cbn.
    now rewrite no_mask.
Qed.

Print Assumptions extract_correct.

(* There are some assumptions of which almost all are in MetaCoq.
   From this project is only assume_env_wellformed assumption which is
   used to assume that the environments we extract are
   wellformed. MetaCoq's safe checker does not run from within Coq, so
   we cannot type check the environments. However, our environments
   are unquoted directly from Coq's kernel where they are already
   welltyped, so this is justified (and the same assumption is used in
   MetaCoq when they run their erasure).

   The rest of the assumptions are normal MetaCoq assumptions
   (which are justified in Coq Coq Correct!). *)
