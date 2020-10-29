From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ErasureCorrectness.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Extraction Require Import Transform.
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
        (wfl := opt_wcbv_flags)
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
  cbn -[dearg_transform] in *.
  destruct dearg_transform eqn:dt; cbn -[dearg_transform] in *; [|congruence].
  injection ex as ->.
  destruct wfΣ.
  eapply erases_correct in ev as (erv&erase_to&[erev]).
  2: constructor; auto.
  2: eassumption.
  2: apply erases_tConst.
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

  constructor.
  eapply dearg_transform_correct; eauto.
  apply (OptimizePropDiscr.optimize_correct _ (tConst kn) (tConstruct ind c)).
  assumption.
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
