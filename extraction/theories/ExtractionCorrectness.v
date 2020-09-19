From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import WcbvEvalType.
From Coq Require Import List.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import ErasureCorrectness.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import Prelim.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require PCUICWcbvEval.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import utils.

Open Scope string.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.
Notation "Σ 'e⊢' s ▷ t" := (EWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Definition Pis_constant (decl : P.global_decl) : bool :=
  match decl with
  | P.ConstantDecl _ => true
  | _ => false
  end.

Definition Ponly_constants (Σ : P.global_env) : P.global_env :=
  filter (Pis_constant ∘ snd) Σ.

Lemma Pdeclared_constant_only_constants Σ kn decl :
  declared_constant Σ kn decl ->
  declared_constant (Ponly_constants Σ) kn decl.
Proof.
  unfold declared_constant.
  intros lookup_decl.
  induction Σ; [easy|].
  destruct a as (kn' & decl').
  cbn in *.
  destruct (Pis_constant decl') eqn:isconst.
  - cbn in *.
    unfold eq_kername in *.
    destruct (kername_eq_dec _ _) as [<-|?]; easy.
  - apply IHΣ.
    unfold eq_kername in *.
    destruct (kername_eq_dec _ _).
    + inversion lookup_decl; subst; easy.
    + auto.
Qed.

Lemma Peval_only_constants Σ s t :
  Σ p⊢ s ▷ t ->
  Ponly_constants Σ p⊢ s ▷ t.
Proof.
  induction 1; eauto using PCUICWcbvEval.eval, Pdeclared_constant_only_constants.
Qed.

Lemma eval_const_construct_expanded Σ kn ind c im cm :
  trans_env Σ e⊢ E.tConst kn ▷ E.tConstruct ind c ->
  valid_masks_env im cm Σ ->
  is_expanded im cm (E.tConst kn).
Proof.
  intros ev valid.
  depelim ev.
  unfold valid_masks_env in valid.
  apply forallb_Forall in valid.
  apply declared_constant_trans in isdecl as (? & ? & nth).
  eapply nth_error_forall in nth; [|eassumption].
  cbn in *.
  rewrite H in nth.
  propify.
  destruct nth as (valid_mask_body & _).
  clear -ev valid_mask_body.
  apply valid_dearg_mask_spec in valid_mask_body as (Γ & inner & <- & <-).
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

Lemma extract_correct (Σ : P.global_env_ext) kn ui ind c ui' (wfΣ : wf_ext Σ) exΣ :
  axiom_free Σ ->
  welltyped Σ [] (P.tConst kn ui) ->
  Σ p⊢ P.tConst kn ui ▷ P.tConstruct ind c ui' ->
  (isErasable Σ [] (P.tConstruct ind c ui') -> False) ->
  extract_pcuic_env
    (pcuic_params check_masks_args)
    Σ (wf_ext_wf_squash wfΣ) [kn] (fun _ => false) = Ok exΣ ->
  trans_env exΣ e⊢ E.tConst kn ▷ E.tConstruct ind c.
Proof.
  intros ax [T wt] ev not_erasable ex.
  cbn in *.
  destruct validate_erases eqn:validate; cbn in *; [|congruence].
  destruct erase_global_decls_deps_recursive as [Σex|] eqn:er; cbn in *; [|congruence].
  destruct env_closed eqn:closed; cbn in *; [|congruence].
  destruct analyze_env eqn:an; cbn in *.
  destruct is_expanded_env eqn:isexp; cbn in *; [|congruence].
  destruct valid_masks_env eqn:valid; cbn in *; [|congruence].
  inversion_clear ex.
  rewrite trans_env_debox_env_types.

  assert (exists Σer,
             (erases_global Σ Σer) /\
             (forall kn decl, In (kn, decl) (trans_env Σex) -> In (kn, decl) Σer))
    as (Σer & erΣer & same_consts) by admit.
  eapply erases_correct in erΣer as ever.
  5: exact ev.
  3: exact wt.
  3: constructor.
  2: now constructor.
  destruct ever as (? & er' & ev').
  depelim er'; [|easy].
  { exfalso.
    eapply subject_reduction_eval in ev; eauto.

  assert (exists v', Σ;;; [] |- P.tConst kn ui ⇝ℇ v' /\ trans_env Σex e⊢ E.tConst kn ▷ v').
  { eapply erases_correct.
    - now constructor.
    - easy.
    - constructor.
    - a
  trans_env Σex e⊢ E.tConst kn ▷ E.tConstruct ind c).
  { eapply erases_correct.
  apply Peval_only_constants in ev.
Lemma validate_erases_erases_global Σ wfΣ :
  validate_erases erase_func Σ wfΣ ->
  erase_global_decls_deps_recursive erase_func Σ wfΣ
  erases_global (Ponly_constants Σ) (trans_env Σex)
  Admitted.
