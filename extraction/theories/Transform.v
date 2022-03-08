From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import WcbvEvalAux.

Definition Transform (A : Type) := A -> result A string.

Definition TemplateTransform := Transform Ast.global_env.

Definition ExtractTransform := Transform ExAst.global_env.

Definition ExtractTransformCorrect (transform : ExtractTransform) : Type :=
  forall Σ Σopt kn ind c (wf := EWcbvEval.opt_wcbv_flags),
    transform Σ = Ok Σopt ->
    trans_env Σ e⊢ tConst kn ▷ tConstruct ind c ->
    trans_env Σopt e⊢ tConst kn ▷ tConstruct ind c.

Definition CorrectExtractTransform := ∑ t, ExtractTransformCorrect t.

Fixpoint compose_transforms {A : Type} (transforms : list (Transform A)) : Transform A :=
  match transforms with
  | [] => Ok
  | t :: transforms =>
    fun Σ : A =>
      Σopt <- t Σ;;
      compose_transforms transforms Σopt
  end.

Lemma compose_transforms_correct transforms :
  All ExtractTransformCorrect transforms ->
  ExtractTransformCorrect (compose_transforms transforms).
Proof.
  intros all Σ Σopt kn ind c wf success ev.
  subst wf.
  induction all in Σ, success, ev |- *; cbn in *.
  - now injection success as ->.
  - destruct x eqn:teq; [|congruence].
    eapply (p _ _ kn ind c) in teq; eauto.
Qed.
