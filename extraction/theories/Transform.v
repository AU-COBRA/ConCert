From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import WcbvEvalAux.
From Equations Require Import Equations.
From MetaCoq.Template Require Import utils.

Definition Transform := global_env -> result global_env string.
Definition TransformCorrect (transform : Transform) : Type :=
  forall Σ Σopt kn ind c (wf := EWcbvEval.opt_wcbv_flags),
    transform Σ = Ok Σopt ->
    trans_env Σ e⊢ tConst kn ▷ tConstruct ind c ->
    trans_env Σopt e⊢ tConst kn ▷ tConstruct ind c.

Definition CorrectTransform := ∑ t, TransformCorrect t.

Fixpoint compose_transforms (transforms : list Transform) : Transform :=
  match transforms with
  | [] => Ok
  | t :: transforms =>
    fun Σ =>
      Σopt <- t Σ;;
      compose_transforms transforms Σopt
  end.

Lemma compose_transforms_correct transforms :
  All TransformCorrect transforms ->
  TransformCorrect (compose_transforms transforms).
Proof.
  intros all Σ Σopt kn ind c wf success ev.
  subst wf.
  induction all in Σ, success, ev |- *; cbn in *.
  - now injection success as ->.
  - destruct x eqn:teq; [|congruence].
    eapply (p _ _ kn ind c) in teq; eauto.
Qed.
