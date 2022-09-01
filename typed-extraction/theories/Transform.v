From MetaCoq.Template Require Import utils.
From MetaCoq.TypedExtraction Require Import ExAst.
From MetaCoq.TypedExtraction Require Import ResultMonad.
From MetaCoq.TypedExtraction Require Import WcbvEvalAux.

Import MCString.
Import MCMonadNotation.

Definition Transform (A : Type) := A -> result A string.

Definition TemplateTransform := Transform Ast.Env.global_env.

Definition ExtractTransform := Transform ExAst.global_env.

Definition ExtractTransformCorrect `{wcbvf : EWcbvEval.WcbvFlags} (transform : ExtractTransform) : Type :=
  forall Σ Σopt kn ind c,
    EWcbvEval.with_constructor_as_block = false ->
    transform Σ = Ok Σopt ->
    trans_env Σ e⊢ tConst kn ▷ tConstruct ind c [] ->
    trans_env Σopt e⊢ tConst kn ▷ tConstruct ind c [].

Definition CorrectExtractTransform `{EWcbvEval.WcbvFlags} := ∑ t, ExtractTransformCorrect t.

Fixpoint compose_transforms {A : Type} (transforms : list (Transform A)) : Transform A :=
  match transforms with
  | [] => Ok
  | t :: transforms =>
    fun Σ : A =>
      match t Σ with
      | Ok Σopt => compose_transforms transforms Σopt
      | Err e => Err e
      end
  end.

Lemma compose_transforms_correct `{EWcbvEval.WcbvFlags} transforms :
  All ExtractTransformCorrect transforms ->
  ExtractTransformCorrect (compose_transforms transforms).
Proof.
  intros all. intros Σ Σopt kn ind c ? success ev.
  induction all in Σ, success, ev |- *; cbn in *.
  - now injection success as ->.
  - destruct x eqn:teq; [|congruence].
    eapply (p _ _ kn ind c) in teq; eauto.
Qed.
