(* Pass that removes discrimination (matches and projections) on things in Prop.
   This uses MetaCoq's optimization but adapted to run on our environments. *)

From ConCert.Extraction Require Import ExAst.
From MetaCoq.Erasure Require Import EOptimizePropDiscr.
From MetaCoq.Erasure Require Import EWcbvEval.

Definition optimize_constant_body Σ cst :=
  {| cst_type := cst_type cst;
     cst_body := option_map (optimize Σ) (cst_body cst) |}.

Definition optimize_decl Σ d :=
  match d with
  | ConstantDecl cst => ConstantDecl (optimize_constant_body Σ cst)
  | _ => d
  end.

Definition optimize_env (Σ : global_env) : global_env :=
  map (on_snd (optimize_decl (trans_env Σ))) Σ.

Module Ee := EWcbvEval.

Lemma trans_env_optimize_env Σ :
  trans_env (optimize_env Σ) =
  EOptimizePropDiscr.optimize_env (trans_env Σ).
Proof.
  unfold trans_env.
  unfold EOptimizePropDiscr.optimize_env.
  unfold optimize_env.
  rewrite !map_map.
  apply map_ext.
  intros ((kn&has_deps)&decl).
  cbn.
  f_equal.
  destruct decl; auto.
  cbn.
  now destruct o.
Qed.

Lemma optimize_correct Σ t v :
  @Ee.eval Ee.default_wcbv_flags (trans_env Σ) t v ->
  @Ee.eval
      Ee.opt_wcbv_flags
      (trans_env (optimize_env Σ))
      (optimize (trans_env Σ) t)
      (optimize (trans_env Σ) v).
Proof.
  intros ev.
  rewrite trans_env_optimize_env.
  now apply EOptimizePropDiscr.optimize_correct.
Qed.
