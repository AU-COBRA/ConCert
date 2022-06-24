(* Pass that removes discrimination (matches and projections) on things in Prop.
   This uses MetaCoq's optimization but adapted to run on our environments. *)
From ConCert.Extraction Require Import ExAst.
From MetaCoq.Erasure Require Import EOptimizePropDiscr.

Definition optimize_constant_body Σ cst :=
  {| cst_type := cst_type cst;
     cst_body := option_map (optimize Σ) (cst_body cst) |}.

Definition optimize_decl Σ d :=
  match d with
  | ConstantDecl cst => ConstantDecl (optimize_constant_body Σ cst)
  | _ => d
  end.

Lemma trans_env_fresh_globals Σ :
  fresh_globals Σ ->
  EnvMap.EnvMap.fresh_globals (trans_env Σ).
Proof.
  intros fg.
  induction fg.
  + constructor.
  + cbn. constructor;auto.
    clear IHfg.
    induction H.
    * constructor.
    * cbn. inversion fg;subst;cbn in *. now constructor.
Qed.

Program Definition optimize_env (Σ : global_env) (fgΣ : fresh_globals Σ) : global_env :=
  List.map (MCProd.on_snd (optimize_decl (EEnvMap.GlobalContextMap.make (trans_env Σ) _))) Σ.
Next Obligation.
  now apply trans_env_fresh_globals.
Qed.

Module Ee := EWcbvEval.

Lemma trans_env_optimize_env Σ fgΣ :
  trans_env (optimize_env Σ fgΣ) =
  EOptimizePropDiscr.optimize_env (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)).
Proof.
(*   unfold trans_env. *)
(*   unfold EOptimizePropDiscr.optimize_env. *)
(*   unfold optimize_env. *)
(*   rewrite !List.map_map. *)
(*   apply List.map_ext. *)
(*   intros ((kn&has_deps)&decl). *)
(*   cbn. *)
(*   f_equal. *)
(*   destruct decl; auto. *)
(*   cbn. *)
(*   now destruct o. *)
(* Qed. *)
Admitted.

Lemma optimize_correct Σ fgΣ t v :
  @Prelim.Ee.eval Ee.default_wcbv_flags (trans_env Σ) t v ->
  @Prelim.Ee.eval
      (EWcbvEval.disable_prop_cases Ee.opt_wcbv_flags)
      (trans_env (optimize_env Σ fgΣ))
      (optimize (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)) t)
      (optimize (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)) v).
Proof.
  intros ev.
  rewrite trans_env_optimize_env.
  remember (EEnvMap.GlobalContextMap.make _ _) as Σ0.
  eapply (EOptimizePropDiscr.optimize_correct (Σ:=Σ0)) with (t0:=t) (v0:=v);eauto.
Admitted.
