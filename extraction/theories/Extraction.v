(* This file provides the main function for invoking our extraction. *)

From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Extraction Require OptimizePropDiscr.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Transform.
From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import SafeErasureFunction.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.

Local Open Scope bool.
Local Open Scope string.
Import MonadNotation.

Record extract_pcuic_params :=
  { (* Whether to remove discrimination (matches and projections) on things in Prop.
     Necessary to run the transforms. *)
    optimize_prop_discr : bool;
    (* The transforms to apply. Only run when optimize_prop_discr is true. *)
    transforms : list Transform; }.

Definition extract_pcuic_env
           (params : extract_pcuic_params)
           (Σ : P.global_env) (wfΣ : ∥PT.wf Σ∥)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=

  let Σ := erase_global_decls_deps_recursive Σ wfΣ seeds ignore in

  if optimize_prop_discr params then
    let Σ := OptimizePropDiscr.optimize_env Σ in
    compose_transforms (transforms params) Σ
  else
    Ok Σ.

Record extract_template_env_params :=
  { (* Function to use to check wellformedness of the environment *)
    check_wf_env_func : forall Σ, result (∥PT.wf Σ∥) string;
    pcuic_args : extract_pcuic_params }.

Definition extract_template_env
           (params : extract_template_env_params)
           (Σ : T.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := T2P.trans_global_decls Σ in
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

(* MetaCoq's safe checker does not run from within Coq, only when extracting.
   To work around this we assume environments are well formed when extracting
   from within Coq. This is justified since our environments are produced by quoting
   and thus come directly from Coq, where they have already been type checked. *)
Axiom assume_env_wellformed : forall Σ, ∥PT.wf Σ∥.

(* Extract an environment with some minimal checks. This assumes the environment
   is well-formed (to make it computable from within Coq) but furthermore checks that the
   erased context is closed, expanded and that the masks are valid before dearging.
   Suitable for extraction of programs **from within Coq**. *)
Definition extract_within_coq :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     pcuic_args :=
       {| optimize_prop_discr := true;
          transforms := [dearg_transform true true true true true] |} |}.

Definition extract_template_env_within_coq := extract_template_env extract_within_coq.
