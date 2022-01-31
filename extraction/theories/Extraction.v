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
From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import Certifying.

From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import SafeTemplateChecker.

Local Open Scope bool.
Local Open Scope string.
Import MonadNotation.

Existing Instance extraction_checker_flags.
--
(** We consider a type to be empty, if it is not mutual and has no constructors *)
Definition is_empty_type_decl (d : ExAst.global_decl) : bool :=
  match d with
  | ExAst.ConstantDecl _ => false
  | ExAst.InductiveDecl mib =>
    match mib.(ExAst.ind_bodies) with
    | oib :: _ => match oib.(ExAst.ind_ctors) with [] => true | _ => false end
    | _ => false (* NOTE: this should not happen, the list of bodies should not be empty for a well-formed inductive  *)
    end
  | ExAst.TypeAliasDecl _ => false
  end.

Record extract_pcuic_params :=
  { (* Whether to remove discrimination (matches and projections) on things in Prop.
     Necessary to run the transforms. *)
    optimize_prop_discr : bool;
    (* The transforms to apply after extraction. Only run when optimize_prop_discr is true. *)
    extract_transforms : list ExtractTransform; }.

Definition extract_pcuic_env
           (params : extract_pcuic_params)
           (Σ : P.global_env) (wfΣ : ∥wf Σ∥)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := timed "Erasure" (fun _ => erase_global_decls_deps_recursive Σ wfΣ seeds ignore) in
  if optimize_prop_discr params then
    let Σ := timed "Removal of prop discrimination" (fun _ => OptimizePropDiscr.optimize_env Σ) in
    compose_transforms (extract_transforms params) Σ
  else
    Ok Σ.

Record extract_template_env_params :=
  { (* The transforms to apply at the template coq level, before translating to PCUIC and extracting.
     After performing all the transforms, the pipiline generates proofs that
     the transformed terms are convertible to the originals. *)
    template_transforms : list TemplateTransform;

    (* Function to use to check wellformedness of the environment *)
    check_wf_env_func : forall Σ, result (∥wf Σ∥) string;
    pcuic_args : extract_pcuic_params }.

Definition check_wf_and_extract (params : extract_template_env_params)
           (Σ : global_env) (seeds : KernameSet.t) (ignore : kername -> bool)
  := wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

Definition extract_template_env_general
           (pcuic_trans : PCUICEnvironment.global_env -> result PCUICEnvironment.global_env string)
           (params : extract_template_env_params)
           (Σ : Ast.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := trans_global_decls Σ in
  Σ <- pcuic_trans Σ ;;
  check_wf_and_extract params Σ seeds ignore.

Definition extract_template_env := extract_template_env_general ret.

Definition run_transforms_list (Σ : Ast.global_env) (ts : list TemplateTransform) : TemplateMonad Ast.global_env :=
  res <- tmEval lazy (compose_transforms ts Σ) ;;
  match res with
  | Ok Σ => ret Σ
  | Err s => tmFail s
  end.

Definition run_transforms (Σ : Ast.global_env) (params : extract_template_env_params) : TemplateMonad Ast.global_env :=
  let transforms := params.(template_transforms) in
  run_transforms_list Σ transforms.

Definition extract_template_env_certifying_passes
           (pcuic_trans : PCUICEnvironment.global_env -> result PCUICEnvironment.global_env string)
           (params : extract_template_env_params)
           (Σ : Ast.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : TemplateMonad ExAst.global_env :=
  Σtrans <- run_transforms Σ params ;;
  mpath <- tmCurrentModPath tt;;
  gen_defs_and_proofs Σ Σtrans mpath "_cert_pass" seeds;;
  res <- tmEval lazy (extract_template_env_general pcuic_trans params  Σtrans seeds ignore) ;;
  match res with
    | Ok env => ret env
    | Err e => tmFail e
  end.

(* MetaCoq's safe checker does not run from within Coq, only when extracting.
   To work around this we assume environments are well formed when extracting
   from within Coq. This is justified since our environments are produced by quoting
   and thus come directly from Coq, where they have already been type checked. *)
Axiom assume_env_wellformed : forall Σ, ∥wf Σ∥.

(* Extract an environment with some minimal checks. This assumes the environment
   is well-formed (to make it computable from within Coq) but furthermore checks that the
   erased context is closed, expanded and that the masks are valid before dearging.
   Suitable for extraction of programs **from within Coq**. *)
Definition extract_within_coq : extract_template_env_params :=
  {| template_transforms := [];
     check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true true true true] |} |}.

Definition extract_template_env_within_coq := extract_template_env extract_within_coq.

(* returns a list of constructor names and the name of the inductive associated *)
Definition get_projections (env : ExAst.global_env) : list (ident * ExAst.one_inductive_body) :=
  let get_projs (d : ExAst.global_decl) : list (ident * ExAst.one_inductive_body) :=
    match d with
    | ExAst.InductiveDecl mind => 
      (* We assume no mutually inductive definitions *)
      match mind.(ExAst.ind_bodies) with
      (* pair every constructor with the inductive's name *)
      | [oib] => 
        match oib.(ExAst.ind_ctors), oib.(ExAst.ind_projs) with
        (* case 1-ind with primitive projections *)
        | [ctor],_::_ => map (fun '(na, _) => (na, oib)) oib.(ExAst.ind_projs)
        (*case 1-ind without primitive projections *)
        | [(_,ctor_args)],[] => 
          (* let is_named '(nm,_) := match nm with nNamed _ => true | _ => false end in *)
          (* let named_args := filter is_named ctor_args in *)
          map (fun '(na, _) =>(string_of_name na, oib)) ctor_args
        | _,_ => []
        end
      | _ => []
      end
    | _ => []
    end in
  List.concat (List.map (fun p => get_projs p.2) env).
