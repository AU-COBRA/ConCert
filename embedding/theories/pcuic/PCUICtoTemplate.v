(** * Almost one-to-one tranlsation of PCUIC to Template Coq kernel AST *)
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import All.
     (* config utils AstUtils BasicAst Ast. *)
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGeneration.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Module TC := Ast.
Module P := PCUICAst.

Fixpoint trans (t : P.term) : TC.term :=
  match t with
  | P.tRel n => TC.tRel n
  | P.tVar n => TC.tVar n
  | P.tEvar ev args => TC.tEvar ev (List.map trans args)
  | P.tSort u => TC.tSort u
  | P.tConst c u => TC.tConst c u
  | P.tInd c u => TC.tInd c u
  | P.tConstruct c k u => TC.tConstruct c k u
  | P.tLambda na T M => TC.tLambda na (trans T) (trans M)
  | P.tApp u v => TC.mkApps (trans u) [trans v]
  | P.tProd na A B => TC.tProd na (trans A) (trans B)
  | P.tLetIn na b t b' => TC.tLetIn na (trans b) (trans t) (trans b')
  | P.tCase ind p c brs =>
    let brs' := List.map (on_snd trans) brs in
    TC.tCase ind (trans p) (trans c) brs'
  | P.tProj p c => TC.tProj p (trans c)
  | P.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    TC.tFix mfix' idx
  | P.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    TC.tCoFix mfix' idx
  end.

Definition trans_decl (d : P.context_decl) :=
  let 'P.mkdecl na b t := d in
  {| TC.decl_name := na;
     TC.decl_body := option_map trans b;
     TC.decl_type := trans t |}.

Definition trans_local Γ := List.map trans_decl Γ.

Definition trans_one_ind_body (d : P.one_inductive_body) :=
  {| TC.ind_name := d.(P.ind_name);
     TC.ind_type := trans d.(P.ind_type);
     TC.ind_kelim := d.(P.ind_kelim);
     TC.ind_ctors := List.map (fun '(x, y, z) => (x, trans y, z)) d.(P.ind_ctors);
     TC.ind_projs := List.map (fun '(x, y) => (x, trans y)) d.(P.ind_projs) |}.

Definition trans_local_entry (nle : ident * P.local_entry) : TC.context_decl :=
  let (nm, le) := nle in
  match le with
  | P.LocalDef ld =>
    (* NOTE: it doesn't seem meaningful to have declarations with
       bodies as parameters, so we produce a dummy value here.
       To produce an actual decalaration with a body we need its type,
       and it's not available it this point*)
    TC.mkdecl (nNamed nm) None (TC.tVar "not supported")
  | P.LocalAssum la =>
    TC.mkdecl (nNamed nm) None (trans la)
  end.

Definition trans_one_ind_entry (d : P.one_inductive_entry) : TC.one_inductive_entry :=
  {| TC.mind_entry_typename := d.(P.mind_entry_typename);
     TC.mind_entry_arity := trans d.(P.mind_entry_arity);
     TC.mind_entry_template := d.(P.mind_entry_template);
     TC.mind_entry_consnames := d.(P.mind_entry_consnames);
     TC.mind_entry_lc := map trans d.(P.mind_entry_lc) |}.

Definition trans_universes_decl (ud : universes_decl) : universes_entry :=
  match ud with
  | Monomorphic_ctx ctx => Monomorphic_entry ctx
  | Polymorphic_ctx (ln, cst) => Polymorphic_entry ln (AUContext.repr (ln,cst))
  end.

Definition trans_minductive_entry (e : P.mutual_inductive_entry) :  TC.mutual_inductive_entry :=
  {| TC.mind_entry_record := e.(P.mind_entry_record);
     TC.mind_entry_finite := e.(P.mind_entry_finite);
     TC.mind_entry_params := List.map trans_local_entry  e.(P.mind_entry_params);
     TC.mind_entry_inds := List.map trans_one_ind_entry e.(P.mind_entry_inds);
     TC.mind_entry_universes := trans_universes_decl e.(P.mind_entry_universes);
     TC.mind_entry_variance := None;
     TC.mind_entry_private := e.(P.mind_entry_private) |}.

Definition trans_constant_body (bd : P.constant_body) : TC.constant_body :=
  {| TC.cst_type := trans bd.(P.cst_type);
     TC.cst_body := option_map trans bd.(P.cst_body);
     TC.cst_universes := bd.(P.cst_universes) |}.

Definition trans_minductive_body md :=
  {| TC.ind_finite := md.(P.ind_finite);
     TC.ind_npars := md.(P.ind_npars);
     TC.ind_params := trans_local md.(P.ind_params);
     TC.ind_bodies := map trans_one_ind_body md.(P.ind_bodies);
     TC.ind_variance := md.(ind_variance);
     TC.ind_universes := md.(P.ind_universes) |}.

Definition trans_global_decl (d : P.global_decl) : TC.global_decl :=
  match d with
  | P.ConstantDecl bd => TC.ConstantDecl (trans_constant_body bd)
  | P.InductiveDecl bd => TC.InductiveDecl (trans_minductive_body bd)
  end.

Definition trans_global_env (d : P.global_env) :=
  List.map (on_snd trans_global_decl) d.

Definition trans_global (Σ : P.global_env_ext) : TC.global_env_ext :=
  (trans_global_env (fst Σ), snd Σ).