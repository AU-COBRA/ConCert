(** * Almost one-to-one tranlsation of PCUIC to Template Coq kernel AST *)
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils BasicAst Ast.
From MetaCoq.Checker Require Import WfInv Typing Weakening TypingWf.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICGeneration.
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
  let 'P.Build_context_decl na b t := d in
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

Definition trans_local_entry (le : P.local_entry) :=
  match le with
  | P.LocalDef ld => TC.LocalDef (trans ld)
  | P.LocalAssum la => TC.LocalAssum (trans la)
  end.

Definition trans_one_ind_entry (d : P.one_inductive_entry) : TC.one_inductive_entry :=
  {| TC.mind_entry_typename := d.(P.mind_entry_typename);
     TC.mind_entry_arity := trans d.(P.mind_entry_arity);
     TC.mind_entry_template := d.(P.mind_entry_template);
     TC.mind_entry_consnames := d.(P.mind_entry_consnames);
     TC.mind_entry_lc := map trans d.(P.mind_entry_lc) |}.

Definition trans_minductive_entry (e : P.mutual_inductive_entry) :  TC.mutual_inductive_entry :=
  {| TC.mind_entry_record := e.(P.mind_entry_record);
     TC.mind_entry_finite := e.(P.mind_entry_finite);
     TC.mind_entry_params := List.map (fun '(x, y) => (x, trans_local_entry y)) e.(P.mind_entry_params);
     TC.mind_entry_inds := List.map trans_one_ind_entry e.(P.mind_entry_inds);
     TC.mind_entry_universes := e.(P.mind_entry_universes);
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
     TC.ind_universes := md.(P.ind_universes) |}.

Definition trans_global_decl (d : P.global_decl) : TC.global_decl :=
  match d with
  | P.ConstantDecl kn bd => TC.ConstantDecl kn (trans_constant_body bd)
  | P.InductiveDecl kn bd => TC.InductiveDecl kn (trans_minductive_body bd)
  end.

Definition trans_global_decls d :=
  List.map trans_global_decl d.

Definition trans_global (Σ : P.global_env_ext) :=
  (trans_global_decls (fst Σ), snd Σ).