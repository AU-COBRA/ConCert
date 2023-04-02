(** * Almost one-to-one translation of PCUIC to Template Coq kernel AST *)
From Coq Require Import Bool.
From Coq Require Import String.
From Coq Require Import List.
From MetaCoq.Template Require Import All.
From MetaCoq.TemplatePCUIC Require Export PCUICToTemplate.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Module TC := Ast.
Module P := PCUICAst.

Definition aRelevant (n : name) : aname :=
  {| binder_name := n;
     binder_relevance := Relevant |}.

Definition trans_context_decl (c : @BasicAst.context_decl P.term) : TC.Env.context_decl :=
  let t := trans c.(decl_type) in
  match c.(decl_body) with
  | Some x => {| decl_name := c.(decl_name); decl_body := Some (trans x); decl_type := t |}
  | None => {| decl_name := c.(decl_name); decl_body := None; decl_type := t |}
  end.

Definition trans_one_ind_entry (d : P.one_inductive_entry) : TC.one_inductive_entry :=
  {| TC.mind_entry_typename := d.(P.mind_entry_typename);
     TC.mind_entry_arity := trans d.(P.mind_entry_arity);
     TC.mind_entry_consnames := d.(P.mind_entry_consnames);
     TC.mind_entry_lc := map trans d.(P.mind_entry_lc) |}.

Definition trans_universes_decl (ud : universes_decl) : universes_entry :=
  match ud with
  | Monomorphic_ctx => Monomorphic_entry ContextSet.empty
  | Polymorphic_ctx (ln, cst) => Polymorphic_entry (AUContext.repr (ln,cst))
  end.

Definition trans_minductive_entry (e : P.mutual_inductive_entry) : TC.mutual_inductive_entry :=
  {| TC.mind_entry_record := e.(P.mind_entry_record);
     TC.mind_entry_finite := e.(P.mind_entry_finite);
     TC.mind_entry_params := List.map trans_context_decl e.(P.mind_entry_params);
     TC.mind_entry_inds := List.map trans_one_ind_entry e.(P.mind_entry_inds);
     TC.mind_entry_universes := trans_universes_decl e.(P.mind_entry_universes);
     TC.mind_entry_variance := None;
     TC.mind_entry_template := false;
     TC.mind_entry_private := e.(P.mind_entry_private) |}.
