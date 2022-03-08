(** * Almost one-to-one tranlsation of PCUIC to Template Coq kernel AST *)
From Coq Require Import Bool.
From Coq Require Import String.
From Coq Require Import List.
From MetaCoq.Template Require Import All.
     (* config utils AstUtils BasicAst Ast. *)
From MetaCoq.PCUIC Require Export PCUICToTemplate.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Module TC := Ast.
Module P := PCUICAst.

Definition aRelevant (n : name) : aname :=
  {| binder_name := n;
     binder_relevance := Relevant |}.

Definition trans_local_entry (nle : ident * P.local_entry) : TC.context_decl :=
  let (nm, le) := nle in
  match le with
  | P.LocalDef ld =>
    (* NOTE: it doesn't seem meaningful to have declarations with
       bodies as parameters, so we produce a dummy value here.
       To produce an actual decalaration with a body we need its type,
       and it's not available it this point*)
    TC.mkdecl (aRelevant (nNamed nm)) None (TC.tVar "not supported")
  | P.LocalAssum la =>
    TC.mkdecl (aRelevant (nNamed nm)) None (trans la)
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
