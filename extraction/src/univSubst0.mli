open Ast0
open BasicAst
open Datatypes
open List0
open MCProd
open Universes0

val subst_instance_constr : term coq_UnivSubst

val subst_instance_decl : context_decl coq_UnivSubst

val subst_instance_context : context coq_UnivSubst

val closedu : nat -> term -> bool
