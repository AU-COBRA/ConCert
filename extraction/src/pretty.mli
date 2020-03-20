open Ast0
open AstUtils
open BasicAst
open Datatypes
open LiftSubst
open List0
open MCList
open MCString
open Nat0
open String0
open Universes0

val fix_context : term mfixpoint -> context

val print_defs :
  (context -> bool -> term -> char list) -> context -> term mfixpoint ->
  char list

val is_fresh : context -> ident -> bool

val lookup_env : global_env -> ident -> global_decl option

val lookup_ind_decl :
  global_env_ext -> ident -> nat -> one_inductive_body option

val name_from_term : global_env_ext -> term -> char list

val fresh_id_from : context -> nat -> char list -> char list

val fresh_name : global_env_ext -> context -> name -> term -> name

val print_term : global_env_ext -> context -> bool -> term -> char list
