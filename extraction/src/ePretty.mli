open BasicAst
open Datatypes
open EAst
open EAstUtils
open ETyping
open List0
open MCString
open Nat0
open String0

val print_def : ('a1 -> char list) -> 'a1 def -> char list

val print_defs :
  (context -> bool -> bool -> term -> char list) -> context_decl list -> term
  mfixpoint -> char list

val lookup_ind_decl :
  global_context -> ident -> nat -> one_inductive_body option

val is_fresh : context -> ident -> bool

val name_from_term : term -> char list

val fresh_id_from : context -> nat -> char list -> char list

val fresh_name : context -> name -> term -> name

val print_term :
  global_context -> context -> bool -> bool -> term -> char list
