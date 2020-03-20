open BasicAst
open Datatypes
open List0
open MCString
open Nat0
open PCUICAst
open PCUICAstUtils
open PCUICChecker
open PCUICLiftSubst
open String0
open Universes0

val print_defs :
  (context -> bool -> bool -> term -> char list) -> context -> term mfixpoint
  -> char list

val is_fresh : context -> ident -> bool

val name_from_term : global_env_ext -> term -> char list

val fresh_id_from : context -> nat -> char list -> char list

val fresh_name : global_env_ext -> context -> name -> term -> name

val print_term :
  global_env_ext -> context -> bool -> bool -> term -> char list
