open BasicAst
open Datatypes
open MCString
open PCUICAst
open String0
open Universes0

val string_of_term : term -> char list

val decompose_app_rec : term -> term list -> term * term list

val decompose_app : term -> term * term list

val decompose_prod_assum : context -> term -> context * term

val decompose_prod_n_assum : context -> nat -> term -> (context * term) option
