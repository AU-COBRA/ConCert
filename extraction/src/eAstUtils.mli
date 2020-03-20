open BasicAst
open Datatypes
open EAst
open MCString
open String0

val decompose_app_rec : term -> term list -> term * term list

val decompose_app : term -> term * term list

val string_of_def : ('a1 -> char list) -> 'a1 def -> char list

val string_of_term : term -> char list
