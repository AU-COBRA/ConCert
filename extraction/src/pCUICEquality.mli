open All_Forall
open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICReflect
open Universes0

val eqb_term_upto_univ :
  (Universe.t -> Universe.t -> bool) -> (Universe.t -> Universe.t -> bool) ->
  term -> term -> bool
