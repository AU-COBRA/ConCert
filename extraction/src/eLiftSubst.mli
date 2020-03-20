open Datatypes
open EAst
open List0
open MCProd
open Nat0

val lift : nat -> nat -> term -> term

val up : term -> term

val subst : term list -> nat -> term -> term

val subst1 : term -> nat -> term -> term

val closedn : nat -> term -> bool
