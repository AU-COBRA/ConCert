open BasicAst
open Datatypes
open List0
open MCList
open MCProd
open Nat0
open PCUICAst
open PeanoNat

val lift : nat -> nat -> term -> term

val subst : term list -> nat -> term -> term

val subst1 : term -> nat -> term -> term

val fix_context : term mfixpoint -> context
