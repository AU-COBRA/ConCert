open BasicAst
open Datatypes
open EAst
open EAstUtils
open ELiftSubst
open List0

val lookup_env : global_declarations -> ident -> global_decl option

val fix_subst : term mfixpoint -> term list

val unfold_fix : term mfixpoint -> nat -> (nat * term) option

val cofix_subst : term mfixpoint -> term list

val unfold_cofix : term mfixpoint -> nat -> (nat * term) option

val is_constructor : nat -> term list -> bool

val is_constructor_or_box : nat -> term list -> bool

val tDummy : term

val iota_red : nat -> nat -> term list -> (nat * term) list -> term
