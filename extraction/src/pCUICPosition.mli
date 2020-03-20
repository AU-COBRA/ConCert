open BasicAst
open Datatypes
open List0
open MCList
open PCUICAst
open PCUICLiftSubst
open Monad_utils

type stack =
| Empty
| App of term * stack
| Fix of term mfixpoint * nat * term list * stack
| Fix_mfix_ty of name * term * nat * term mfixpoint * term mfixpoint * 
   nat * stack
| Fix_mfix_bd of name * term * nat * term mfixpoint * term mfixpoint * 
   nat * stack
| CoFix of term mfixpoint * nat * term list * stack
| Case_p of (inductive * nat) * term * (nat * term) list * stack
| Case of (inductive * nat) * term * (nat * term) list * stack
| Case_brs of (inductive * nat) * term * term * nat * (nat * term) list
   * (nat * term) list * stack
| Proj of projection * stack
| Prod_l of name * term * stack
| Prod_r of name * term * stack
| Lambda_ty of name * term * stack
| Lambda_tm of name * term * stack
| LetIn_bd of name * term * term * stack
| LetIn_ty of name * term * term * stack
| LetIn_in of name * term * term * stack
| Coq_coApp of term * stack

val zipc : term -> stack -> term

val zip : (term * stack) -> term

val decompose_stack : stack -> term list * stack

val appstack : term list -> stack -> stack

val decompose_stack_at : stack -> nat -> ((term list * term) * stack) option

val fix_context_alt : (name * term) list -> context

val def_sig : term def -> name * term

val stack_context : stack -> context

val stack_cat : stack -> stack -> stack
