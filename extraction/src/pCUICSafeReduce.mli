open BasicAst
open Datatypes
open List0
open Nat0
open PCUICAst
open PCUICLiftSubst
open PCUICNormal
open PCUICPosition
open PCUICTyping
open PCUICUnivSubst
open Universes0
open Config0

type __ = Obj.t

val inspect : 'a1 -> 'a1

type construct_view =
| Coq_view_construct of inductive * nat * Instance.t
| Coq_view_other of term

val construct_viewc : term -> construct_view

type red_view =
| Coq_red_view_Rel of nat * stack
| Coq_red_view_LetIn of name * term * term * term * stack
| Coq_red_view_Const of kername * Instance.t * stack
| Coq_red_view_App of term * term * stack
| Coq_red_view_Lambda of name * term * term * term * stack
| Coq_red_view_Fix of term mfixpoint * nat * stack
| Coq_red_view_Case of inductive * nat * term * term * (nat * term) list
   * stack
| Coq_red_view_Proj of projection * term * stack
| Coq_red_view_other of term * stack

val red_viewc : term -> stack -> red_view

type construct_cofix_view =
| Coq_ccview_construct of inductive * nat * Instance.t
| Coq_ccview_cofix of term mfixpoint * nat
| Coq_ccview_other of term

val cc_viewc : term -> construct_cofix_view

val _reduce_stack :
  checker_flags -> RedFlags.t -> global_env_ext -> context -> term -> stack
  -> (term -> stack -> __ -> (term * stack)) -> (term * stack)

val reduce_stack_full_obligations_obligation_1 :
  checker_flags -> RedFlags.t -> global_env_ext -> context -> (term * stack)
  -> ((term * stack) -> __ -> __ -> (term * stack)) -> (term * stack)

val reduce_stack_full :
  checker_flags -> RedFlags.t -> global_env_ext -> context -> term -> stack
  -> (term * stack)

val reduce_stack :
  checker_flags -> RedFlags.t -> global_env_ext -> context -> term -> stack
  -> term * stack

val reduce_term :
  checker_flags -> RedFlags.t -> global_env_ext -> context -> term -> term
