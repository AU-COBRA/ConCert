open BasicAst
open Datatypes
open EAst
open Extract
open Init
open List0
open PCUICAst
open PCUICAstUtils
open PCUICLiftSubst
open PCUICSafeChecker
open PCUICSafeReduce
open PCUICSafeRetyping
open Specif
open Universes0
open Config0
open Monad_utils

type __ = Obj.t

val is_arity :
  global_env_ext -> PCUICEnvironment.context -> term -> bool typing_result

val is_erasable : global_env_ext -> context -> term -> bool typing_result

val flag_of_type : global_env_ext -> context -> term -> bool typing_result

val is_box : E.term -> bool

val erase_mfix_obligation_1 :
  global_env_ext -> context_decl list -> term BasicAst.mfixpoint -> term
  BasicAst.def -> __ typing_result

val erase_mfix :
  global_env_ext -> (context -> term -> __ -> E.term typing_result) ->
  context_decl list -> term BasicAst.mfixpoint -> E.term mfixpoint
  typing_result

val erase : global_env_ext -> context -> term -> E.term typing_result

val erase_constant_body :
  PCUICEnvironment.global_env_ext -> constant_body -> E.constant_body
  typing_result

val lift_opt_typing : 'a1 option -> type_error -> 'a1 typing_result

val erase_one_inductive_body :
  global_env_ext -> nat -> context -> one_inductive_body ->
  E.one_inductive_body typing_result

val erase_mutual_inductive_body :
  global_env_ext -> mutual_inductive_body -> E.mutual_inductive_body
  typing_result

val erase_global_decls :
  PCUICEnvironment.global_env -> E.global_declarations typing_result

val erase_global :
  PCUICEnvironment.global_env -> E.global_declarations typing_result
