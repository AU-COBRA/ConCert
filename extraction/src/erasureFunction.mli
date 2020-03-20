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
open PCUICTyping
open Specif
open Universes0
open Config0
open Monad_utils

type __ = Obj.t

val normal_dec : global_env_ext -> context -> term -> __ typing_result

val reduce_to_sort' :
  global_env_ext -> context -> term -> ((Universe.t, __) sigT, __) sum
  typing_result

val reduce_to_prod' :
  global_env_ext -> context -> term -> ((name, (term, (term, __) sigT) sigT)
  sigT, __) sum typing_result

val is_arity :
  global_env_ext -> PCUICEnvironment.context -> term -> bool typing_result

val is_erasable : global_env_ext -> context -> term -> bool typing_result

val flag_of_type : global_env_ext -> context -> term -> bool typing_result

val erase_mfix_obligation_1 :
  global_env_ext -> PCUICEnvironment.context -> term BasicAst.mfixpoint -> __
  typing_result

val erase_mfix :
  global_env_ext -> (context -> __ -> term -> E.term typing_result) ->
  PCUICEnvironment.context -> term BasicAst.mfixpoint -> E.term mfixpoint
  typing_result

val erase : global_env_ext -> context -> term -> E.term typing_result

val optM : 'a1 coq_Monad -> 'a2 option -> ('a2 -> 'a1) -> 'a1

val erase_constant_body :
  global_env_ext -> constant_body -> E.constant_body typing_result

val lift_opt_typing : 'a1 option -> type_error -> 'a1 typing_result

val erase_one_inductive_body :
  global_env_ext -> nat -> context -> one_inductive_body ->
  E.one_inductive_body typing_result

val erase_mutual_inductive_body :
  PCUICEnvironment.global_env_ext -> mutual_inductive_body ->
  E.mutual_inductive_body typing_result

val erase_global_decls :
  PCUICEnvironment.global_env -> E.global_declarations typing_result

val erase_global :
  PCUICEnvironment.global_env -> E.global_declarations typing_result
