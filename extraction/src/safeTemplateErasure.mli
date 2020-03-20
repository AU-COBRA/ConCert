open Ast0
open BasicAst
open Datatypes
open EAst
open EPretty
open ErasureFunction
open List0
open MCString
open PCUICAst
open PCUICAstUtils
open PCUICSafeChecker
open PCUICTyping
open Pretty
open SafeErasureFunction
open SafeTemplateChecker
open Specif
open String0
open TemplateToPCUIC
open Universes0
open Config0
open Monad_utils
open UGraph0

type __ = Obj.t

val erase_template_program_check :
  Ast0.program -> (global_context * EAst.term) coq_EnvCheck

val assume_wf_decl :
  checker_flags -> global_env_ext -> universes_graph -> kername ->
  global_decl -> __ coq_EnvCheck

val check_wf_env_only_univs :
  global_env -> (Coq_wGraph.t, __) sigT coq_EnvCheck

val erase_template_program :
  Ast0.program -> (global_context * EAst.term) coq_EnvCheck

val erase_and_print_template_program_check :
  checker_flags -> Ast0.program -> (char list, char list) sum

val erase_and_print_template_program :
  checker_flags -> Ast0.program -> (char list, char list) sum
