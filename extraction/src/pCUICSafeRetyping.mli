open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICLiftSubst
open PCUICSafeChecker
open PCUICTyping
open PCUICUnivSubst
open Specif
open Universes0
open Config0
open Monad_utils

type __ = Obj.t

val type_of_as_sort :
  checker_flags -> global_env_ext -> (context -> term -> __ -> (term, __)
  sigT typing_result) -> context -> term -> Universe.t typing_result

val option_or : 'a1 option -> type_error -> ('a1, __) sigT typing_result

val type_of :
  checker_flags -> global_env_ext -> context -> term -> (term, __) sigT
  typing_result
