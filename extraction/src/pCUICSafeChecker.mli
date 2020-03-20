open All_Forall
open BasicAst
open Datatypes
open EqDecInstances
open List0
open MCOption
open MCString
open PCUICAst
open PCUICAstUtils
open PCUICCumulativity
open PCUICLiftSubst
open PCUICNormal
open PCUICPosition
open PCUICPretty
open PCUICReflect
open PCUICSafeConversion
open PCUICSafeReduce
open PCUICTyping
open PCUICUnivSubst
open PeanoNat
open Specif
open String0
open Universes0
open Config0
open Monad_utils
open UGraph0

type __ = Obj.t

val check_dec :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> 'a2 -> bool -> 'a1

val check_eq_true :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> bool -> 'a2 -> 'a1

val check_eq_nat :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> nat -> nat -> 'a2 -> 'a1

type type_error =
| UnboundRel of nat
| UnboundVar of char list
| UnboundEvar of nat
| UndeclaredConstant of char list
| UndeclaredInductive of inductive
| UndeclaredConstructor of inductive * nat
| NotCumulSmaller of universes_graph * context * term * term * term * 
   term * coq_ConversionError
| NotConvertible of universes_graph * context * term * term
| NotASort of term
| NotAProduct of term * term
| NotAnInductive of term
| IllFormedFix of term mfixpoint * nat
| UnsatisfiedConstraints of ConstraintSet.t
| Msg of char list

val print_no_prop_level : NoPropLevel.t -> char list

val print_edge : ((NoPropLevel.t * nat) * NoPropLevel.t) -> char list

val print_universes_graph : universes_graph -> char list

val string_of_conv_pb : conv_pb -> char list

val print_term : global_env_ext -> context -> term -> char list

val string_of_conv_error : global_env_ext -> coq_ConversionError -> char list

val string_of_type_error : global_env_ext -> type_error -> char list

type 'a typing_result =
| Checked of 'a
| TypeError of type_error

val typing_monad : __ typing_result coq_Monad

val monad_exc : (type_error, __ typing_result) coq_MonadExc

val wf_ext_gc_of_uctx :
  checker_flags -> global_env_ext ->
  (Coq_wGraph.VSet.t * GoodConstraintSet.t, __) sigT

val wf_ext_is_graph :
  checker_flags -> global_env_ext -> (Coq_wGraph.t, __) sigT

val hnf : checker_flags -> global_env_ext -> context -> term -> term

val reduce_to_sort :
  checker_flags -> global_env_ext -> context -> term -> (Universe.t, __) sigT
  typing_result

val reduce_to_prod :
  checker_flags -> global_env_ext -> context -> term -> (name, (term, (term,
  __) sigT) sigT) sigT typing_result

val stack_to_apps : stack -> term list typing_result

val reduce_to_ind :
  checker_flags -> global_env_ext -> context -> term -> (inductive,
  (Instance.t, (term list, __) sigT) sigT) sigT typing_result

val iscumul :
  checker_flags -> global_env_ext -> universes_graph -> context -> term ->
  term -> coq_ConversionResult

val convert_leq :
  checker_flags -> global_env_ext -> universes_graph -> context -> term ->
  term -> __ typing_result

val infer_type :
  checker_flags -> global_env_ext -> (PCUICEnvironment.context -> __ -> term
  -> (term, __) sigT typing_result) -> context -> term -> (Universe.t, __)
  sigT typing_result

val infer_cumul :
  checker_flags -> global_env_ext -> universes_graph ->
  (PCUICEnvironment.context -> __ -> term -> (term, __) sigT typing_result)
  -> context -> term -> term -> __ typing_result

val lookup_ind_decl :
  global_env_ext -> inductive -> (PCUICEnvironment.mutual_inductive_body,
  (PCUICEnvironment.one_inductive_body, __) sigT) sigT typing_result

val check_consistent_instance :
  checker_flags -> global_env_ext -> universes_graph -> universes_decl ->
  Instance.t -> __ typing_result

val infer :
  checker_flags -> global_env_ext -> universes_graph -> context -> term ->
  (term, __) sigT typing_result

val check_context :
  checker_flags -> global_env_ext -> universes_graph ->
  PCUICEnvironment.context -> __ typing_result

val check_isType :
  checker_flags -> global_env_ext -> universes_graph ->
  PCUICEnvironment.context -> PCUICTerm.term -> __ typing_result

val check_isWAT :
  checker_flags -> global_env_ext -> universes_graph ->
  PCUICEnvironment.context -> term -> __ typing_result

val check :
  checker_flags -> global_env_ext -> universes_graph ->
  PCUICEnvironment.context -> term -> term -> __ typing_result

val infer' :
  checker_flags -> PCUICEnvironment.global_env_ext -> universes_graph ->
  context -> term -> (term, __) sigT typing_result

val make_graph_and_infer :
  checker_flags -> PCUICEnvironment.global_env_ext -> context -> term ->
  (term, __) sigT typing_result

type env_error =
| IllFormedDecl of char list * type_error
| AlreadyDeclared of char list

type 'a coq_EnvCheck =
| CorrectDecl of 'a
| EnvError of global_env_ext * env_error

val envcheck_monad : __ coq_EnvCheck coq_Monad

val envcheck_monad_exc :
  (global_env_ext * env_error, __ coq_EnvCheck) coq_MonadExc

val wrap_error :
  global_env_ext -> char list -> 'a1 typing_result -> 'a1 coq_EnvCheck

val check_wf_type :
  checker_flags -> char list -> global_env_ext -> universes_graph -> term ->
  (Universe.t, __) sigT coq_EnvCheck

val check_wf_judgement :
  checker_flags -> char list -> global_env_ext -> universes_graph -> term ->
  term -> __ coq_EnvCheck

val check_fresh : char list -> PCUICEnvironment.global_env -> __ coq_EnvCheck

val coq_VariableLevel_get_noprop : NoPropLevel.t -> VariableLevel.t option

val add_uctx :
  (Coq_wGraph.VSet.t * GoodConstraintSet.t) -> universes_graph ->
  universes_graph

val monad_Alli :
  'a1 coq_Monad -> (nat -> 'a2 -> 'a1) -> 'a2 list -> nat -> 'a1

val check_one_ind_body :
  checker_flags -> global_env_ext -> universes_graph -> kername ->
  mutual_inductive_body -> nat -> one_inductive_body -> __ coq_EnvCheck

val check_wf_decl :
  checker_flags -> global_env_ext -> universes_graph -> kername ->
  global_decl -> __ coq_EnvCheck

val uctx_of_udecl : universes_decl -> ContextSet.t

val check_udecl :
  checker_flags -> char list -> global_env -> Coq_wGraph.t -> universes_decl
  -> (Coq_wGraph.VSet.t * GoodConstraintSet.t, __) sigT coq_EnvCheck

val check_wf_env :
  checker_flags -> global_env -> (Coq_wGraph.t, __) sigT coq_EnvCheck
