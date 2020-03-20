open All_Forall
open BasicAst
open Classes0
open Datatypes
open EqdepFacts
open List0
open Nat0
open PCUICAst
open PCUICCumulativity
open PCUICEquality
open PCUICNormal
open PCUICPosition
open PCUICReflect
open PCUICSafeLemmata
open PCUICSafeReduce
open PCUICTyping
open PCUICUnivSubst
open Universes0
open Config0
open UGraph0

type __ = Obj.t

type state =
| Reduction
| Term
| Args
| Fallback

type pack = { st : state; tm1 : term; stk1 : stack; tm2 : term; stk2 : stack }

val leqb_term : checker_flags -> universes_graph -> term -> term -> bool

val eqb_term : checker_flags -> universes_graph -> term -> term -> bool

type coq_ConversionError =
| NotFoundConstants of kername * kername
| NotFoundConstant of kername
| LambdaNotConvertibleTypes of context * name * term * term * context * 
   name * term * term * coq_ConversionError
| ProdNotConvertibleDomains of context * name * term * term * context * 
   name * term * term * coq_ConversionError
| CaseOnDifferentInd of context * inductive * nat * term * term
   * (nat * term) list * context * inductive * nat * term * term
   * (nat * term) list
| CaseBranchNumMismatch of inductive * nat * context * term * term
   * (nat * term) list * nat * term * (nat * term) list * context * term
   * term * (nat * term) list * nat * term * (nat * term) list
| DistinctStuckProj of context * projection * term * context * projection
   * term
| CannotUnfoldFix of context * term mfixpoint * nat * context
   * term mfixpoint * nat
| FixRargMismatch of nat * context * term def * term mfixpoint
   * term mfixpoint * context * term def * term mfixpoint * term mfixpoint
| FixMfixMismatch of nat * context * term mfixpoint * context * term mfixpoint
| DistinctCoFix of context * term mfixpoint * nat * context * term mfixpoint
   * nat
| StackHeadError of conv_pb * context * term * term list * term * term list
   * context * term * term * term list * coq_ConversionError
| StackTailError of conv_pb * context * term * term list * term * term list
   * context * term * term * term list * coq_ConversionError
| StackMismatch of context * term * term list * term list * context * 
   term * term list
| HeadMistmatch of conv_pb * context * term * context * term

type coq_ConversionResult =
| Success
| Error of coq_ConversionError

type coq_Ret = conv_pb -> __ -> __ -> __ -> __ -> coq_ConversionResult

type coq_Aux =
  state -> term -> stack -> term -> stack -> __ -> __ -> __ -> __ -> coq_Ret

val _isconv_red :
  checker_flags -> global_env_ext -> context -> conv_pb -> term -> stack ->
  term -> stack -> coq_Aux -> coq_ConversionResult

val unfold_one_fix :
  checker_flags -> global_env_ext -> context -> term mfixpoint -> nat ->
  stack -> (term * stack) option

type prog_view =
| Coq_prog_view_App of term * term * term * term
| Coq_prog_view_Const of kername * Instance.t * kername * Instance.t
| Coq_prog_view_Lambda of name * term * term * name * term * term
| Coq_prog_view_Prod of name * term * term * name * term * term
| Coq_prog_view_Case of inductive * nat * term * term * (nat * term) list
   * inductive * nat * term * term * (nat * term) list
| Coq_prog_view_Proj of projection * term * projection * term
| Coq_prog_view_Fix of term mfixpoint * nat * term mfixpoint * nat
| Coq_prog_view_CoFix of term mfixpoint * nat * term mfixpoint * nat
| Coq_prog_view_other of term * term

val prog_viewc : term -> term -> prog_view

val unfold_constants :
  checker_flags -> global_env_ext -> context -> conv_pb -> kername ->
  Instance.t -> stack -> kername -> Instance.t -> stack -> coq_Aux ->
  coq_ConversionResult

val eqb_universe_instance :
  checker_flags -> universes_graph -> Level.t list -> Level.t list -> bool

val isconv_branches_obligations_obligation_12 :
  checker_flags -> global_env_ext -> nat -> nat -> context -> inductive ->
  nat -> term -> term -> (nat * term) list -> term -> (nat * term) list ->
  stack -> term -> term -> (nat * term) list -> term -> (nat * term) list ->
  stack -> coq_Aux -> state -> term -> stack -> term -> stack -> conv_pb ->
  coq_ConversionResult

val isconv_branches :
  checker_flags -> global_env_ext -> context -> inductive -> nat -> term ->
  term -> (nat * term) list -> (nat * term) list -> stack -> term -> term ->
  (nat * term) list -> (nat * term) list -> stack -> coq_Aux ->
  coq_ConversionResult

val isconv_branches'_obligations_obligation_5 :
  checker_flags -> global_env_ext -> context -> inductive -> nat -> term ->
  term -> (nat * term) list -> stack -> inductive -> nat -> term -> term ->
  (nat * term) list -> stack -> coq_Aux -> state -> term -> stack -> term ->
  stack -> conv_pb -> coq_ConversionResult

val isconv_branches' :
  checker_flags -> global_env_ext -> context -> inductive -> nat -> term ->
  term -> (nat * term) list -> stack -> inductive -> nat -> term -> term ->
  (nat * term) list -> stack -> coq_Aux -> coq_ConversionResult

val isconv_fix_types_obligations_obligation_10 :
  checker_flags -> global_env_ext -> term def -> term def -> context -> nat
  -> term mfixpoint -> term def list -> stack -> term mfixpoint -> term def
  list -> stack -> coq_Aux -> state -> term -> stack -> term -> stack ->
  conv_pb -> coq_ConversionResult

val isconv_fix_types :
  checker_flags -> global_env_ext -> context -> nat -> term mfixpoint -> term
  mfixpoint -> stack -> term mfixpoint -> term mfixpoint -> stack -> coq_Aux
  -> coq_ConversionResult

val isconv_fix_bodies_obligations_obligation_13 :
  checker_flags -> global_env_ext -> context -> nat -> term mfixpoint -> term
  def -> term def list -> stack -> term mfixpoint -> term def -> term def
  list -> stack -> coq_Aux -> state -> term -> stack -> term -> stack ->
  conv_pb -> coq_ConversionResult

val isconv_fix_bodies :
  checker_flags -> global_env_ext -> context -> nat -> term mfixpoint -> term
  mfixpoint -> stack -> term mfixpoint -> term mfixpoint -> stack -> coq_Aux
  -> coq_ConversionResult

val isconv_fix_obligations_obligation_4 :
  checker_flags -> global_env_ext -> context -> term mfixpoint -> nat ->
  stack -> term mfixpoint -> nat -> stack -> coq_Aux -> state -> term ->
  stack -> term -> stack -> conv_pb -> coq_ConversionResult

val isconv_fix_obligations_obligation_9 :
  checker_flags -> global_env_ext -> context -> term mfixpoint -> nat ->
  stack -> term mfixpoint -> nat -> stack -> coq_Aux -> state -> term ->
  stack -> term -> stack -> conv_pb -> coq_ConversionResult

val isconv_fix :
  checker_flags -> global_env_ext -> context -> term mfixpoint -> nat ->
  stack -> term mfixpoint -> nat -> stack -> coq_Aux -> coq_ConversionResult

val _isconv_prog :
  checker_flags -> global_env_ext -> universes_graph -> context -> conv_pb ->
  term -> stack -> term -> stack -> coq_Aux -> coq_ConversionResult

type coq_Aux' =
  term -> term -> term list -> term list -> stack -> __ -> __ -> __ -> __ ->
  coq_Ret

val _isconv_args'_obligations_obligation_13 :
  checker_flags -> global_env_ext -> context -> term -> term list -> term ->
  term list -> stack -> term -> term -> term list -> stack -> coq_Aux' ->
  term -> term -> term list -> term list -> stack -> conv_pb ->
  coq_ConversionResult

val _isconv_args' :
  checker_flags -> global_env_ext -> conv_pb -> context -> term -> term list
  -> term list -> stack -> term -> term list -> stack -> coq_Aux' ->
  coq_ConversionResult

val _isconv_args_obligations_obligation_7 :
  checker_flags -> global_env_ext -> stack -> term list -> stack -> stack ->
  term list -> stack -> conv_pb -> context -> term -> term -> coq_Aux -> term
  -> term -> term list -> term list -> stack -> conv_pb ->
  coq_ConversionResult

val _isconv_args :
  checker_flags -> global_env_ext -> conv_pb -> context -> term -> stack ->
  term -> stack -> coq_Aux -> coq_ConversionResult

val unfold_one_case :
  checker_flags -> global_env_ext -> context -> inductive -> nat -> term ->
  term -> (nat * term) list -> term option

val unfold_one_proj :
  checker_flags -> global_env_ext -> context -> projection -> term -> term
  option

val reducible_head :
  checker_flags -> global_env_ext -> context -> term -> stack ->
  (term * stack) option

val _isconv_fallback :
  checker_flags -> RedFlags.t -> global_env_ext -> universes_graph -> context
  -> conv_pb -> term -> stack -> term -> stack -> coq_Aux ->
  coq_ConversionResult

val _isconv :
  checker_flags -> RedFlags.t -> global_env_ext -> universes_graph -> state
  -> context -> term -> stack -> term -> stack -> coq_Aux -> conv_pb ->
  coq_ConversionResult

val isconv_full_obligations_obligation_1 :
  checker_flags -> RedFlags.t -> global_env_ext -> universes_graph -> context
  -> term -> stack -> pack -> (pack -> __ -> __ -> __ -> coq_Ret) -> conv_pb
  -> coq_ConversionResult

val isconv_full :
  checker_flags -> RedFlags.t -> global_env_ext -> universes_graph -> state
  -> context -> term -> stack -> term -> stack -> conv_pb ->
  coq_ConversionResult

val isconv :
  checker_flags -> RedFlags.t -> global_env_ext -> universes_graph -> context
  -> conv_pb -> term -> stack -> term -> stack -> coq_ConversionResult

val isconv_term :
  checker_flags -> RedFlags.t -> global_env_ext -> universes_graph -> context
  -> conv_pb -> term -> term -> coq_ConversionResult
