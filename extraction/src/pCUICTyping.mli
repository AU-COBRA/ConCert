open BasicAst
open Datatypes
open List0
open MCList
open PCUICAst
open PCUICAstUtils
open PCUICLiftSubst
open PCUICUnivSubst
open Universes0
open Monad_utils

val lookup_env :
  PCUICEnvironment.global_env -> ident -> PCUICEnvironment.global_decl option

val on_udecl_decl :
  (universes_decl -> 'a1) -> PCUICEnvironment.global_decl -> 'a1

val monomorphic_udecl_decl : PCUICEnvironment.global_decl -> ContextSet.t

val monomorphic_levels_decl : PCUICEnvironment.global_decl -> LevelSet.t

val monomorphic_constraints_decl :
  PCUICEnvironment.global_decl -> ConstraintSet.t

val universes_decl_of_decl : PCUICEnvironment.global_decl -> universes_decl

val global_levels : PCUICEnvironment.global_env -> LevelSet.t

val global_constraints : PCUICEnvironment.global_env -> ConstraintSet.t

val global_ext_levels : PCUICEnvironment.global_env_ext -> LevelSet.t

val global_ext_constraints :
  PCUICEnvironment.global_env_ext -> ConstraintSet.t

val inds : kername -> Instance.t -> one_inductive_body list -> term list

val type_of_constructor :
  mutual_inductive_body -> ((ident * term) * nat) -> (inductive * nat) ->
  Level.t list -> term

val fix_subst : term mfixpoint -> term list

val unfold_fix : term mfixpoint -> nat -> (nat * term) option

val cofix_subst : term mfixpoint -> term list

val unfold_cofix : term mfixpoint -> nat -> (nat * term) option

val tDummy : term

val iota_red : nat -> nat -> term list -> (nat * term) list -> term

val destArity :
  context_decl list -> term -> (context_decl list * Universe.t) option

val fix_guard : term mfixpoint -> bool

val ind_guard : mutual_inductive_body -> bool

val instantiate_params_subst :
  context_decl list -> term list -> term list -> term -> (term list * term)
  option

val instantiate_params : context -> term list -> term -> term option

val build_branches_type :
  inductive -> mutual_inductive_body -> one_inductive_body -> term list ->
  Instance.t -> term -> (nat * term) option list

val build_case_predicate_type :
  inductive -> mutual_inductive_body -> one_inductive_body -> term list ->
  Instance.t -> Universe.t -> term option
