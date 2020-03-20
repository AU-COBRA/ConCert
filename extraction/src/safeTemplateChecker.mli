open Ast0
open Datatypes
open Typing0
open Universes0

val update_cst_universes : ContextSet.t -> constant_body -> constant_body

val update_mib_universes :
  ContextSet.t -> mutual_inductive_body -> mutual_inductive_body

val update_universes : ContextSet.t -> global_decl -> global_decl

val is_unbound_level : LevelSet.t -> Level.t -> bool

val dangling_universes : LevelSet.t -> ConstraintSet.t -> LevelSet.t

val fold_map_left :
  ('a1 -> 'a2 -> 'a3 * 'a2) -> 'a1 list -> 'a2 -> 'a3 list * 'a2

val fix_global_env_universes : global_env -> global_env

val fix_program_universes : program -> program
