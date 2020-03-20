open Ast0
open Datatypes
open Typing0
open Universes0

(** val update_cst_universes :
    ContextSet.t -> constant_body -> constant_body **)

let update_cst_universes univs cb =
  { cst_type = (cst_type cb); cst_body = (cst_body cb); cst_universes =
    (match cst_universes cb with
     | Monomorphic_ctx _ -> Monomorphic_ctx univs
     | Polymorphic_ctx cst -> Polymorphic_ctx cst) }

(** val update_mib_universes :
    ContextSet.t -> mutual_inductive_body -> mutual_inductive_body **)

let update_mib_universes univs mib =
  { ind_finite = (ind_finite mib); ind_npars = (ind_npars mib); ind_params =
    (ind_params mib); ind_bodies = (ind_bodies mib); ind_universes =
    (match ind_universes mib with
     | Monomorphic_ctx _ -> Monomorphic_ctx univs
     | Polymorphic_ctx cst -> Polymorphic_ctx cst); ind_variance =
    (ind_variance mib) }

(** val update_universes : ContextSet.t -> global_decl -> global_decl **)

let update_universes univs = function
| ConstantDecl cb0 -> ConstantDecl (update_cst_universes univs cb0)
| InductiveDecl mib -> InductiveDecl (update_mib_universes univs mib)

(** val is_unbound_level : LevelSet.t -> Level.t -> bool **)

let is_unbound_level declared l = match l with
| Level.Level _ -> negb (LevelSet.mem l declared)
| _ -> false

(** val dangling_universes : LevelSet.t -> ConstraintSet.t -> LevelSet.t **)

let dangling_universes declared cstrs =
  ConstraintSet.fold (fun pat acc ->
    let (p, r) = pat in
    let (l, _) = p in
    let acc0 = if is_unbound_level declared l then LevelSet.add l acc else acc
    in
    if is_unbound_level declared r then LevelSet.add r acc0 else acc0) cstrs
    LevelSet.empty

(** val fold_map_left :
    ('a1 -> 'a2 -> 'a3 * 'a2) -> 'a1 list -> 'a2 -> 'a3 list * 'a2 **)

let rec fold_map_left f l acc =
  match l with
  | [] -> ([], acc)
  | hd :: tl ->
    let (hd', acc0) = f hd acc in
    let (tl', acc') = fold_map_left f tl acc0 in ((hd' :: tl'), acc')

(** val fix_global_env_universes : global_env -> global_env **)

let fix_global_env_universes _UU03a3_ =
  let fix_decl = fun pat declared ->
    let (kn, decl) = pat in
    let (declu, declcstrs) = monomorphic_udecl_decl decl in
    let declared0 = LevelSet.union declu declared in
    let dangling = dangling_universes declared0 declcstrs in
    ((kn,
    (update_universes ((LevelSet.union declu dangling), declcstrs) decl)),
    (LevelSet.union declared0 dangling))
  in
  fst (fold_map_left fix_decl _UU03a3_ LevelSet.empty)

(** val fix_program_universes : program -> program **)

let fix_program_universes = function
| (_UU03a3_, t0) -> ((fix_global_env_universes _UU03a3_), t0)
