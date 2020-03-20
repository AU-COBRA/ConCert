open Ast0
open BasicAst
open Datatypes
open List0
open MCProd
open Universes0

(** val subst_instance_constr : term coq_UnivSubst **)

let rec subst_instance_constr u c = match c with
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst_instance_constr u) args))
| Coq_tSort s -> Coq_tSort (subst_instance_univ u s)
| Coq_tCast (c0, kind, ty) ->
  Coq_tCast ((subst_instance_constr u c0), kind, (subst_instance_constr u ty))
| Coq_tProd (na, a, b) ->
  Coq_tProd (na, (subst_instance_constr u a), (subst_instance_constr u b))
| Coq_tLambda (na, t, m) ->
  Coq_tLambda (na, (subst_instance_constr u t), (subst_instance_constr u m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst_instance_constr u b), (subst_instance_constr u ty),
    (subst_instance_constr u b'))
| Coq_tApp (f, v) ->
  Coq_tApp ((subst_instance_constr u f), (map (subst_instance_constr u) v))
| Coq_tConst (c0, u') -> Coq_tConst (c0, (subst_instance_instance u u'))
| Coq_tInd (i, u') -> Coq_tInd (i, (subst_instance_instance u u'))
| Coq_tConstruct (ind, k, u') ->
  Coq_tConstruct (ind, k, (subst_instance_instance u u'))
| Coq_tCase (ind, p, c0, brs) ->
  let brs' = map (on_snd (subst_instance_constr u)) brs in
  Coq_tCase (ind, (subst_instance_constr u p), (subst_instance_constr u c0),
  brs')
| Coq_tProj (p, c0) -> Coq_tProj (p, (subst_instance_constr u c0))
| Coq_tFix (mfix, idx) ->
  let mfix' =
    map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix
  in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' =
    map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix
  in
  Coq_tCoFix (mfix', idx)
| _ -> c

(** val subst_instance_decl : context_decl coq_UnivSubst **)

let subst_instance_decl x =
  map_decl (subst_instance_constr x)

(** val subst_instance_context : context coq_UnivSubst **)

let subst_instance_context x =
  map_context (subst_instance_constr x)

(** val closedu : nat -> term -> bool **)

let rec closedu k = function
| Coq_tEvar (_, args) -> forallb (closedu k) args
| Coq_tSort univ -> closedu_universe k univ
| Coq_tCast (c, _, t0) -> (&&) (closedu k c) (closedu k t0)
| Coq_tProd (_, t0, m) -> (&&) (closedu k t0) (closedu k m)
| Coq_tLambda (_, t0, m) -> (&&) (closedu k t0) (closedu k m)
| Coq_tLetIn (_, b, t0, b') ->
  (&&) ((&&) (closedu k b) (closedu k t0)) (closedu k b')
| Coq_tApp (u, v) -> (&&) (closedu k u) (forallb (closedu k) v)
| Coq_tConst (_, u) -> closedu_instance k u
| Coq_tInd (_, u) -> closedu_instance k u
| Coq_tConstruct (_, _, u) -> closedu_instance k u
| Coq_tCase (_, p, c, brs) ->
  let brs' = forallb (test_snd (closedu k)) brs in
  (&&) ((&&) (closedu k p) (closedu k c)) brs'
| Coq_tProj (_, c) -> closedu k c
| Coq_tFix (mfix, _) -> forallb (test_def (closedu k) (closedu k)) mfix
| Coq_tCoFix (mfix, _) -> forallb (test_def (closedu k) (closedu k)) mfix
| _ -> true
