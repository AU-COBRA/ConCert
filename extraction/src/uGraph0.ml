open Bool
open Datatypes
open List0
open MSetWeakList
open Nat0
open PeanoNat
open Specif
open String0
open Universes0
open Config0
open Monad_utils
open WGraph

type __ = Obj.t

module VariableLevel =
 struct
  type t =
  | Level of char list
  | Var of nat

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match x with
    | Level s0 -> (match y with
                   | Level s' -> string_dec s0 s'
                   | Var _ -> false)
    | Var n -> (match y with
                | Level _ -> false
                | Var n' -> Nat.eq_dec n n')

  (** val to_noprop : t -> NoPropLevel.t **)

  let to_noprop = function
  | Level s0 -> NoPropLevel.Level s0
  | Var n -> NoPropLevel.Var n
 end

module GoodConstraint =
 struct
  type t_ =
  | Coq_gc_le of VariableLevel.t * VariableLevel.t
  | Coq_gc_lt of VariableLevel.t * VariableLevel.t
  | Coq_gc_lt_set of nat
  | Coq_gc_eq_set of nat

  (** val t__rect :
      (VariableLevel.t -> VariableLevel.t -> 'a1) -> (VariableLevel.t ->
      VariableLevel.t -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rect f f0 f1 f2 = function
  | Coq_gc_le (x, x0) -> f x x0
  | Coq_gc_lt (x, x0) -> f0 x x0
  | Coq_gc_lt_set x -> f1 x
  | Coq_gc_eq_set x -> f2 x

  (** val t__rec :
      (VariableLevel.t -> VariableLevel.t -> 'a1) -> (VariableLevel.t ->
      VariableLevel.t -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rec f f0 f1 f2 = function
  | Coq_gc_le (x, x0) -> f x x0
  | Coq_gc_lt (x, x0) -> f0 x x0
  | Coq_gc_lt_set x -> f1 x
  | Coq_gc_eq_set x -> f2 x

  type t = t_

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match x with
    | Coq_gc_le (x0, x1) ->
      (match y with
       | Coq_gc_le (t2, t3) ->
         if VariableLevel.eq_dec x0 t2
         then VariableLevel.eq_dec x1 t3
         else false
       | _ -> false)
    | Coq_gc_lt (x0, x1) ->
      (match y with
       | Coq_gc_lt (t2, t3) ->
         if VariableLevel.eq_dec x0 t2
         then VariableLevel.eq_dec x1 t3
         else false
       | _ -> false)
    | Coq_gc_lt_set x0 ->
      (match y with
       | Coq_gc_lt_set n0 -> Nat.eq_dec x0 n0
       | _ -> false)
    | Coq_gc_eq_set x0 ->
      (match y with
       | Coq_gc_eq_set n0 -> Nat.eq_dec x0 n0
       | _ -> false)
 end

module GoodConstraintSet = Make(GoodConstraint)

(** val coq_GoodConstraintSet_pair :
    GoodConstraintSet.elt -> GoodConstraintSet.elt -> GoodConstraintSet.t **)

let coq_GoodConstraintSet_pair x y =
  GoodConstraintSet.add y (GoodConstraintSet.singleton x)

(** val gc_of_constraint :
    checker_flags -> UnivConstraint.t -> GoodConstraintSet.t option **)

let gc_of_constraint h uc =
  let empty0 = Some GoodConstraintSet.empty in
  let singleton0 = fun x -> Some (GoodConstraintSet.singleton x) in
  let pair = fun x y -> Some (coq_GoodConstraintSet_pair x y) in
  let (p, t0) = uc in
  let (t1, t2) = p in
  (match t1 with
   | Level.Coq_lProp ->
     (match t2 with
      | ConstraintType.Lt ->
        (match t0 with
         | Level.Coq_lProp -> None
         | _ -> if h.prop_sub_type then empty0 else None)
      | ConstraintType.Le ->
        (match t0 with
         | Level.Coq_lProp -> empty0
         | _ -> if h.prop_sub_type then empty0 else None)
      | ConstraintType.Eq ->
        (match t0 with
         | Level.Coq_lProp -> empty0
         | _ -> None))
   | Level.Coq_lSet ->
     (match t2 with
      | ConstraintType.Lt ->
        (match t0 with
         | Level.Level _ -> empty0
         | Level.Var n -> singleton0 (GoodConstraint.Coq_gc_lt_set n)
         | _ -> None)
      | ConstraintType.Le ->
        (match t0 with
         | Level.Coq_lProp -> None
         | _ -> empty0)
      | ConstraintType.Eq ->
        (match t0 with
         | Level.Coq_lSet -> empty0
         | Level.Var n -> singleton0 (GoodConstraint.Coq_gc_eq_set n)
         | _ -> None))
   | Level.Level l ->
     (match t2 with
      | ConstraintType.Lt ->
        (match t0 with
         | Level.Level l' ->
           singleton0 (GoodConstraint.Coq_gc_lt ((VariableLevel.Level l),
             (VariableLevel.Level l')))
         | Level.Var n ->
           singleton0 (GoodConstraint.Coq_gc_lt ((VariableLevel.Level l),
             (VariableLevel.Var n)))
         | _ -> None)
      | ConstraintType.Le ->
        (match t0 with
         | Level.Level l' ->
           singleton0 (GoodConstraint.Coq_gc_le ((VariableLevel.Level l),
             (VariableLevel.Level l')))
         | Level.Var n ->
           singleton0 (GoodConstraint.Coq_gc_le ((VariableLevel.Level l),
             (VariableLevel.Var n)))
         | _ -> None)
      | ConstraintType.Eq ->
        (match t0 with
         | Level.Level l' ->
           pair (GoodConstraint.Coq_gc_le ((VariableLevel.Level l),
             (VariableLevel.Level l'))) (GoodConstraint.Coq_gc_le
             ((VariableLevel.Level l'), (VariableLevel.Level l)))
         | Level.Var n ->
           pair (GoodConstraint.Coq_gc_le ((VariableLevel.Level l),
             (VariableLevel.Var n))) (GoodConstraint.Coq_gc_le
             ((VariableLevel.Var n), (VariableLevel.Level l)))
         | _ -> None))
   | Level.Var n ->
     (match t2 with
      | ConstraintType.Lt ->
        (match t0 with
         | Level.Level l ->
           singleton0 (GoodConstraint.Coq_gc_lt ((VariableLevel.Var n),
             (VariableLevel.Level l)))
         | Level.Var n' ->
           singleton0 (GoodConstraint.Coq_gc_lt ((VariableLevel.Var n),
             (VariableLevel.Var n')))
         | _ -> None)
      | ConstraintType.Le ->
        (match t0 with
         | Level.Coq_lProp -> None
         | Level.Coq_lSet -> singleton0 (GoodConstraint.Coq_gc_eq_set n)
         | Level.Level l ->
           singleton0 (GoodConstraint.Coq_gc_le ((VariableLevel.Var n),
             (VariableLevel.Level l)))
         | Level.Var n' ->
           singleton0 (GoodConstraint.Coq_gc_le ((VariableLevel.Var n),
             (VariableLevel.Var n'))))
      | ConstraintType.Eq ->
        (match t0 with
         | Level.Coq_lProp -> None
         | Level.Coq_lSet -> singleton0 (GoodConstraint.Coq_gc_eq_set n)
         | Level.Level l ->
           pair (GoodConstraint.Coq_gc_le ((VariableLevel.Var n),
             (VariableLevel.Level l))) (GoodConstraint.Coq_gc_le
             ((VariableLevel.Level l), (VariableLevel.Var n)))
         | Level.Var n' ->
           pair (GoodConstraint.Coq_gc_le ((VariableLevel.Var n),
             (VariableLevel.Var n'))) (GoodConstraint.Coq_gc_le
             ((VariableLevel.Var n'), (VariableLevel.Var n))))))

(** val add_gc_of_constraint :
    checker_flags -> UnivConstraint.t -> GoodConstraintSet.t option ->
    GoodConstraintSet.t option **)

let add_gc_of_constraint cf uc s0 =
  bind (Obj.magic option_monad) s0 (fun s1 ->
    bind (Obj.magic option_monad) (gc_of_constraint cf uc) (fun s2 ->
      ret (Obj.magic option_monad) (GoodConstraintSet.union s1 s2)))

(** val gc_of_constraints :
    checker_flags -> ConstraintSet.t -> GoodConstraintSet.t option **)

let gc_of_constraints cf ctrs =
  ConstraintSet.fold (add_gc_of_constraint cf) ctrs (Some
    GoodConstraintSet.empty)

module Coq_wGraph = WeightedGraph(NoPropLevel)

type universes_graph = Coq_wGraph.t

(** val init_graph : universes_graph **)

let init_graph =
  (((Coq_wGraph.VSet.singleton NoPropLevel.Coq_lSet),
    Coq_wGraph.EdgeSet.empty), NoPropLevel.Coq_lSet)

(** val no_prop_levels : LevelSet.t -> Coq_wGraph.VSet.t **)

let no_prop_levels x =
  LevelSet.fold (fun l x0 ->
    match NoPropLevel.of_level l with
    | Some l0 -> Coq_wGraph.VSet.add l0 x0
    | None -> x0) x Coq_wGraph.VSet.empty

(** val gc_of_uctx :
    checker_flags -> ContextSet.t ->
    (Coq_wGraph.VSet.t * GoodConstraintSet.t) option **)

let gc_of_uctx h uctx =
  bind (Obj.magic option_monad) (Obj.magic gc_of_constraints h (snd uctx))
    (fun ctrs ->
    ret (Obj.magic option_monad) ((no_prop_levels (fst uctx)), ctrs))

(** val edge_of_level : VariableLevel.t -> Coq_wGraph.EdgeSet.elt **)

let edge_of_level = function
| VariableLevel.Level l0 ->
  ((NoPropLevel.Coq_lSet, (S O)), (NoPropLevel.Level l0))
| VariableLevel.Var n -> ((NoPropLevel.Coq_lSet, O), (NoPropLevel.Var n))

(** val edge_of_constraint : GoodConstraint.t -> Coq_wGraph.EdgeSet.elt **)

let edge_of_constraint = function
| GoodConstraint.Coq_gc_le (l, l') ->
  (((VariableLevel.to_noprop l), O), (VariableLevel.to_noprop l'))
| GoodConstraint.Coq_gc_lt (l, l') ->
  (((VariableLevel.to_noprop l), (S O)), (VariableLevel.to_noprop l'))
| GoodConstraint.Coq_gc_lt_set n ->
  ((NoPropLevel.Coq_lSet, (S O)),
    (VariableLevel.to_noprop (VariableLevel.Var n)))
| GoodConstraint.Coq_gc_eq_set n ->
  (((VariableLevel.to_noprop (VariableLevel.Var n)), O), NoPropLevel.Coq_lSet)

(** val make_graph :
    (Coq_wGraph.VSet.t * GoodConstraintSet.t) -> Coq_wGraph.t **)

let make_graph uctx =
  let init_edges =
    Coq_wGraph.VSet.fold (fun l e ->
      match l with
      | NoPropLevel.Coq_lSet -> e
      | NoPropLevel.Level s0 ->
        Coq_wGraph.EdgeSet.add (edge_of_level (VariableLevel.Level s0)) e
      | NoPropLevel.Var n ->
        Coq_wGraph.EdgeSet.add (edge_of_level (VariableLevel.Var n)) e)
      (fst uctx) Coq_wGraph.EdgeSet.empty
  in
  let edges =
    GoodConstraintSet.fold (fun ctr ->
      Coq_wGraph.EdgeSet.add (edge_of_constraint ctr)) (snd uctx) init_edges
  in
  (((fst uctx), edges), NoPropLevel.Coq_lSet)

(** val leqb_no_prop_n :
    universes_graph -> nat -> NoPropLevel.t -> NoPropLevel.t -> bool **)

let leqb_no_prop_n =
  Coq_wGraph.leqb_vertices

(** val leqb_expr_n :
    checker_flags -> universes_graph -> nat -> UnivExpr.t -> UnivExpr.t ->
    bool **)

let leqb_expr_n cf g n e1 e2 =
  match e1 with
  | UnivExpr.Coq_lProp ->
    (match e2 with
     | UnivExpr.Coq_lProp -> Nat0.eqb n O
     | UnivExpr.Coq_npe e ->
       let (l, b) = e in
       if b
       then (match n with
             | O -> cf.prop_sub_type
             | S n0 ->
               (match n0 with
                | O -> true
                | S n1 -> leqb_no_prop_n g n1 NoPropLevel.Coq_lSet l))
       else (match n with
             | O -> cf.prop_sub_type
             | S n0 -> leqb_no_prop_n g n0 NoPropLevel.Coq_lSet l))
  | UnivExpr.Coq_npe e ->
    let (l1, b) = e in
    if b
    then (match e2 with
          | UnivExpr.Coq_lProp -> false
          | UnivExpr.Coq_npe e0 ->
            let (l2, b0) = e0 in
            if b0
            then leqb_no_prop_n g n l1 l2
            else leqb_no_prop_n g (S n) l1 l2)
    else (match e2 with
          | UnivExpr.Coq_lProp -> false
          | UnivExpr.Coq_npe e0 ->
            let (l2, b0) = e0 in
            if b0
            then leqb_no_prop_n g (pred n) l1 l2
            else leqb_no_prop_n g n l1 l2)

(** val leqb_expr_univ_n :
    checker_flags -> universes_graph -> nat -> UnivExpr.t -> Universe.t ->
    bool **)

let leqb_expr_univ_n cf g n e1 u =
  if (&&) (UnivExpr.is_prop e1) (Nat0.eqb n O)
  then (||) cf.prop_sub_type (Universe.is_prop u)
  else let (e2, u0) = Universe.exprs u in
       fold_left (fun b e3 -> (||) (leqb_expr_n cf g n e1 e3) b) u0
         (leqb_expr_n cf g n e1 e2)

(** val leqb_universe_n :
    checker_flags -> universes_graph -> nat -> Universe.t -> Universe.t ->
    bool **)

let leqb_universe_n cf g n u1 u2 =
  if (&&) (Universe.is_prop u1) (Nat0.eqb n O)
  then (||) cf.prop_sub_type (Universe.is_prop u2)
  else let (e1, u3) = Universe.exprs u1 in
       fold_left (fun b e2 ->
         (&&)
           ((||) ((&&) (UnivExpr.is_prop e2) (Nat0.eqb n O))
             (leqb_expr_univ_n cf g n e2 u2)) b) u3
         ((||) ((&&) (UnivExpr.is_prop e1) (Nat0.eqb n O))
           (leqb_expr_univ_n cf g n e1 u2))

(** val check_leqb_universe :
    checker_flags -> universes_graph -> Universe.t -> Universe.t -> bool **)

let check_leqb_universe cf g u1 u2 =
  (||)
    ((||)
      ((||) (negb cf.check_univs)
        ((&&) cf.prop_sub_type (Universe.is_prop u1))) (Universe.eqb u1 u2))
    (leqb_universe_n cf g O u1 u2)

(** val check_eqb_universe :
    checker_flags -> universes_graph -> Universe.t -> Universe.t -> bool **)

let check_eqb_universe cf g u1 u2 =
  (||) ((||) (negb cf.check_univs) (Universe.eqb u1 u2))
    ((&&) (leqb_universe_n cf g O u1 u2) (leqb_universe_n cf g O u2 u1))

(** val check_gc_constraint :
    checker_flags -> universes_graph -> GoodConstraint.t -> bool **)

let check_gc_constraint cf g gc =
  (||) (negb cf.check_univs)
    (match gc with
     | GoodConstraint.Coq_gc_le (l, l') ->
       leqb_no_prop_n g O (VariableLevel.to_noprop l)
         (VariableLevel.to_noprop l')
     | GoodConstraint.Coq_gc_lt (l, l') ->
       leqb_no_prop_n g (S O) (VariableLevel.to_noprop l)
         (VariableLevel.to_noprop l')
     | GoodConstraint.Coq_gc_lt_set n ->
       leqb_no_prop_n g (S O) NoPropLevel.Coq_lSet
         (VariableLevel.to_noprop (VariableLevel.Var n))
     | GoodConstraint.Coq_gc_eq_set n ->
       leqb_no_prop_n g O (VariableLevel.to_noprop (VariableLevel.Var n))
         NoPropLevel.Coq_lSet)

(** val check_gc_constraints :
    checker_flags -> universes_graph -> GoodConstraintSet.t -> bool **)

let check_gc_constraints cf g =
  GoodConstraintSet.for_all (check_gc_constraint cf g)

(** val check_constraints :
    checker_flags -> universes_graph -> ConstraintSet.t -> bool **)

let check_constraints cf g ctrs =
  match gc_of_constraints cf ctrs with
  | Some ctrs0 -> check_gc_constraints cf g ctrs0
  | None -> false
