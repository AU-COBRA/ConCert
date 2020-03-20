open Bool
open Compare_dec
open Datatypes
open List0
open MSetFacts
open MSetList
open MSetProperties
open Nat0
open Orders
open PeanoNat
open Specif
open Ssrbool

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Nbar =
 struct
  type t = nat option

  (** val max : t -> t -> t **)

  let max n m =
    match n with
    | Some n0 -> (match m with
                  | Some m0 -> Some (max n0 m0)
                  | None -> Some n0)
    | None -> m

  (** val add : t -> t -> t **)

  let add n m =
    match n with
    | Some n0 -> (match m with
                  | Some m0 -> Some (add n0 m0)
                  | None -> None)
    | None -> None

  (** val le_dec : t -> t -> bool **)

  let le_dec n m =
    match n with
    | Some n0 -> (match m with
                  | Some m0 -> le_dec n0 m0
                  | None -> false)
    | None -> true
 end

module WeightedGraph =
 functor (V:UsualOrderedType) ->
 struct
  module VSet = Make(V)

  module VSetFact = WFactsOn(V)(VSet)

  module VSetProp = WPropertiesOn(V)(VSet)

  module Edge =
   struct
    type t = (V.t * nat) * V.t

    (** val compare : t -> t -> comparison **)

    let compare pat pat0 =
      let (p, y) = pat in
      let (x, n) = p in
      let (p0, y') = pat0 in
      let (x', n') = p0 in
      (match V.compare x x' with
       | Eq -> (match Nat.compare n n' with
                | Eq -> V.compare y y'
                | x0 -> x0)
       | x0 -> x0)

    (** val eq_dec : t -> t -> bool **)

    let eq_dec x y =
      let (x0, x1) = x in
      let (p, t0) = y in
      if let (x2, x3) = x0 in
         let (t1, n) = p in if V.eq_dec x2 t1 then Nat.eq_dec x3 n else false
      then V.eq_dec x1 t0
      else false

    (** val eqb : t -> t -> bool **)

    let eqb x y =
      match compare x y with
      | Eq -> true
      | _ -> false
   end

  module EdgeSet = Make(Edge)

  module EdgeSetFact = WFactsOn(Edge)(EdgeSet)

  module EdgeSetProp = WPropertiesOn(Edge)(EdgeSet)

  type t = (VSet.t * EdgeSet.t) * V.t

  (** val coq_V : t -> VSet.t **)

  let coq_V g =
    fst (fst g)

  (** val coq_E : t -> EdgeSet.t **)

  let coq_E g =
    snd (fst g)

  (** val s : t -> V.t **)

  let s =
    snd

  (** val e_source : Edge.t -> V.t **)

  let e_source x =
    fst (fst x)

  (** val e_target : Edge.t -> V.t **)

  let e_target =
    snd

  (** val e_weight : Edge.t -> nat **)

  let e_weight x =
    snd (fst x)

  type labelling = V.t -> nat

  (** val add_node : t -> VSet.elt -> t **)

  let add_node g x =
    (((VSet.add x (coq_V g)), (coq_E g)), (s g))

  (** val add_edge : t -> Edge.t -> t **)

  let add_edge g e =
    (((VSet.add (e_source e) (VSet.add (e_target e) (coq_V g))),
      (EdgeSet.add e (coq_E g))), (s g))

  type coq_Edges = (nat, __) sigT

  type coq_Paths =
  | Coq_paths_refl of V.t
  | Coq_paths_step of V.t * V.t * V.t * coq_Edges * coq_Paths

  (** val coq_Paths_rect :
      t -> (V.t -> 'a1) -> (V.t -> V.t -> V.t -> coq_Edges -> coq_Paths ->
      'a1 -> 'a1) -> V.t -> V.t -> coq_Paths -> 'a1 **)

  let rec coq_Paths_rect g f f0 _ _ = function
  | Coq_paths_refl x -> f x
  | Coq_paths_step (x, y, z, e, p0) ->
    f0 x y z e p0 (coq_Paths_rect g f f0 y z p0)

  (** val coq_Paths_rec :
      t -> (V.t -> 'a1) -> (V.t -> V.t -> V.t -> coq_Edges -> coq_Paths ->
      'a1 -> 'a1) -> V.t -> V.t -> coq_Paths -> 'a1 **)

  let rec coq_Paths_rec g f f0 _ _ = function
  | Coq_paths_refl x -> f x
  | Coq_paths_step (x, y, z, e, p0) ->
    f0 x y z e p0 (coq_Paths_rec g f f0 y z p0)

  (** val weight : t -> V.t -> V.t -> coq_Paths -> nat **)

  let rec weight g _ _ = function
  | Coq_paths_refl _ -> O
  | Coq_paths_step (_, y, z, e, p0) -> add (projT1 e) (weight g y z p0)

  (** val nodes : t -> V.t -> V.t -> coq_Paths -> VSet.t **)

  let rec nodes g _ _ = function
  | Coq_paths_refl _ -> VSet.empty
  | Coq_paths_step (x, y, z, _, p0) -> VSet.add x (nodes g y z p0)

  (** val concat :
      t -> V.t -> V.t -> V.t -> coq_Paths -> coq_Paths -> coq_Paths **)

  let rec concat g _ _ z p q =
    match p with
    | Coq_paths_refl _ -> q
    | Coq_paths_step (x0, y0, z0, e, p0) ->
      Coq_paths_step (x0, y0, z, e, (concat g y0 z0 z p0 q))

  (** val length : t -> V.t -> V.t -> coq_Paths -> nat **)

  let rec length g _ _ = function
  | Coq_paths_refl _ -> O
  | Coq_paths_step (_, y, z, _, p0) -> S (length g y z p0)

  type coq_SimplePaths =
  | Coq_spaths_refl of VSet.t * V.t
  | Coq_spaths_step of VSet.t * VSet.t * V.t * V.t * V.t * coq_Edges
     * coq_SimplePaths

  (** val coq_SimplePaths_rect :
      t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> VSet.t -> V.t -> V.t -> V.t
      -> __ -> coq_Edges -> coq_SimplePaths -> 'a1 -> 'a1) -> VSet.t -> V.t
      -> V.t -> coq_SimplePaths -> 'a1 **)

  let rec coq_SimplePaths_rect g f f0 _ _ _ = function
  | Coq_spaths_refl (s1, x) -> f s1 x
  | Coq_spaths_step (s1, s', x, y, z, e, s2) ->
    f0 s1 s' x y z __ e s2 (coq_SimplePaths_rect g f f0 s1 y z s2)

  (** val coq_SimplePaths_rec :
      t -> (VSet.t -> V.t -> 'a1) -> (VSet.t -> VSet.t -> V.t -> V.t -> V.t
      -> __ -> coq_Edges -> coq_SimplePaths -> 'a1 -> 'a1) -> VSet.t -> V.t
      -> V.t -> coq_SimplePaths -> 'a1 **)

  let rec coq_SimplePaths_rec g f f0 _ _ _ = function
  | Coq_spaths_refl (s1, x) -> f s1 x
  | Coq_spaths_step (s1, s', x, y, z, e, s2) ->
    f0 s1 s' x y z __ e s2 (coq_SimplePaths_rec g f f0 s1 y z s2)

  (** val to_paths :
      t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> coq_Paths **)

  let rec to_paths g _ _ _ = function
  | Coq_spaths_refl (_, x) -> Coq_paths_refl x
  | Coq_spaths_step (s0, _, x, y, z, e, p0) ->
    Coq_paths_step (x, y, z, e, (to_paths g s0 y z p0))

  (** val sweight : t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> nat **)

  let rec sweight g _ _ _ = function
  | Coq_spaths_refl (_, _) -> O
  | Coq_spaths_step (s0, _, _, y, z, e, p0) ->
    add (projT1 e) (sweight g s0 y z p0)

  (** val is_simple : t -> V.t -> V.t -> coq_Paths -> bool **)

  let rec is_simple g _ _ = function
  | Coq_paths_refl _ -> true
  | Coq_paths_step (x, y, z, _, p0) ->
    (&&) (negb (VSet.mem x (nodes g y z p0))) (is_simple g y z p0)

  (** val to_simple : t -> V.t -> V.t -> coq_Paths -> coq_SimplePaths **)

  let rec to_simple g _ _ = function
  | Coq_paths_refl x -> Coq_spaths_refl ((nodes g x x (Coq_paths_refl x)), x)
  | Coq_paths_step (x, y, z, e, p0) ->
    Coq_spaths_step ((nodes g y z p0),
      (nodes g x z (Coq_paths_step (x, y, z, e, p0))), x, y, z, e,
      (to_simple g y z p0))

  (** val add_end :
      t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> V.t -> coq_Edges ->
      VSet.t -> coq_SimplePaths **)

  let rec add_end g _ _ _ p z e s' =
    match p with
    | Coq_spaths_refl (s0, x) ->
      Coq_spaths_step (s0, s', x, z, z, e, (Coq_spaths_refl (s0, z)))
    | Coq_spaths_step (s0, _, x, x0, y, e0, p0) ->
      Coq_spaths_step ((VSet.add y s0), s', x, x0, z, e0,
        (add_end g s0 x0 y p0 z e (VSet.add y s0)))

  (** val coq_SimplePaths_sub :
      t -> VSet.t -> VSet.t -> V.t -> V.t -> coq_SimplePaths ->
      coq_SimplePaths **)

  let rec coq_SimplePaths_sub g _ s' _ _ = function
  | Coq_spaths_refl (_, x) -> Coq_spaths_refl (s', x)
  | Coq_spaths_step (s0, _, x, y, z, e, s1) ->
    Coq_spaths_step ((VSet.remove x s'), s', x, y, z, e,
      (coq_SimplePaths_sub g s0 (VSet.remove x s') y z s1))

  (** val snodes : t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> VSet.t **)

  let rec snodes g _ _ _ = function
  | Coq_spaths_refl (_, _) -> VSet.empty
  | Coq_spaths_step (s0, _, x, y, z, _, p0) -> VSet.add x (snodes g s0 y z p0)

  (** val split :
      t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> VSet.elt -> bool ->
      coq_SimplePaths * coq_SimplePaths **)

  let rec split g _ _ _ p u hu =
    match p with
    | Coq_spaths_refl (s0, x) ->
      if hu
      then assert false (* absurd case *)
      else ((Coq_spaths_refl ((VSet.remove x s0), x)), (Coq_spaths_refl (s0,
             x)))
    | Coq_spaths_step (s0, s', x, y, z, e, s1) ->
      let s2 = V.eq_dec x u in
      if s2
      then ((Coq_spaths_refl ((VSet.remove u s'), u)), (Coq_spaths_step (s0,
             s', u, y, z, e, s1)))
      else let iHp = split g s0 y z s1 u hu in
           ((Coq_spaths_step ((VSet.remove u s0), (VSet.remove u s'), x, y,
           u, e, (fst iHp))), (coq_SimplePaths_sub g s0 s' u z (snd iHp)))

  (** val split' :
      t -> VSet.t -> V.t -> V.t -> coq_SimplePaths ->
      coq_SimplePaths * coq_SimplePaths **)

  let split' g s0 x y p =
    split g s0 x y p y false

  (** val simplify :
      t -> VSet.t -> V.t -> V.t -> coq_Paths -> coq_SimplePaths -> VSet.t ->
      (V.t, coq_SimplePaths) sigT **)

  let rec simplify g s0 _ _ q p s' =
    match q with
    | Coq_paths_refl x -> Coq_existT (x, (coq_SimplePaths_sub g s0 s' x x p))
    | Coq_paths_step (y, y', z, e, q0) ->
      if VSet.mem y s0
      then let (p1, p2) = split' g s0 z y p in
           if ltb O (sweight g s0 y y p2)
           then Coq_existT (y, (coq_SimplePaths_sub g s0 s' y y p2))
           else simplify g s0 z y' q0
                  (add_end g (VSet.remove y s0) z y p1 y' e s0) s'
      else simplify g (VSet.add y s0) z y' q0
             (add_end g s0 z y p y' e (VSet.add y s0)) s'

  (** val succs : t -> V.t -> (nat * V.t) list **)

  let succs g x =
    let l =
      filter (fun e -> is_left (V.eq_dec (e_source e) x))
        (EdgeSet.elements (coq_E g))
    in
    map (fun e -> ((e_weight e), (e_target e))) l

  (** val lsp00 : t -> nat -> VSet.t -> V.t -> V.t -> Nbar.t **)

  let rec lsp00 g fuel s0 x z =
    let base = if V.eq_dec x z then Some O else None in
    (match fuel with
     | O -> base
     | S fuel0 ->
       if VSet.mem x s0
       then let ds =
              map (fun pat ->
                let (n, y) = pat in
                Nbar.add (Some n) (lsp00 g fuel0 (VSet.remove x s0) y z))
                (succs g x)
            in
            fold_left Nbar.max ds base
       else base)

  (** val lsp0 : t -> VSet.t -> V.t -> V.t -> Nbar.t **)

  let lsp0 g s0 =
    lsp00 g (VSet.cardinal s0) s0

  (** val lsp : t -> V.t -> V.t -> Nbar.t **)

  let lsp g =
    lsp0 g (coq_V g)

  (** val reduce :
      t -> VSet.t -> V.t -> V.t -> coq_SimplePaths -> coq_SimplePaths **)

  let rec reduce g _ _ _ = function
  | Coq_spaths_refl (_, x) -> Coq_spaths_refl (VSet.empty, x)
  | Coq_spaths_step (s0, _, x, y, z, e, s1) ->
    Coq_spaths_step ((snodes g s0 y z s1), (VSet.add x (snodes g s0 y z s1)),
      x, y, z, e, (reduce g s0 y z s1))

  (** val simplify2 : t -> V.t -> V.t -> coq_Paths -> coq_SimplePaths **)

  let rec simplify2 g _ _ = function
  | Coq_paths_refl x -> Coq_spaths_refl (VSet.empty, x)
  | Coq_paths_step (x, y, z, e, p0) ->
    let iHp = simplify2 g y z p0 in
    if VSet.mem x (snodes g (nodes g y z p0) y z iHp)
    then coq_SimplePaths_sub g (nodes g y z p0) (VSet.add x (nodes g y z p0))
           x z (snd (split g (nodes g y z p0) y z iHp x true))
    else coq_SimplePaths_sub g
           (VSet.add x (snodes g (nodes g y z p0) y z iHp))
           (VSet.add x (nodes g y z p0)) x z (Coq_spaths_step
           ((snodes g (nodes g y z p0) y z iHp),
           (VSet.add x (snodes g (nodes g y z p0) y z iHp)), x, y, z, e,
           (reduce g (nodes g y z p0) y z iHp)))

  (** val simplify2' : t -> V.t -> V.t -> coq_Paths -> coq_SimplePaths **)

  let simplify2' g x z p =
    coq_SimplePaths_sub g (nodes g x z p) (coq_V g) x z (simplify2 g x z p)

  (** val coq_VSet_Forall_reflect :
      (VSet.elt -> bool) -> (VSet.elt -> reflect) -> VSet.t -> reflect **)

  let coq_VSet_Forall_reflect f _ s0 =
    iff_reflect (VSet.for_all f s0)

  (** val reflect_logically_equiv : bool -> reflect -> reflect **)

  let reflect_logically_equiv _ h0 =
    h0

  (** val is_acyclic : t -> bool **)

  let is_acyclic g =
    VSet.for_all (fun x ->
      match lsp g x x with
      | Some n -> (match n with
                   | O -> true
                   | S _ -> false)
      | None -> false) (coq_V g)

  (** val spaths_one :
      t -> VSet.t -> VSet.elt -> V.t -> nat -> coq_SimplePaths **)

  let spaths_one _ s0 x y k =
    Coq_spaths_step ((VSet.remove x s0), s0, x, y, y, (Coq_existT (k, __)),
      (Coq_spaths_refl ((VSet.remove x s0), y)))

  (** val coq_G' : t -> V.t -> V.t -> nat -> t **)

  let coq_G' g y_0 x_0 k =
    (((coq_V g), (EdgeSet.add ((y_0, k), x_0) (coq_E g))), (s g))

  (** val to_G' :
      t -> V.t -> V.t -> nat -> V.t -> V.t -> coq_Paths -> coq_Paths **)

  let rec to_G' g y_0 x_0 k _ _ = function
  | Coq_paths_refl x -> Coq_paths_refl x
  | Coq_paths_step (x, y, z, e, p) ->
    Coq_paths_step (x, y, z, (Coq_existT ((projT1 e), __)),
      (to_G' g y_0 x_0 k y z p))

  (** val from_G' :
      t -> V.t -> V.t -> nat -> VSet.t -> V.t -> V.t -> coq_SimplePaths ->
      (coq_SimplePaths, coq_SimplePaths * coq_SimplePaths) sum **)

  let rec from_G' g y_0 x_0 k _ _ _ = function
  | Coq_spaths_refl (s0, x) -> Coq_inl (Coq_spaths_refl (s0, x))
  | Coq_spaths_step (s0, s', x, y, z, e, s1) ->
    let s2 = Edge.eq_dec ((y_0, k), x_0) ((x, (projT1 e)), y) in
    if s2
    then Coq_inr ((Coq_spaths_refl (s', x)),
           (coq_SimplePaths_sub g s0 s' x_0 z
             (match from_G' g y_0 x_0 k s0 y z s1 with
              | Coq_inl x0 -> x0
              | Coq_inr x0 -> snd x0)))
    else (match from_G' g y_0 x_0 k s0 y z s1 with
          | Coq_inl x0 ->
            Coq_inl (Coq_spaths_step (s0, s', x, y, z, (Coq_existT
              ((projT1 e), __)), x0))
          | Coq_inr x0 ->
            Coq_inr ((Coq_spaths_step (s0, s', x, y, y_0, (Coq_existT
              ((projT1 e), __)), (fst x0))),
              (coq_SimplePaths_sub g s0 s' x_0 z (snd x0))))

  (** val sto_G' :
      t -> V.t -> V.t -> nat -> VSet.t -> V.t -> V.t -> coq_SimplePaths ->
      coq_SimplePaths **)

  let rec sto_G' g y_0 x_0 k _ _ _ = function
  | Coq_spaths_refl (s0, x) -> Coq_spaths_refl (s0, x)
  | Coq_spaths_step (s0, s', x, y, z, e, s1) ->
    Coq_spaths_step (s0, s', x, y, z, (Coq_existT ((projT1 e), __)),
      (sto_G' g y_0 x_0 k s0 y z s1))

  (** val leqb_vertices : t -> nat -> V.t -> VSet.elt -> bool **)

  let leqb_vertices g n x y =
    if VSet.mem y (coq_V g)
    then is_left (Nbar.le_dec (Some n) (lsp g x y))
    else (&&) (eqb n O)
           ((||) (is_left (V.eq_dec x y))
             (is_left (Nbar.le_dec (Some O) (lsp g x (s g)))))
 end
