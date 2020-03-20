open Datatypes
open Equalities
open List0
open MSetDecide

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module WPropertiesOn =
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 struct
  module Dec = WDecideOn(E)(M)

  module FM = Dec.F

  (** val coq_In_dec : M.elt -> M.t -> bool **)

  let coq_In_dec x s =
    if M.mem x s then true else false

  (** val of_list : M.elt list -> M.t **)

  let of_list l =
    fold_right M.add M.empty l

  (** val to_list : M.t -> M.elt list **)

  let to_list =
    M.elements

  (** val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2 **)

  let fold_rec f i s pempty pstep =
    let l = rev (M.elements s) in
    let pstep' = fun x a s' s'' x0 -> pstep x a s' s'' __ __ __ x0 in
    let rec f0 l0 pstep'0 s0 =
      match l0 with
      | [] -> pempty s0 __
      | y :: l1 ->
        pstep'0 y (fold_right f i l1) (of_list l1) s0 __ __ __
          (f0 l1 (fun x a0 s' s'' _ _ _ x0 ->
            pstep'0 x a0 s' s'' __ __ __ x0) (of_list l1))
    in f0 l (fun x a s' s'' _ _ _ x0 -> pstep' x a s' s'' x0) s

  (** val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2 **)

  let fold_rec_bis f i s pmorphism pempty pstep =
    fold_rec f i s (fun s' _ -> pmorphism M.empty s' i __ pempty)
      (fun x a s' s'' _ _ _ x0 ->
      pmorphism (M.add x s') s'' (f x a) __ (pstep x a s' __ __ x0))

  (** val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 **)

  let fold_rec_nodep f i s x x0 =
    fold_rec_bis f i s (fun _ _ _ _ x1 -> x1) x (fun x1 a _ _ _ x2 ->
      x0 x1 a __ x2)

  (** val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2 **)

  let fold_rec_weak f i x x0 x1 s =
    fold_rec_bis f i s x x0 (fun x2 a s' _ _ x3 -> x1 x2 a s' __ x3)

  (** val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)

  let fold_rel f g i j s rempty rstep =
    let l = rev (M.elements s) in
    let rstep' = fun x a b x0 -> rstep x a b __ x0 in
    let rec f0 l0 rstep'0 =
      match l0 with
      | [] -> rempty
      | y :: l1 ->
        rstep'0 y (fold_right f i l1) (fold_right g j l1) __
          (f0 l1 (fun x a0 b _ x0 -> rstep'0 x a0 b __ x0))
    in f0 l (fun x a b _ x0 -> rstep' x a b x0)

  (** val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1 **)

  let set_induction x x0 s =
    fold_rec (fun _ _ -> ()) () s x (fun x1 _ s' s'' _ _ _ x2 ->
      x0 s' s'' x2 x1 __ __)

  (** val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1 **)

  let set_induction_bis x x0 x1 s =
    fold_rec_bis (fun _ _ -> ()) () s (fun s0 s' _ _ x2 -> x s0 s' __ x2) x0
      (fun x2 _ s' _ _ x3 -> x1 x2 s' __ x3)

  (** val cardinal_inv_2 : M.t -> nat -> M.elt **)

  let cardinal_inv_2 s _ =
    let l = M.elements s in
    (match l with
     | [] -> assert false (* absurd case *)
     | e :: _ -> e)

  (** val cardinal_inv_2b : M.t -> M.elt **)

  let cardinal_inv_2b s =
    let n = M.cardinal s in
    let x = fun x -> cardinal_inv_2 s x in
    (match n with
     | O -> assert false (* absurd case *)
     | S n0 -> x n0)
 end
