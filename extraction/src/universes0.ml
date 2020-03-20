open BasicAst
open BinInt
open BinPos
open Bool
open Datatypes
open List0
open MCCompare
open MCList
open MCString
open MSetList
open MSetProperties
open PeanoNat
open String0

type __ = Obj.t

type valuation = { valuation_mono : (char list -> int);
                   valuation_poly : (nat -> nat) }

type 'a coq_Evaluable = valuation -> 'a -> int

(** val coq_val : 'a1 coq_Evaluable -> valuation -> 'a1 -> int **)

let coq_val evaluable =
  evaluable

module Level =
 struct
  type t_ =
  | Coq_lProp
  | Coq_lSet
  | Level of char list
  | Var of nat

  (** val t__rect :
      'a1 -> 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rect f f0 f1 f2 = function
  | Coq_lProp -> f
  | Coq_lSet -> f0
  | Level x -> f1 x
  | Var x -> f2 x

  (** val t__rec :
      'a1 -> 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rec f f0 f1 f2 = function
  | Coq_lProp -> f
  | Coq_lSet -> f0
  | Level x -> f1 x
  | Var x -> f2 x

  type t = t_

  (** val is_small : t -> bool **)

  let is_small = function
  | Coq_lProp -> true
  | Coq_lSet -> true
  | _ -> false

  (** val is_prop : t -> bool **)

  let is_prop = function
  | Coq_lProp -> true
  | _ -> false

  (** val is_set : t -> bool **)

  let is_set = function
  | Coq_lSet -> true
  | _ -> false

  (** val is_var : t -> bool **)

  let is_var = function
  | Var _ -> true
  | _ -> false

  (** val coq_Evaluable : t coq_Evaluable **)

  let coq_Evaluable v = function
  | Coq_lProp -> (~-) 1
  | Coq_lSet -> 0
  | Level s -> (v.valuation_mono s)
  | Var x -> Z.of_nat (v.valuation_poly x)

  (** val compare : t -> t -> comparison **)

  let compare l1 l2 =
    match l1 with
    | Coq_lProp -> (match l2 with
                    | Coq_lProp -> Eq
                    | _ -> Lt)
    | Coq_lSet -> (match l2 with
                   | Coq_lProp -> Gt
                   | Coq_lSet -> Eq
                   | _ -> Lt)
    | Level s1 ->
      (match l2 with
       | Level s2 -> string_compare s1 s2
       | Var _ -> Lt
       | _ -> Gt)
    | Var n -> (match l2 with
                | Var m -> Nat.compare n m
                | _ -> Gt)

  (** val eq_dec : t -> t -> bool **)

  let eq_dec l1 l2 =
    match l1 with
    | Coq_lProp -> (match l2 with
                    | Coq_lProp -> true
                    | _ -> false)
    | Coq_lSet -> (match l2 with
                   | Coq_lSet -> true
                   | _ -> false)
    | Level x -> (match l2 with
                  | Level s0 -> string_dec x s0
                  | _ -> false)
    | Var x -> (match l2 with
                | Var n0 -> Nat.eq_dec x n0
                | _ -> false)

  (** val eqb : t -> t -> bool **)

  let eqb l1 l2 =
    match compare l1 l2 with
    | Eq -> true
    | _ -> false

  (** val eqb_spec : t -> t -> reflect **)

  let eqb_spec l l' =
    match l with
    | Coq_lProp -> (match l' with
                    | Coq_lProp -> ReflectT
                    | _ -> ReflectF)
    | Coq_lSet -> (match l' with
                   | Coq_lSet -> ReflectT
                   | _ -> ReflectF)
    | Level s ->
      (match l' with
       | Level s0 -> iff_reflect (eqb (Level s) (Level s0))
       | _ -> ReflectF)
    | Var n ->
      (match l' with
       | Var n0 -> iff_reflect (eqb (Var n) (Var n0))
       | _ -> ReflectF)
 end

module LevelSet = MakeWithLeibniz(Level)

module LevelSetProp = WPropertiesOn(Level)(LevelSet)

(** val coq_LevelSet_pair : LevelSet.elt -> LevelSet.elt -> LevelSet.t **)

let coq_LevelSet_pair x y =
  LevelSet.add y (LevelSet.singleton x)

module NoPropLevel =
 struct
  type t_ =
  | Coq_lSet
  | Level of char list
  | Var of nat

  (** val t__rect : 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rect f f0 f1 = function
  | Coq_lSet -> f
  | Level x -> f0 x
  | Var x -> f1 x

  (** val t__rec : 'a1 -> (char list -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rec f f0 f1 = function
  | Coq_lSet -> f
  | Level x -> f0 x
  | Var x -> f1 x

  type t = t_

  (** val coq_Level_Evaluable : t coq_Evaluable **)

  let coq_Level_Evaluable v = function
  | Coq_lSet -> 0
  | Level s -> (v.valuation_mono s)
  | Var x -> Z.of_nat (v.valuation_poly x)

  (** val compare : t -> t -> comparison **)

  let compare l1 l2 =
    match l1 with
    | Coq_lSet -> (match l2 with
                   | Coq_lSet -> Eq
                   | _ -> Lt)
    | Level s1 ->
      (match l2 with
       | Coq_lSet -> Gt
       | Level s2 -> string_compare s1 s2
       | Var _ -> Lt)
    | Var n -> (match l2 with
                | Var m -> Nat.compare n m
                | _ -> Gt)

  (** val eq_dec : t -> t -> bool **)

  let eq_dec l1 l2 =
    match l1 with
    | Coq_lSet -> (match l2 with
                   | Coq_lSet -> true
                   | _ -> false)
    | Level x -> (match l2 with
                  | Level s0 -> string_dec x s0
                  | _ -> false)
    | Var x -> (match l2 with
                | Var n0 -> Nat.eq_dec x n0
                | _ -> false)

  (** val of_level : Level.t -> t option **)

  let of_level = function
  | Level.Coq_lProp -> None
  | Level.Coq_lSet -> Some Coq_lSet
  | Level.Level s -> Some (Level s)
  | Level.Var n -> Some (Var n)

  (** val to_level : t -> Level.t **)

  let to_level = function
  | Coq_lSet -> Level.Coq_lSet
  | Level s -> Level.Level s
  | Var n -> Level.Var n

  (** val is_small : t -> bool **)

  let is_small = function
  | Coq_lSet -> true
  | _ -> false
 end

module UnivExpr =
 struct
  type t_ =
  | Coq_lProp
  | Coq_npe of (NoPropLevel.t * bool)

  (** val t__rect : 'a1 -> ((NoPropLevel.t * bool) -> 'a1) -> t_ -> 'a1 **)

  let t__rect f f0 = function
  | Coq_lProp -> f
  | Coq_npe x -> f0 x

  (** val t__rec : 'a1 -> ((NoPropLevel.t * bool) -> 'a1) -> t_ -> 'a1 **)

  let t__rec f f0 = function
  | Coq_lProp -> f
  | Coq_npe x -> f0 x

  type t = t_

  (** val coq_Evaluable : t coq_Evaluable **)

  let coq_Evaluable v = function
  | Coq_lProp -> (~-) 1
  | Coq_npe e ->
    let (l0, b) = e in
    Z.add (if b then 1 else 0) (coq_val NoPropLevel.coq_Level_Evaluable v l0)

  (** val is_small : t -> bool **)

  let is_small = function
  | Coq_lProp -> true
  | Coq_npe e0 ->
    let (t0, b) = e0 in
    (match t0 with
     | NoPropLevel.Coq_lSet -> if b then false else true
     | _ -> false)

  (** val is_level : t -> bool **)

  let is_level = function
  | Coq_lProp -> true
  | Coq_npe e0 -> let (_, b) = e0 in if b then false else true

  (** val is_prop : t -> bool **)

  let is_prop = function
  | Coq_lProp -> true
  | Coq_npe _ -> false

  (** val get_level : t -> Level.t **)

  let get_level = function
  | Coq_lProp -> Level.Coq_lProp
  | Coq_npe e0 -> let (l, _) = e0 in NoPropLevel.to_level l

  (** val get_noprop : t -> NoPropLevel.t option **)

  let get_noprop = function
  | Coq_lProp -> None
  | Coq_npe e0 -> let (l, _) = e0 in Some l

  (** val make : Level.t -> t **)

  let make l =
    match NoPropLevel.of_level l with
    | Some l0 -> Coq_npe (l0, false)
    | None -> Coq_lProp

  (** val prop : t **)

  let prop =
    Coq_lProp

  (** val set : t **)

  let set =
    Coq_npe (NoPropLevel.Coq_lSet, false)

  (** val type1 : t **)

  let type1 =
    Coq_npe (NoPropLevel.Coq_lSet, true)

  (** val from_kernel_repr : (Level.t * bool) -> t **)

  let from_kernel_repr e =
    match NoPropLevel.of_level (fst e) with
    | Some l -> Coq_npe (l, (snd e))
    | None -> Coq_lProp

  (** val to_kernel_repr : t -> Level.t * bool **)

  let to_kernel_repr = function
  | Coq_lProp -> (Level.Coq_lProp, false)
  | Coq_npe e0 -> let (l, b) = e0 in ((NoPropLevel.to_level l), b)

  (** val compare : t -> t -> comparison **)

  let compare x y =
    match x with
    | Coq_lProp -> (match y with
                    | Coq_lProp -> Eq
                    | Coq_npe _ -> Lt)
    | Coq_npe e ->
      let (l1, b1) = e in
      (match y with
       | Coq_lProp -> Gt
       | Coq_npe e0 ->
         let (l2, b2) = e0 in
         (match NoPropLevel.compare l1 l2 with
          | Eq -> bool_compare b1 b2
          | x0 -> x0))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec l1 l2 =
    match l1 with
    | Coq_lProp -> (match l2 with
                    | Coq_lProp -> true
                    | Coq_npe _ -> false)
    | Coq_npe x ->
      (match l2 with
       | Coq_lProp -> false
       | Coq_npe e0 ->
         let (x0, x1) = x in
         let (t0, b0) = e0 in
         if match x0 with
            | NoPropLevel.Coq_lSet ->
              (match t0 with
               | NoPropLevel.Coq_lSet -> true
               | _ -> false)
            | NoPropLevel.Level x2 ->
              (match t0 with
               | NoPropLevel.Level s0 ->
                 let rec f s x3 =
                   match s with
                   | [] -> (match x3 with
                            | [] -> true
                            | _::_ -> false)
                   | a::s1 ->
                     (match x3 with
                      | [] -> false
                      | a1::s2 ->
                        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                          (fun x4 x5 x6 x7 x8 x9 x10 x11 ->
                          (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                            (fun b9 b10 b11 b12 b13 b14 b15 b16 ->
                            if x4
                            then if b9
                                 then if x5
                                      then if b10
                                           then if x6
                                                then if b11
                                                     then if x7
                                                          then if b12
                                                               then if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                               else false
                                                          else if b12
                                                               then false
                                                               else if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                     else false
                                                else if b11
                                                     then false
                                                     else if x7
                                                          then if b12
                                                               then if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                               else false
                                                          else if b12
                                                               then false
                                                               else if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                           else false
                                      else if b10
                                           then false
                                           else if x6
                                                then if b11
                                                     then if x7
                                                          then if b12
                                                               then if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                               else false
                                                          else if b12
                                                               then false
                                                               else if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                     else false
                                                else if b11
                                                     then false
                                                     else if x7
                                                          then if b12
                                                               then if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                               else false
                                                          else if b12
                                                               then false
                                                               else if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                 else false
                            else if b9
                                 then false
                                 else if x5
                                      then if b10
                                           then if x6
                                                then if b11
                                                     then if x7
                                                          then if b12
                                                               then if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                               else false
                                                          else if b12
                                                               then false
                                                               else if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                     else false
                                                else if b11
                                                     then false
                                                     else if x7
                                                          then if b12
                                                               then if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                               else false
                                                          else if b12
                                                               then false
                                                               else if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                           else false
                                      else if b10
                                           then false
                                           else if x6
                                                then if b11
                                                     then if x7
                                                          then if b12
                                                               then if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                               else false
                                                          else if b12
                                                               then false
                                                               else if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                     else false
                                                else if b11
                                                     then false
                                                     else if x7
                                                          then if b12
                                                               then if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                               else false
                                                          else if b12
                                                               then false
                                                               else if x8
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x9
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x10
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2)
                            a1)
                          a)
                 in f x2 s0
               | _ -> false)
            | NoPropLevel.Var x2 ->
              (match t0 with
               | NoPropLevel.Var n0 ->
                 let rec f n x3 =
                   match n with
                   | O -> (match x3 with
                           | O -> true
                           | S _ -> false)
                   | S n1 -> (match x3 with
                              | O -> false
                              | S n2 -> f n1 n2)
                 in f x2 n0
               | _ -> false)
         then if x1
              then if b0 then true else false
              else if b0 then false else true
         else false)
 end

module UnivExprSet = MakeWithLeibniz(UnivExpr)

module Universe =
 struct
  type t =
    UnivExprSet.t
    (* singleton inductive, whose constructor was Build_t *)

  (** val t_set : t -> UnivExprSet.t **)

  let t_set t0 =
    t0

  (** val eqb : t -> t -> bool **)

  let eqb u1 u2 =
    UnivExprSet.equal (t_set u1) (t_set u2)

  (** val make' : UnivExpr.t -> t **)

  let make' =
    UnivExprSet.singleton

  (** val make : Level.t -> t **)

  let make l =
    make' (UnivExpr.make l)

  (** val add : UnivExpr.t -> t -> t **)

  let add e u =
    UnivExprSet.add e (t_set u)

  (** val add_list : UnivExpr.t list -> t -> t **)

  let add_list =
    fold_left (fun u e -> add e u)

  (** val is_small : t -> bool **)

  let is_small s =
    UnivExprSet.for_all UnivExpr.is_small (t_set s)

  (** val is_prop : t -> bool **)

  let is_prop s =
    UnivExprSet.for_all UnivExpr.is_prop (t_set s)

  (** val type1 : t **)

  let type1 =
    make' UnivExpr.type1

  (** val super : Level.t -> t **)

  let super l =
    match NoPropLevel.of_level l with
    | Some l0 ->
      (match l0 with
       | NoPropLevel.Coq_lSet -> type1
       | _ -> make' (UnivExpr.Coq_npe (l0, true)))
    | None -> type1

  (** val exprs : t -> UnivExpr.t * UnivExpr.t list **)

  let exprs u =
    let filtered_var = UnivExprSet.elements (t_set u) in
    (match filtered_var with
     | [] -> assert false (* absurd case *)
     | e :: l -> (e, l))

  (** val map : (UnivExpr.t -> UnivExpr.t) -> t -> t **)

  let map f u =
    let (e, l) = exprs u in add_list (map f l) (make' (f e))

  (** val try_suc : t -> t **)

  let try_suc =
    map (fun l ->
      match l with
      | UnivExpr.Coq_lProp -> UnivExpr.type1
      | UnivExpr.Coq_npe e -> let (l0, _) = e in UnivExpr.Coq_npe (l0, true))

  (** val sup : t -> t -> t **)

  let sup u v =
    UnivExprSet.union (t_set u) (t_set v)

  (** val sort_of_product : t -> t -> t **)

  let sort_of_product domsort rangsort =
    if is_prop rangsort then rangsort else sup domsort rangsort

  (** val get_is_level : t -> Level.t option **)

  let get_is_level u =
    match UnivExprSet.elements (t_set u) with
    | [] -> None
    | e :: l0 ->
      (match e with
       | UnivExpr.Coq_lProp ->
         (match l0 with
          | [] -> Some Level.Coq_lProp
          | _ :: _ -> None)
       | UnivExpr.Coq_npe e0 ->
         let (l, b) = e0 in
         if b
         then None
         else (match l0 with
               | [] -> Some (NoPropLevel.to_level l)
               | _ :: _ -> None))
 end

type sort_family =
| InProp
| InSet
| InType

(** val leb_sort_family : sort_family -> sort_family -> bool **)

let leb_sort_family x y =
  match x with
  | InProp -> true
  | InSet -> (match y with
              | InProp -> false
              | _ -> true)
  | InType -> (match y with
               | InType -> true
               | _ -> false)

(** val universe_family : Universe.t -> sort_family **)

let universe_family u =
  if Universe.is_prop u
  then InProp
  else if Universe.is_small u then InSet else InType

module ConstraintType =
 struct
  type t_ =
  | Lt
  | Le
  | Eq

  (** val t__rect : 'a1 -> 'a1 -> 'a1 -> t_ -> 'a1 **)

  let t__rect f f0 f1 = function
  | Lt -> f
  | Le -> f0
  | Eq -> f1

  (** val t__rec : 'a1 -> 'a1 -> 'a1 -> t_ -> 'a1 **)

  let t__rec f f0 f1 = function
  | Lt -> f
  | Le -> f0
  | Eq -> f1

  type t = t_

  (** val compare : t -> t -> comparison **)

  let compare x y =
    match x with
    | Lt -> (match y with
             | Lt -> Datatypes.Eq
             | _ -> Datatypes.Lt)
    | Le -> (match y with
             | Lt -> Gt
             | Le -> Datatypes.Eq
             | Eq -> Datatypes.Lt)
    | Eq -> (match y with
             | Eq -> Datatypes.Eq
             | _ -> Gt)
 end

module UnivConstraint =
 struct
  type t = (Level.t * ConstraintType.t) * Level.t

  (** val make : Level.t -> ConstraintType.t -> Level.t -> t **)

  let make l1 ct l2 =
    ((l1, ct), l2)

  (** val compare : t -> t -> comparison **)

  let compare pat pat0 =
    let (p, l2) = pat in
    let (l1, t0) = p in
    let (p0, l2') = pat0 in
    let (l1', t') = p0 in
    Pos.switch_Eq
      (Pos.switch_Eq (Level.compare l2 l2') (ConstraintType.compare t0 t'))
      (Level.compare l1 l1')

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let (x0, x1) = x in
    let (p, t0) = y in
    let (x2, x3) = x0 in
    let (t1, t2) = p in
    if match x2 with
       | Level.Coq_lProp ->
         (match t1 with
          | Level.Coq_lProp -> true
          | _ -> false)
       | Level.Coq_lSet -> (match t1 with
                            | Level.Coq_lSet -> true
                            | _ -> false)
       | Level.Level x4 ->
         (match t1 with
          | Level.Level s0 ->
            let rec f s x5 =
              match s with
              | [] -> (match x5 with
                       | [] -> true
                       | _::_ -> false)
              | a::s1 ->
                (match x5 with
                 | [] -> false
                 | a2::s2 ->
                   (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                     (fun x6 x7 x8 x9 x10 x11 x12 x13 ->
                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                       (fun b9 b10 b11 b12 b13 b14 b15 b16 ->
                       if x6
                       then if b9
                            then if x7
                                 then if b10
                                      then if x8
                                           then if b11
                                                then if x9
                                                     then if b12
                                                          then if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                          else false
                                                     else if b12
                                                          then false
                                                          else if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                else false
                                           else if b11
                                                then false
                                                else if x9
                                                     then if b12
                                                          then if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                          else false
                                                     else if b12
                                                          then false
                                                          else if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                      else false
                                 else if b10
                                      then false
                                      else if x8
                                           then if b11
                                                then if x9
                                                     then if b12
                                                          then if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                          else false
                                                     else if b12
                                                          then false
                                                          else if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                else false
                                           else if b11
                                                then false
                                                else if x9
                                                     then if b12
                                                          then if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                          else false
                                                     else if b12
                                                          then false
                                                          else if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                            else false
                       else if b9
                            then false
                            else if x7
                                 then if b10
                                      then if x8
                                           then if b11
                                                then if x9
                                                     then if b12
                                                          then if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                          else false
                                                     else if b12
                                                          then false
                                                          else if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                else false
                                           else if b11
                                                then false
                                                else if x9
                                                     then if b12
                                                          then if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                          else false
                                                     else if b12
                                                          then false
                                                          else if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                      else false
                                 else if b10
                                      then false
                                      else if x8
                                           then if b11
                                                then if x9
                                                     then if b12
                                                          then if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                          else false
                                                     else if b12
                                                          then false
                                                          else if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                else false
                                           else if b11
                                                then false
                                                else if x9
                                                     then if b12
                                                          then if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                          else false
                                                     else if b12
                                                          then false
                                                          else if x10
                                                               then if b13
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                               else if b13
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b16
                                                                    then false
                                                                    else 
                                                                    f s1 s2)
                       a2)
                     a)
            in f x4 s0
          | _ -> false)
       | Level.Var x4 ->
         (match t1 with
          | Level.Var n0 ->
            let rec f n x5 =
              match n with
              | O -> (match x5 with
                      | O -> true
                      | S _ -> false)
              | S n1 -> (match x5 with
                         | O -> false
                         | S n2 -> f n1 n2)
            in f x4 n0
          | _ -> false)
    then (match x3 with
          | ConstraintType.Lt ->
            (match t2 with
             | ConstraintType.Lt ->
               (match x1 with
                | Level.Coq_lProp ->
                  (match t0 with
                   | Level.Coq_lProp -> true
                   | _ -> false)
                | Level.Coq_lSet ->
                  (match t0 with
                   | Level.Coq_lSet -> true
                   | _ -> false)
                | Level.Level x4 ->
                  (match t0 with
                   | Level.Level s0 ->
                     let rec f s x5 =
                       match s with
                       | [] -> (match x5 with
                                | [] -> true
                                | _::_ -> false)
                       | a::s1 ->
                         (match x5 with
                          | [] -> false
                          | a2::s2 ->
                            (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                              (fun x6 x7 x8 x9 x10 x11 x12 x13 ->
                              (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
                                if x6
                                then if b8
                                     then if x7
                                          then if b9
                                               then if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                               else false
                                          else if b9
                                               then false
                                               else if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                     else false
                                else if b8
                                     then false
                                     else if x7
                                          then if b9
                                               then if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                               else false
                                          else if b9
                                               then false
                                               else if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2)
                                a2)
                              a)
                     in f x4 s0
                   | _ -> false)
                | Level.Var x4 ->
                  (match t0 with
                   | Level.Var n0 ->
                     let rec f n x5 =
                       match n with
                       | O -> (match x5 with
                               | O -> true
                               | S _ -> false)
                       | S n1 -> (match x5 with
                                  | O -> false
                                  | S n2 -> f n1 n2)
                     in f x4 n0
                   | _ -> false))
             | _ -> false)
          | ConstraintType.Le ->
            (match t2 with
             | ConstraintType.Le ->
               (match x1 with
                | Level.Coq_lProp ->
                  (match t0 with
                   | Level.Coq_lProp -> true
                   | _ -> false)
                | Level.Coq_lSet ->
                  (match t0 with
                   | Level.Coq_lSet -> true
                   | _ -> false)
                | Level.Level x4 ->
                  (match t0 with
                   | Level.Level s0 ->
                     let rec f s x5 =
                       match s with
                       | [] -> (match x5 with
                                | [] -> true
                                | _::_ -> false)
                       | a::s1 ->
                         (match x5 with
                          | [] -> false
                          | a2::s2 ->
                            (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                              (fun x6 x7 x8 x9 x10 x11 x12 x13 ->
                              (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
                                if x6
                                then if b8
                                     then if x7
                                          then if b9
                                               then if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                               else false
                                          else if b9
                                               then false
                                               else if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                     else false
                                else if b8
                                     then false
                                     else if x7
                                          then if b9
                                               then if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                               else false
                                          else if b9
                                               then false
                                               else if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2)
                                a2)
                              a)
                     in f x4 s0
                   | _ -> false)
                | Level.Var x4 ->
                  (match t0 with
                   | Level.Var n0 ->
                     let rec f n x5 =
                       match n with
                       | O -> (match x5 with
                               | O -> true
                               | S _ -> false)
                       | S n1 -> (match x5 with
                                  | O -> false
                                  | S n2 -> f n1 n2)
                     in f x4 n0
                   | _ -> false))
             | _ -> false)
          | ConstraintType.Eq ->
            (match t2 with
             | ConstraintType.Eq ->
               (match x1 with
                | Level.Coq_lProp ->
                  (match t0 with
                   | Level.Coq_lProp -> true
                   | _ -> false)
                | Level.Coq_lSet ->
                  (match t0 with
                   | Level.Coq_lSet -> true
                   | _ -> false)
                | Level.Level x4 ->
                  (match t0 with
                   | Level.Level s0 ->
                     let rec f s x5 =
                       match s with
                       | [] -> (match x5 with
                                | [] -> true
                                | _::_ -> false)
                       | a::s1 ->
                         (match x5 with
                          | [] -> false
                          | a2::s2 ->
                            (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                              (fun x6 x7 x8 x9 x10 x11 x12 x13 ->
                              (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
                                if x6
                                then if b8
                                     then if x7
                                          then if b9
                                               then if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                               else false
                                          else if b9
                                               then false
                                               else if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                     else false
                                else if b8
                                     then false
                                     else if x7
                                          then if b9
                                               then if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                               else false
                                          else if b9
                                               then false
                                               else if x8
                                                    then if b10
                                                         then if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                         else false
                                                    else if b10
                                                         then false
                                                         else if x9
                                                              then if b11
                                                                   then 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                   else false
                                                              else if b11
                                                                   then false
                                                                   else 
                                                                    if x10
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b12
                                                                    then false
                                                                    else 
                                                                    if x11
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b13
                                                                    then false
                                                                    else 
                                                                    if x12
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b14
                                                                    then false
                                                                    else 
                                                                    if x13
                                                                    then 
                                                                    if b15
                                                                    then 
                                                                    f s1 s2
                                                                    else false
                                                                    else 
                                                                    if b15
                                                                    then false
                                                                    else 
                                                                    f s1 s2)
                                a2)
                              a)
                     in f x4 s0
                   | _ -> false)
                | Level.Var x4 ->
                  (match t0 with
                   | Level.Var n0 ->
                     let rec f n x5 =
                       match n with
                       | O -> (match x5 with
                               | O -> true
                               | S _ -> false)
                       | S n1 -> (match x5 with
                                  | O -> false
                                  | S n2 -> f n1 n2)
                     in f x4 n0
                   | _ -> false))
             | _ -> false))
    else false
 end

module ConstraintSet = MakeWithLeibniz(UnivConstraint)

module Instance =
 struct
  type t = Level.t list
 end

module UContext =
 struct
  type t = Instance.t * ConstraintSet.t
 end

module AUContext =
 struct
  type t = name list * ConstraintSet.t

  (** val repr : t -> UContext.t **)

  let repr = function
  | (u, cst) -> ((mapi (fun i _ -> Level.Var i) u), cst)

  (** val levels : t -> LevelSet.t **)

  let levels uctx =
    LevelSetProp.of_list (fst (repr uctx))
 end

module ContextSet =
 struct
  type t = LevelSet.t * ConstraintSet.t

  (** val empty : t **)

  let empty =
    (LevelSet.empty, ConstraintSet.empty)
 end

module Variance =
 struct
  type t =
  | Irrelevant
  | Covariant
  | Invariant
 end

type universes_decl =
| Monomorphic_ctx of ContextSet.t
| Polymorphic_ctx of AUContext.t

(** val monomorphic_udecl : universes_decl -> ContextSet.t **)

let monomorphic_udecl = function
| Monomorphic_ctx ctx -> ctx
| Polymorphic_ctx _ -> ContextSet.empty

(** val levels_of_udecl : universes_decl -> LevelSet.t **)

let levels_of_udecl = function
| Monomorphic_ctx ctx -> fst ctx
| Polymorphic_ctx ctx -> AUContext.levels ctx

(** val constraints_of_udecl : universes_decl -> ConstraintSet.t **)

let constraints_of_udecl = function
| Monomorphic_ctx ctx -> snd ctx
| Polymorphic_ctx ctx -> snd (AUContext.repr ctx)

type 'a coq_UnivSubst = Instance.t -> 'a -> 'a

(** val subst_instance_level : Level.t coq_UnivSubst **)

let subst_instance_level u l = match l with
| Level.Var n -> nth n u Level.Coq_lSet
| _ -> l

(** val subst_instance_cstr : UnivConstraint.t coq_UnivSubst **)

let subst_instance_cstr u c =
  (((subst_instance_level u (fst (fst c))), (snd (fst c))),
    (subst_instance_level u (snd c)))

(** val subst_instance_cstrs : ConstraintSet.t coq_UnivSubst **)

let subst_instance_cstrs u ctrs =
  ConstraintSet.fold (fun c -> ConstraintSet.add (subst_instance_cstr u c))
    ctrs ConstraintSet.empty

(** val subst_instance_level_expr : UnivExpr.t coq_UnivSubst **)

let subst_instance_level_expr u e = match e with
| UnivExpr.Coq_lProp -> UnivExpr.Coq_lProp
| UnivExpr.Coq_npe e0 ->
  let (t0, b) = e0 in
  (match t0 with
   | NoPropLevel.Var n ->
     (match nth_error u n with
      | Some l ->
        (match NoPropLevel.of_level l with
         | Some l0 -> UnivExpr.Coq_npe (l0, b)
         | None -> if b then UnivExpr.type1 else UnivExpr.Coq_lProp)
      | None -> UnivExpr.Coq_npe (NoPropLevel.Coq_lSet, b))
   | _ -> e)

(** val subst_instance_univ : Universe.t coq_UnivSubst **)

let subst_instance_univ u s =
  Universe.map (subst_instance_level_expr u) s

(** val subst_instance_instance : Instance.t coq_UnivSubst **)

let subst_instance_instance u u' =
  map (subst_instance_level u) u'

(** val closedu_level : nat -> Level.t -> bool **)

let closedu_level k = function
| Level.Var n -> Nat.ltb n k
| _ -> true

(** val closedu_level_expr : nat -> UnivExpr.t -> bool **)

let closedu_level_expr k s =
  closedu_level k (UnivExpr.get_level s)

(** val closedu_universe : nat -> Universe.t -> bool **)

let closedu_universe k u =
  UnivExprSet.for_all (closedu_level_expr k) (Universe.t_set u)

(** val closedu_instance : nat -> Instance.t -> bool **)

let closedu_instance k u =
  forallb (closedu_level k) u

(** val string_of_level : Level.t -> char list **)

let string_of_level = function
| Level.Coq_lProp -> 'P'::('r'::('o'::('p'::[])))
| Level.Coq_lSet -> 'S'::('e'::('t'::[]))
| Level.Level s -> s
| Level.Var n -> append ('V'::('a'::('r'::[]))) (string_of_nat n)

(** val string_of_level_expr : UnivExpr.t -> char list **)

let string_of_level_expr = function
| UnivExpr.Coq_lProp -> 'P'::('r'::('o'::('p'::[])))
| UnivExpr.Coq_npe e0 ->
  let (l, b) = e0 in
  append (string_of_level (NoPropLevel.to_level l))
    (if b then '+'::('1'::[]) else [])

(** val string_of_sort : Universe.t -> char list **)

let string_of_sort u =
  string_of_list string_of_level_expr
    (UnivExprSet.elements (Universe.t_set u))

(** val string_of_universe_instance : Level.t list -> char list **)

let string_of_universe_instance u =
  string_of_list string_of_level u

(** val print_universe_instance : Level.t list -> char list **)

let print_universe_instance u = match u with
| [] -> []
| _ :: _ ->
  append ('@'::('{'::[]))
    (append (print_list string_of_level (' '::[]) u) ('}'::[]))

(** val print_lset : LevelSet.t -> char list **)

let print_lset t0 =
  print_list string_of_level (' '::[]) (LevelSet.elements t0)

(** val print_constraint_type : ConstraintType.t_ -> char list **)

let print_constraint_type = function
| ConstraintType.Lt -> '<'::[]
| ConstraintType.Le -> '<'::('='::[])
| ConstraintType.Eq -> '='::[]

(** val print_constraint_set : ConstraintSet.t -> char list **)

let print_constraint_set t0 =
  print_list (fun pat ->
    let (y, l2) = pat in
    let (l1, d) = y in
    append (string_of_level l1)
      (append (' '::[])
        (append (print_constraint_type d)
          (append (' '::[]) (string_of_level l2)))))
    (' '::('/'::('\\'::(' '::[])))) (ConstraintSet.elements t0)
