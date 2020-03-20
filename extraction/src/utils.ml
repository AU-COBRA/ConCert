open Datatypes

type ('a, 'b) isEquiv = { equiv : ('a -> 'b); equiv_inv : ('b -> 'a) }

(** val equiv : ('a1, 'a2) isEquiv -> 'a1 -> 'a2 **)

let equiv i =
  i.equiv

(** val equiv_inv : ('a1, 'a2) isEquiv -> 'a2 -> 'a1 **)

let equiv_inv i =
  i.equiv_inv

type coq_Fuel = nat

(** val fuel : coq_Fuel -> nat **)

let fuel fuel0 =
  fuel0

(** val todo : char list -> 'a1 **)

let todo = fun s -> failwith (String.concat "" (List.map (String.make 1) s))
