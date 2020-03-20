open Datatypes

type ('a, 'b) isEquiv = { equiv : ('a -> 'b); equiv_inv : ('b -> 'a) }

val equiv : ('a1, 'a2) isEquiv -> 'a1 -> 'a2

val equiv_inv : ('a1, 'a2) isEquiv -> 'a2 -> 'a1

type coq_Fuel = nat

val fuel : coq_Fuel -> nat

val todo : char list -> 'a1
