open Datatypes

val mapi_rec : (nat -> 'a1 -> 'a2) -> 'a1 list -> nat -> 'a2 list

val mapi : (nat -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list

val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val chop : nat -> 'a1 list -> 'a1 list * 'a1 list
