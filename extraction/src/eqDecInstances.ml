open Classes0
open Datatypes

(** val nat_eqdec : nat -> nat -> nat dec_eq **)

let rec nat_eqdec n y =
  match n with
  | O -> (match y with
          | O -> true
          | S _ -> false)
  | S n0 -> (match y with
             | O -> false
             | S y0 -> nat_eqdec n0 y0)
