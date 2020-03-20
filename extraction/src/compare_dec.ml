open Datatypes

(** val le_lt_dec : nat -> nat -> bool **)

let rec le_lt_dec n m =
  match n with
  | O -> true
  | S n0 -> (match m with
             | O -> false
             | S m0 -> le_lt_dec n0 m0)

(** val le_gt_dec : nat -> nat -> bool **)

let le_gt_dec =
  le_lt_dec

(** val le_dec : nat -> nat -> bool **)

let le_dec =
  le_gt_dec
