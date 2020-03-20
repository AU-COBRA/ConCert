open BinPos
open Datatypes

module N =
 struct
  (** val of_nat : nat -> int **)

  let of_nat = function
  | O -> 0
  | S n' -> (Pos.of_succ_nat n')
 end
