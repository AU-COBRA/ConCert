open Ascii
open Datatypes
open MCCompare
open String0

val nl : char list

val string_of_list_aux :
  ('a1 -> char list) -> char list -> 'a1 list -> char list

val string_of_list : ('a1 -> char list) -> 'a1 list -> char list

val print_list : ('a1 -> char list) -> char list -> 'a1 list -> char list

val parens : bool -> char list -> char list

val string_of_nat : nat -> char list

val eq_string : char list -> char list -> bool
