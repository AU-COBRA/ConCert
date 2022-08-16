open Datatypes

(** val on_snd : ('a2 -> 'a3) -> ('a1 * 'a2) -> 'a1 * 'a3 **)

let on_snd f p =
  ((fst p), (f (snd p)))

(** val test_snd : ('a2 -> bool) -> ('a1 * 'a2) -> bool **)

let test_snd f p =
  f (snd p)
