
type 'a dec_eq = bool

type 'a coq_EqDec = 'a -> 'a -> bool

(** val eq_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let eq_dec eqDec =
  eqDec
