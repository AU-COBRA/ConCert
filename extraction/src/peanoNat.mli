open Bool
open Datatypes

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val eq_dec : nat -> nat -> bool

  val eqb_spec : nat -> nat -> reflect
 end
