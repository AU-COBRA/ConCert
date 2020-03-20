
module RedFlags :
 sig
  type t = { beta : bool; iota : bool; zeta : bool; delta : bool;
             fix_ : bool; cofix_ : bool }

  val beta : t -> bool

  val iota : t -> bool

  val zeta : t -> bool

  val delta : t -> bool

  val fix_ : t -> bool

  val default : t
 end
