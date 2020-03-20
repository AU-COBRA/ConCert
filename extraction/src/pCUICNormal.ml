
module RedFlags =
 struct
  type t = { beta : bool; iota : bool; zeta : bool; delta : bool;
             fix_ : bool; cofix_ : bool }

  (** val beta : t -> bool **)

  let beta t0 =
    t0.beta

  (** val iota : t -> bool **)

  let iota t0 =
    t0.iota

  (** val zeta : t -> bool **)

  let zeta t0 =
    t0.zeta

  (** val delta : t -> bool **)

  let delta t0 =
    t0.delta

  (** val fix_ : t -> bool **)

  let fix_ t0 =
    t0.fix_

  (** val default : t **)

  let default =
    { beta = true; iota = true; zeta = true; delta = true; fix_ = true;
      cofix_ = true }
 end
