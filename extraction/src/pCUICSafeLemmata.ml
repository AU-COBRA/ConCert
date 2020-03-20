open PCUICNormal

(** val nodelta_flags : RedFlags.t **)

let nodelta_flags =
  { RedFlags.beta = true; RedFlags.iota = true; RedFlags.zeta = true;
    RedFlags.delta = false; RedFlags.fix_ = true; RedFlags.cofix_ = true }
