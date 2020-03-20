
type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

(** val eqb_spec : bool -> bool -> reflect **)

let eqb_spec b b' =
  if b
  then if b' then ReflectT else ReflectF
  else if b' then ReflectF else ReflectT
