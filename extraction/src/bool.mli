
type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

val eqb_spec : bool -> bool -> reflect
