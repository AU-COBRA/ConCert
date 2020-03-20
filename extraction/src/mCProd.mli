open Datatypes

val on_snd : ('a2 -> 'a3) -> ('a1 * 'a2) -> 'a1 * 'a3

val test_snd : ('a2 -> bool) -> ('a1 * 'a2) -> bool

val on_pi2 : ('a2 -> 'a2) -> (('a1 * 'a2) * 'a3) -> ('a1 * 'a2) * 'a3
