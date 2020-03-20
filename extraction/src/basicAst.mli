open Datatypes
open MCCompare
open MCString
open String0

type ident = char list

type kername = char list

type name =
| Coq_nAnon
| Coq_nNamed of ident

val string_of_name : name -> char list

type inductive = { inductive_mind : kername; inductive_ind : nat }

val string_of_inductive : inductive -> char list

type projection = (inductive * nat) * nat

type 'term def = { dname : name; dtype : 'term; dbody : 'term; rarg : nat }

val string_of_def : ('a1 -> char list) -> 'a1 def -> char list

val print_def :
  ('a1 -> char list) -> ('a1 -> char list) -> 'a1 def -> char list

val map_def : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 def -> 'a2 def

type 'term mfixpoint = 'term def list

type cast_kind =
| VmCast
| NativeCast
| Cast
| RevertCast

type recursivity_kind =
| Finite
| CoFinite
| BiFinite

val ident_eq : ident -> ident -> bool

val eq_constant : char list -> char list -> bool

val test_def : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 def -> bool
