open Datatypes
open MCCompare
open MCString
open String0

type ident = char list

type kername = char list

type name =
| Coq_nAnon
| Coq_nNamed of ident

(** val string_of_name : name -> char list **)

let string_of_name = function
| Coq_nAnon -> 'A'::('n'::('o'::('n'::('y'::('m'::('o'::('u'::('s'::[]))))))))
| Coq_nNamed n -> n

type inductive = { inductive_mind : kername; inductive_ind : nat }

(** val string_of_inductive : inductive -> char list **)

let string_of_inductive i =
  append i.inductive_mind (append (','::[]) (string_of_nat i.inductive_ind))

type projection = (inductive * nat) * nat

type 'term def = { dname : name; dtype : 'term; dbody : 'term; rarg : nat }

(** val string_of_def : ('a1 -> char list) -> 'a1 def -> char list **)

let string_of_def f def0 =
  append ('('::[])
    (append (string_of_name def0.dname)
      (append (','::[])
        (append (f def0.dtype)
          (append (','::[])
            (append (f def0.dbody)
              (append (','::[]) (append (string_of_nat def0.rarg) (')'::[]))))))))

(** val print_def :
    ('a1 -> char list) -> ('a1 -> char list) -> 'a1 def -> char list **)

let print_def f g def0 =
  append (string_of_name def0.dname)
    (append
      (' '::('{'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::[]))))))))))
      (append (string_of_nat def0.rarg)
        (append (' '::('}'::[]))
          (append (' '::(':'::(' '::[])))
            (append (f def0.dtype)
              (append (' '::(':'::('='::(' '::[]))))
                (append nl (g def0.dbody))))))))

(** val map_def : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 def -> 'a2 def **)

let map_def tyf bodyf d =
  { dname = d.dname; dtype = (tyf d.dtype); dbody = (bodyf d.dbody); rarg =
    d.rarg }

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

(** val ident_eq : ident -> ident -> bool **)

let ident_eq x y =
  match string_compare x y with
  | Eq -> true
  | _ -> false

(** val eq_constant : char list -> char list -> bool **)

let eq_constant =
  eq_string

(** val test_def : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 def -> bool **)

let test_def tyf bodyf d =
  (&&) (tyf d.dtype) (bodyf d.dbody)
