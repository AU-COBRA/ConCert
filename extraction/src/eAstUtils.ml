open BasicAst
open Datatypes
open EAst
open MCString
open String0

(** val decompose_app_rec : term -> term list -> term * term list **)

let rec decompose_app_rec t l =
  match t with
  | Coq_tApp (f, a) -> decompose_app_rec f (a :: l)
  | _ -> (t, l)

(** val decompose_app : term -> term * term list **)

let decompose_app f =
  decompose_app_rec f []

(** val string_of_def : ('a1 -> char list) -> 'a1 def -> char list **)

let string_of_def f def0 =
  append ('('::[])
    (append (string_of_name def0.dname)
      (append (','::[])
        (append (f def0.dbody)
          (append (','::[]) (append (string_of_nat def0.rarg) (')'::[]))))))

(** val string_of_term : term -> char list **)

let rec string_of_term = function
| Coq_tBox -> '\226'::('\136'::('\142'::[]))
| Coq_tRel n ->
  append ('R'::('e'::('l'::('('::[])))) (append (string_of_nat n) (')'::[]))
| Coq_tVar n -> append ('V'::('a'::('r'::('('::[])))) (append n (')'::[]))
| Coq_tEvar (ev, _) ->
  append ('E'::('v'::('a'::('r'::('('::[])))))
    (append (string_of_nat ev) (append ('['::(']'::[])) (')'::[])))
| Coq_tLambda (na, t0) ->
  append ('L'::('a'::('m'::('b'::('d'::('a'::('('::[])))))))
    (append (string_of_name (aname_to_name na))
      (append (','::[]) (append (string_of_term t0) (')'::[]))))
| Coq_tLetIn (na, b, t0) ->
  append ('L'::('e'::('t'::('I'::('n'::('('::[]))))))
    (append (string_of_name (aname_to_name na))
      (append (','::[])
        (append (string_of_term b)
          (append (','::[]) (append (string_of_term t0) (')'::[]))))))
| Coq_tApp (f, l) ->
  append ('A'::('p'::('p'::('('::[]))))
    (append (string_of_term f)
      (append (','::[]) (append (string_of_term l) (')'::[]))))
| Coq_tConst c ->
  append ('C'::('o'::('n'::('s'::('t'::('('::[])))))) (append c (')'::[]))
| Coq_tConstruct (i, n) ->
  append
    ('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('('::[]))))))))))
    (append (string_of_inductive i)
      (append (','::[]) (append (string_of_nat n) (')'::[]))))
| Coq_tCase (p, t0, brs) ->
  let (ind, i) = p in
  append ('C'::('a'::('s'::('e'::('('::[])))))
    (append (string_of_inductive ind)
      (append (','::[])
        (append (string_of_nat i)
          (append (','::[])
            (append (string_of_term t0)
              (append (','::[])
                (append
                  (string_of_list (fun b -> string_of_term (snd b)) brs)
                  (')'::[]))))))))
| Coq_tProj (p, c) ->
  let (p0, k) = p in
  let (ind, i) = p0 in
  append ('P'::('r'::('o'::('j'::('('::[])))))
    (append (string_of_inductive ind)
      (append (','::[])
        (append (string_of_nat i)
          (append (','::[])
            (append (string_of_nat k)
              (append (','::[]) (append (string_of_term c) (')'::[]))))))))
| Coq_tFix (l, n) ->
  append ('F'::('i'::('x'::('('::[]))))
    (append (string_of_list (string_of_def string_of_term) l)
      (append (','::[]) (append (string_of_nat n) (')'::[]))))
| Coq_tCoFix (l, n) ->
  append ('C'::('o'::('F'::('i'::('x'::('('::[]))))))
    (append (string_of_list (string_of_def string_of_term) l)
      (append (','::[]) (append (string_of_nat n) (')'::[]))))
