
type ('a, 'p) coq_All =
| All_nil
| All_cons of 'a * 'a list * 'p * ('a, 'p) coq_All

type ('a, 'b, 'r) coq_All2 =
| All2_nil
| All2_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2

(** val forallb2 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec forallb2 f l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | hd :: tl ->
    (match l' with
     | [] -> false
     | hd' :: tl' -> (&&) (f hd hd') (forallb2 f tl tl'))
