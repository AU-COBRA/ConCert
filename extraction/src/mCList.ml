open Datatypes

(** val mapi_rec : (nat -> 'a1 -> 'a2) -> 'a1 list -> nat -> 'a2 list **)

let rec mapi_rec f l n =
  match l with
  | [] -> []
  | hd :: tl -> (f n hd) :: (mapi_rec f tl (S n))

(** val mapi : (nat -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let mapi f l =
  mapi_rec f l O

(** val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rev_map f l =
  let rec aux l0 acc =
    match l0 with
    | [] -> acc
    | x :: l1 -> aux l1 ((f x) :: acc)
  in aux l []

(** val chop : nat -> 'a1 list -> 'a1 list * 'a1 list **)

let rec chop n l =
  match n with
  | O -> ([], l)
  | S n0 ->
    (match l with
     | [] -> ([], [])
     | hd :: tl -> let (l0, r) = chop n0 tl in ((hd :: l0), r))
