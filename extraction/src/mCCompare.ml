open Datatypes

(** val bool_compare : bool -> bool -> comparison **)

let bool_compare x y =
  if x then if y then Eq else Gt else if y then Lt else Eq

(** val ascii_compare : char -> char -> comparison **)

let ascii_compare x y =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a b c d e f g h ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun a' b' c' d' e' f' g' h' ->
      match match match match match match match bool_compare a a' with
                                          | Eq -> bool_compare b b'
                                          | x0 -> x0 with
                                    | Eq -> bool_compare c c'
                                    | x0 -> x0 with
                              | Eq -> bool_compare d d'
                              | x0 -> x0 with
                        | Eq -> bool_compare e e'
                        | x0 -> x0 with
                  | Eq -> bool_compare f f'
                  | x0 -> x0 with
            | Eq -> bool_compare g g'
            | x0 -> x0 with
      | Eq -> bool_compare h h'
      | x0 -> x0)
      y)
    x

(** val string_compare : char list -> char list -> comparison **)

let rec string_compare x y =
  match x with
  | [] -> (match y with
           | [] -> Eq
           | _::_ -> Lt)
  | a::s ->
    (match y with
     | [] -> Gt
     | b::s' ->
       (match ascii_compare a b with
        | Eq -> string_compare s s'
        | x0 -> x0))
