open BinNat
open Bool
open Datatypes

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val eqb_spec : char -> char -> reflect **)

let eqb_spec a b =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
      match eqb_spec b0 b8 with
      | ReflectT ->
        (match eqb_spec b1 b9 with
         | ReflectT ->
           (match eqb_spec b2 b10 with
            | ReflectT ->
              (match eqb_spec b3 b11 with
               | ReflectT ->
                 (match eqb_spec b4 b12 with
                  | ReflectT ->
                    (match eqb_spec b5 b13 with
                     | ReflectT ->
                       (match eqb_spec b6 b14 with
                        | ReflectT -> eqb_spec b7 b15
                        | ReflectF -> ReflectF)
                     | ReflectF -> ReflectF)
                  | ReflectF -> ReflectF)
               | ReflectF -> ReflectF)
            | ReflectF -> ReflectF)
         | ReflectF -> ReflectF)
      | ReflectF -> ReflectF)
      b)
    a

(** val ascii_of_pos : int -> char **)

let ascii_of_pos =
  let rec loop n p =
    match n with
    | O -> zero
    | S n' ->
      ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
         (fun p' -> shift true (loop n' p'))
         (fun p' -> shift false (loop n' p'))
         (fun _ -> one)
         p)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : int -> char **)

let ascii_of_N n =
  (fun f0 fp n -> if n=0 then f0 () else fp n)
    (fun _ -> zero)
    (fun p -> ascii_of_pos p)
    n

(** val ascii_of_nat : nat -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)


