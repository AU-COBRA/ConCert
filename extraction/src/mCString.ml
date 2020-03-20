open Ascii
open Datatypes
open MCCompare
open String0

(** val nl : char list **)

let nl =
  (ascii_of_nat (S (S (S (S (S (S (S (S (S (S O)))))))))))::[]

(** val string_of_list_aux :
    ('a1 -> char list) -> char list -> 'a1 list -> char list **)

let rec string_of_list_aux f sep = function
| [] -> []
| a :: l0 ->
  (match l0 with
   | [] -> f a
   | _ :: _ -> append (f a) (append sep (string_of_list_aux f sep l0)))

(** val string_of_list : ('a1 -> char list) -> 'a1 list -> char list **)

let string_of_list f l =
  append ('['::[]) (append (string_of_list_aux f (','::[]) l) (']'::[]))

(** val print_list :
    ('a1 -> char list) -> char list -> 'a1 list -> char list **)

let print_list =
  string_of_list_aux

(** val parens : bool -> char list -> char list **)

let parens top s =
  if top then s else append ('('::[]) (append s (')'::[]))

(** val string_of_nat : nat -> char list **)

let string_of_nat = function
| O -> '0'::[]
| S n0 ->
  (match n0 with
   | O -> '1'::[]
   | S n1 ->
     (match n1 with
      | O -> '2'::[]
      | S n2 ->
        (match n2 with
         | O -> '3'::[]
         | S n3 ->
           (match n3 with
            | O -> '4'::[]
            | S n4 ->
              (match n4 with
               | O -> '5'::[]
               | S n5 ->
                 (match n5 with
                  | O -> '6'::[]
                  | S n6 ->
                    (match n6 with
                     | O -> '7'::[]
                     | S n7 ->
                       (match n7 with
                        | O -> '8'::[]
                        | S n8 ->
                          (match n8 with
                           | O -> '9'::[]
                           | S n9 ->
                             (match n9 with
                              | O -> '1'::('0'::[])
                              | S n10 ->
                                (match n10 with
                                 | O -> '1'::('1'::[])
                                 | S n11 ->
                                   (match n11 with
                                    | O -> '1'::('2'::[])
                                    | S n12 ->
                                      (match n12 with
                                       | O -> '1'::('3'::[])
                                       | S n13 ->
                                         (match n13 with
                                          | O -> '1'::('4'::[])
                                          | S n14 ->
                                            (match n14 with
                                             | O -> '1'::('5'::[])
                                             | S n15 ->
                                               (match n15 with
                                                | O -> '1'::('6'::[])
                                                | S n16 ->
                                                  (match n16 with
                                                   | O -> '1'::('7'::[])
                                                   | S n17 ->
                                                     (match n17 with
                                                      | O -> '1'::('8'::[])
                                                      | S n18 ->
                                                        (match n18 with
                                                         | O -> '1'::('9'::[])
                                                         | S n19 ->
                                                           (match n19 with
                                                            | O ->
                                                              '2'::('0'::[])
                                                            | S n20 ->
                                                              (match n20 with
                                                               | O ->
                                                                 '2'::('1'::[])
                                                               | S n21 ->
                                                                 (match n21 with
                                                                  | O ->
                                                                    '2'::('2'::[])
                                                                  | S n22 ->
                                                                    (match n22 with
                                                                    | O ->
                                                                    '2'::('3'::[])
                                                                    | S n23 ->
                                                                    (match n23 with
                                                                    | O ->
                                                                    '2'::('4'::[])
                                                                    | S n24 ->
                                                                    (match n24 with
                                                                    | O ->
                                                                    '2'::('5'::[])
                                                                    | S n25 ->
                                                                    (match n25 with
                                                                    | O ->
                                                                    '2'::('6'::[])
                                                                    | S n26 ->
                                                                    (match n26 with
                                                                    | O ->
                                                                    '2'::('7'::[])
                                                                    | S n27 ->
                                                                    (match n27 with
                                                                    | O ->
                                                                    '2'::('8'::[])
                                                                    | S n28 ->
                                                                    (match n28 with
                                                                    | O ->
                                                                    '2'::('9'::[])
                                                                    | S n29 ->
                                                                    (match n29 with
                                                                    | O ->
                                                                    '3'::('0'::[])
                                                                    | S n30 ->
                                                                    (match n30 with
                                                                    | O ->
                                                                    '3'::('1'::[])
                                                                    | S n31 ->
                                                                    (match n31 with
                                                                    | O ->
                                                                    '3'::('2'::[])
                                                                    | S n32 ->
                                                                    (match n32 with
                                                                    | O ->
                                                                    '3'::('3'::[])
                                                                    | S n33 ->
                                                                    (match n33 with
                                                                    | O ->
                                                                    '3'::('4'::[])
                                                                    | S n34 ->
                                                                    (match n34 with
                                                                    | O ->
                                                                    '3'::('5'::[])
                                                                    | S n35 ->
                                                                    (match n35 with
                                                                    | O ->
                                                                    '3'::('6'::[])
                                                                    | S n36 ->
                                                                    (match n36 with
                                                                    | O ->
                                                                    '3'::('7'::[])
                                                                    | S n37 ->
                                                                    (match n37 with
                                                                    | O ->
                                                                    '3'::('8'::[])
                                                                    | S n38 ->
                                                                    (match n38 with
                                                                    | O ->
                                                                    '3'::('9'::[])
                                                                    | S n39 ->
                                                                    (match n39 with
                                                                    | O ->
                                                                    '4'::('0'::[])
                                                                    | S n40 ->
                                                                    (match n40 with
                                                                    | O ->
                                                                    '4'::('1'::[])
                                                                    | S n41 ->
                                                                    (match n41 with
                                                                    | O ->
                                                                    '4'::('2'::[])
                                                                    | S n42 ->
                                                                    (match n42 with
                                                                    | O ->
                                                                    '4'::('3'::[])
                                                                    | S n43 ->
                                                                    (match n43 with
                                                                    | O ->
                                                                    '4'::('4'::[])
                                                                    | S n44 ->
                                                                    (match n44 with
                                                                    | O ->
                                                                    '4'::('5'::[])
                                                                    | S n45 ->
                                                                    (match n45 with
                                                                    | O ->
                                                                    '4'::('6'::[])
                                                                    | S n46 ->
                                                                    (match n46 with
                                                                    | O ->
                                                                    '4'::('7'::[])
                                                                    | S n47 ->
                                                                    (match n47 with
                                                                    | O ->
                                                                    '4'::('8'::[])
                                                                    | S n48 ->
                                                                    (match n48 with
                                                                    | O ->
                                                                    '4'::('9'::[])
                                                                    | S _ ->
                                                                    't'::('o'::('d'::('o'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::('_'::('o'::('f'::('_'::('n'::('a'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eq_string : char list -> char list -> bool **)

let eq_string s s' =
  match string_compare s s' with
  | Eq -> true
  | _ -> false
