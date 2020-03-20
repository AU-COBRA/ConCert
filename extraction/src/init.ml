
(** val pr1 : ('a1*'a2) -> 'a1 **)

let pr1 = function
| pr3,_ -> pr3

(** val pr2 : ('a1*'a2) -> 'a2 **)

let pr2 = function
| _,pr3 -> pr3
