
(** val map_option_out : 'a1 option list -> 'a1 list option **)

let rec map_option_out = function
| [] -> Some []
| hd :: tl ->
  (match hd with
   | Some hd0 ->
     (match map_option_out tl with
      | Some tl0 -> Some (hd0 :: tl0)
      | None -> None)
   | None -> None)
