
type checker_flags = { check_univs : bool; allow_cofix : bool;
                       prop_sub_type : bool; indices_matter : bool }

(** val extraction_checker_flags : checker_flags **)

let extraction_checker_flags =
  { check_univs = true; allow_cofix = false; prop_sub_type = false;
    indices_matter = false }
