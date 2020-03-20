open BasicAst
open Datatypes
open EAst
open EAstUtils
open ELiftSubst
open List0

(** val lookup_env : global_declarations -> ident -> global_decl option **)

let rec lookup_env _UU03a3_ id =
  match _UU03a3_ with
  | [] -> None
  | hd :: tl ->
    if ident_eq id (fst hd) then Some (snd hd) else lookup_env tl id

(** val fix_subst : term mfixpoint -> term list **)

let fix_subst l =
  let rec aux = function
  | O -> []
  | S n0 -> (Coq_tFix (l, n0)) :: (aux n0)
  in aux (length l)

(** val unfold_fix : term mfixpoint -> nat -> (nat * term) option **)

let unfold_fix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (subst (fix_subst mfix) O d.dbody))
  | None -> None

(** val cofix_subst : term mfixpoint -> term list **)

let cofix_subst l =
  let rec aux = function
  | O -> []
  | S n0 -> (Coq_tCoFix (l, n0)) :: (aux n0)
  in aux (length l)

(** val unfold_cofix : term mfixpoint -> nat -> (nat * term) option **)

let unfold_cofix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (subst (cofix_subst mfix) O d.dbody))
  | None -> None

(** val is_constructor : nat -> term list -> bool **)

let is_constructor n ts =
  match nth_error ts n with
  | Some a ->
    let (f, _) = decompose_app a in
    (match f with
     | Coq_tConstruct (_, _) -> true
     | _ -> false)
  | None -> false

(** val is_constructor_or_box : nat -> term list -> bool **)

let is_constructor_or_box n ts =
  match nth_error ts n with
  | Some a ->
    (match a with
     | Coq_tBox -> true
     | _ ->
       let (f, _) = decompose_app a in
       (match f with
        | Coq_tConstruct (_, _) -> true
        | _ -> false))
  | None -> false

(** val tDummy : term **)

let tDummy =
  Coq_tVar []

(** val iota_red : nat -> nat -> term list -> (nat * term) list -> term **)

let iota_red npar c args brs =
  mkApps (snd (nth c brs (O, tDummy))) (skipn npar args)
