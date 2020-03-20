open BasicAst
open Datatypes
open EAst
open EAstUtils
open ETyping
open List0
open MCString
open Nat0
open String0

(** val print_def : ('a1 -> char list) -> 'a1 def -> char list **)

let print_def f def0 =
  append (string_of_name def0.dname)
    (append
      (' '::('{'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::[]))))))))))
      (append (string_of_nat def0.rarg)
        (append (' '::('}'::[]))
          (append (' '::(':'::('='::(' '::[])))) (append nl (f def0.dbody))))))

(** val print_defs :
    (context -> bool -> bool -> term -> char list) -> context_decl list ->
    term mfixpoint -> char list **)

let print_defs print_term0 _UU0393_ defs =
  let ctx' = map (fun d -> { decl_name = d.dname; decl_body = None }) defs in
  print_list (print_def (print_term0 (app ctx' _UU0393_) true false))
    (append nl (' '::('w'::('i'::('t'::('h'::(' '::[]))))))) defs

(** val lookup_ind_decl :
    global_context -> ident -> nat -> one_inductive_body option **)

let lookup_ind_decl _UU03a3_ ind i =
  match lookup_env _UU03a3_ ind with
  | Some g ->
    (match g with
     | ConstantDecl _ -> None
     | InductiveDecl m ->
       let { ind_npars = _; ind_bodies = l } = m in nth_error l i)
  | None -> None

(** val is_fresh : context -> ident -> bool **)

let is_fresh _UU0393_ id =
  forallb (fun decl ->
    match decl.decl_name with
    | Coq_nAnon -> true
    | Coq_nNamed id' -> negb (ident_eq id id')) _UU0393_

(** val name_from_term : term -> char list **)

let rec name_from_term = function
| Coq_tRel _ -> 'H'::[]
| Coq_tVar _ -> 'H'::[]
| Coq_tEvar (_, _) -> 'H'::[]
| Coq_tLambda (_, _) -> 'f'::[]
| Coq_tLetIn (_, _, t') -> name_from_term t'
| Coq_tApp (f, _) -> name_from_term f
| Coq_tConst _ -> 'x'::[]
| _ -> 'U'::[]

(** val fresh_id_from : context -> nat -> char list -> char list **)

let fresh_id_from _UU0393_ n id =
  let rec aux i = match i with
  | O -> id
  | S i' ->
    let id' = append id (string_of_nat (sub n i)) in
    if is_fresh _UU0393_ id' then id' else aux i'
  in aux n

(** val fresh_name : context -> name -> term -> name **)

let fresh_name _UU0393_ na t =
  let id = match na with
           | Coq_nAnon -> name_from_term t
           | Coq_nNamed id -> id
  in
  if is_fresh _UU0393_ id
  then Coq_nNamed id
  else Coq_nNamed
         (fresh_id_from _UU0393_ (S (S (S (S (S (S (S (S (S (S O)))))))))) id)

(** val print_term :
    global_context -> context -> bool -> bool -> term -> char list **)

let rec print_term _UU03a3_ _UU0393_ top inapp t = match t with
| Coq_tBox -> '\226'::('\136'::('\142'::[]))
| Coq_tRel n ->
  (match nth_error _UU0393_ n with
   | Some c ->
     let { decl_name = na; decl_body = _ } = c in
     (match na with
      | Coq_nAnon ->
        append
          ('A'::('n'::('o'::('n'::('y'::('m'::('o'::('u'::('s'::(' '::('('::[])))))))))))
          (append (string_of_nat n) (')'::[]))
      | Coq_nNamed id -> id)
   | None ->
     append
       ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('R'::('e'::('l'::('('::[])))))))))))
       (append (string_of_nat n) (')'::[])))
| Coq_tVar n -> append ('V'::('a'::('r'::('('::[])))) (append n (')'::[]))
| Coq_tEvar (ev, _) ->
  append ('E'::('v'::('a'::('r'::('('::[])))))
    (append (string_of_nat ev) (append ('['::(']'::[])) (')'::[])))
| Coq_tLambda (na, body) ->
  let na' = fresh_name _UU0393_ (aname_to_name na) t in
  parens top
    (append ('f'::('u'::('n'::(' '::[]))))
      (append (string_of_name na')
        (append (' '::('='::('>'::(' '::[]))))
          (print_term _UU03a3_ ((vass na') :: _UU0393_) true false body))))
| Coq_tLetIn (na, def0, body) ->
  let na' = fresh_name _UU0393_ (aname_to_name na) t in
  parens top
    (append ('l'::('e'::('t'::(' '::[]))))
      (append (string_of_name na')
        (append (' '::(':'::('='::(' '::[]))))
          (append (print_term _UU03a3_ _UU0393_ true false def0)
            (append (' '::('i'::('n'::(' '::[]))))
              (append nl
                (print_term _UU03a3_ ((vdef na' def0) :: _UU0393_) true false
                  body)))))))
| Coq_tApp (f, l) ->
  parens ((||) top inapp)
    (append (print_term _UU03a3_ _UU0393_ false true f)
      (append (' '::[]) (print_term _UU03a3_ _UU0393_ false false l)))
| Coq_tConst c -> c
| Coq_tConstruct (ind, l) ->
  let { inductive_mind = i; inductive_ind = k } = ind in
  (match lookup_ind_decl _UU03a3_ i k with
   | Some oib ->
     (match nth_error oib.ind_ctors l with
      | Some p -> let (p0, _) = p in let (na, _) = p0 in na
      | None ->
        append
          ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('('::[])))))))))))))))))
          (append (string_of_inductive ind)
            (append (','::[]) (append (string_of_nat l) (')'::[])))))
   | None ->
     append
       ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('('::[])))))))))))))))))
       (append (string_of_inductive ind)
         (append (','::[]) (append (string_of_nat l) (')'::[])))))
| Coq_tCase (p, t0, brs) ->
  let (ind, _) = p in
  let { inductive_mind = mind; inductive_ind = i } = ind in
  (match lookup_ind_decl _UU03a3_ mind i with
   | Some oib ->
     let print_branch =
       let rec print_branch _UU0393_0 arity br =
         match arity with
         | O ->
           append ('='::('>'::(' '::[])))
             (print_term _UU03a3_ _UU0393_0 true false br)
         | S n ->
           (match br with
            | Coq_tLambda (na, b) ->
              let na' = fresh_name _UU0393_0 (aname_to_name na) br in
              append (string_of_name na')
                (append (' '::(' '::[]))
                  (print_branch ((vass na') :: _UU0393_0) n b))
            | _ ->
              append ('='::('>'::(' '::[])))
                (print_term _UU03a3_ _UU0393_0 true false br))
       in print_branch
     in
     let brs0 =
       map (fun pat ->
         let (arity, br) = pat in print_branch _UU0393_ arity br) brs
     in
     let brs1 = combine brs0 oib.ind_ctors in
     parens top
       (append ('m'::('a'::('t'::('c'::('h'::(' '::[]))))))
         (append (print_term _UU03a3_ _UU0393_ true false t0)
           (append (' '::('w'::('i'::('t'::('h'::(' '::[]))))))
             (append nl
               (append
                 (print_list (fun pat ->
                   let (b, y) = pat in
                   let (y0, _) = y in
                   let (na, _) = y0 in append na (append (' '::[]) b))
                   (append nl (' '::('|'::(' '::[])))) brs1)
                 (append nl (append ('e'::('n'::('d'::[]))) nl)))))))
   | None ->
     append ('C'::('a'::('s'::('e'::('('::[])))))
       (append (string_of_inductive ind)
         (append (','::[])
           (append (string_of_nat i)
             (append (','::[])
               (append (string_of_term t0)
                 (append (','::[])
                   (append
                     (string_of_list (fun b -> string_of_term (snd b)) brs)
                     (')'::[])))))))))
| Coq_tProj (p, c) ->
  let (p0, k) = p in
  let (ind, _) = p0 in
  let { inductive_mind = mind; inductive_ind = i } = ind in
  (match lookup_ind_decl _UU03a3_ mind i with
   | Some oib ->
     (match nth_error oib.ind_projs k with
      | Some p1 ->
        let (na, _) = p1 in
        append (print_term _UU03a3_ _UU0393_ false false c)
          (append ('.'::('('::[])) (append na (')'::[])))
      | None ->
        append
          ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('P'::('r'::('o'::('j'::('('::[]))))))))))))
          (append (string_of_inductive ind)
            (append (','::[])
              (append (string_of_nat i)
                (append (','::[])
                  (append (string_of_nat k)
                    (append (','::[])
                      (append (print_term _UU03a3_ _UU0393_ true false c)
                        (')'::[])))))))))
   | None ->
     append
       ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('P'::('r'::('o'::('j'::('('::[]))))))))))))
       (append (string_of_inductive ind)
         (append (','::[])
           (append (string_of_nat i)
             (append (','::[])
               (append (string_of_nat k)
                 (append (','::[])
                   (append (print_term _UU03a3_ _UU0393_ true false c)
                     (')'::[])))))))))
| Coq_tFix (l, n) ->
  parens top
    (append ('l'::('e'::('t'::(' '::('f'::('i'::('x'::(' '::[]))))))))
      (append (print_defs (print_term _UU03a3_) _UU0393_ l)
        (append nl
          (append (' '::('i'::('n'::(' '::[]))))
            (nth_default (string_of_nat n)
              (map
                (let f0 = fun d -> d.dname in fun x -> string_of_name (f0 x))
                l) n)))))
| Coq_tCoFix (l, n) ->
  parens top
    (append
      ('l'::('e'::('t'::(' '::('c'::('o'::('f'::('i'::('x'::(' '::[]))))))))))
      (append (print_defs (print_term _UU03a3_) _UU0393_ l)
        (append nl
          (append (' '::('i'::('n'::(' '::[]))))
            (nth_default (string_of_nat n)
              (map
                (let f0 = fun d -> d.dname in fun x -> string_of_name (f0 x))
                l) n)))))
