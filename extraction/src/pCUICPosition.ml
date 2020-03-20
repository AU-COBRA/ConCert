open BasicAst
open Datatypes
open List0
open MCList
open PCUICAst
open PCUICLiftSubst
open Monad_utils

type stack =
| Empty
| App of term * stack
| Fix of term mfixpoint * nat * term list * stack
| Fix_mfix_ty of name * term * nat * term mfixpoint * term mfixpoint * 
   nat * stack
| Fix_mfix_bd of name * term * nat * term mfixpoint * term mfixpoint * 
   nat * stack
| CoFix of term mfixpoint * nat * term list * stack
| Case_p of (inductive * nat) * term * (nat * term) list * stack
| Case of (inductive * nat) * term * (nat * term) list * stack
| Case_brs of (inductive * nat) * term * term * nat * (nat * term) list
   * (nat * term) list * stack
| Proj of projection * stack
| Prod_l of name * term * stack
| Prod_r of name * term * stack
| Lambda_ty of name * term * stack
| Lambda_tm of name * term * stack
| LetIn_bd of name * term * term * stack
| LetIn_ty of name * term * term * stack
| LetIn_in of name * term * term * stack
| Coq_coApp of term * stack

(** val zipc : term -> stack -> term **)

let rec zipc t = function
| Empty -> t
| App (u, _UU03c0_) -> zipc (Coq_tApp (t, u)) _UU03c0_
| Fix (f, n, args, _UU03c0_) ->
  zipc (Coq_tApp ((mkApps (Coq_tFix (f, n)) args), t)) _UU03c0_
| Fix_mfix_ty (na, bo, ra, mfix1, mfix2, idx, _UU03c0_) ->
  zipc (Coq_tFix
    ((app mfix1 ({ dname = na; dtype = t; dbody = bo; rarg = ra } :: mfix2)),
    idx)) _UU03c0_
| Fix_mfix_bd (na, ty, ra, mfix1, mfix2, idx, _UU03c0_) ->
  zipc (Coq_tFix
    ((app mfix1 ({ dname = na; dtype = ty; dbody = t; rarg = ra } :: mfix2)),
    idx)) _UU03c0_
| CoFix (f, n, args, _UU03c0_) ->
  zipc (Coq_tApp ((mkApps (Coq_tCoFix (f, n)) args), t)) _UU03c0_
| Case_p (indn, c, brs, _UU03c0_) ->
  zipc (Coq_tCase (indn, t, c, brs)) _UU03c0_
| Case (indn, pred, brs, _UU03c0_) ->
  zipc (Coq_tCase (indn, pred, t, brs)) _UU03c0_
| Case_brs (indn, pred, c, m, brs1, brs2, _UU03c0_) ->
  zipc (Coq_tCase (indn, pred, c, (app brs1 ((m, t) :: brs2)))) _UU03c0_
| Proj (p, _UU03c0_) -> zipc (Coq_tProj (p, t)) _UU03c0_
| Prod_l (na, b, _UU03c0_) -> zipc (Coq_tProd (na, t, b)) _UU03c0_
| Prod_r (na, a, _UU03c0_) -> zipc (Coq_tProd (na, a, t)) _UU03c0_
| Lambda_ty (na, b, _UU03c0_) -> zipc (Coq_tLambda (na, t, b)) _UU03c0_
| Lambda_tm (na, a, _UU03c0_) -> zipc (Coq_tLambda (na, a, t)) _UU03c0_
| LetIn_bd (na, b, u, _UU03c0_) -> zipc (Coq_tLetIn (na, t, b, u)) _UU03c0_
| LetIn_ty (na, b, u, _UU03c0_) -> zipc (Coq_tLetIn (na, b, t, u)) _UU03c0_
| LetIn_in (na, b, b0, _UU03c0_) -> zipc (Coq_tLetIn (na, b, b0, t)) _UU03c0_
| Coq_coApp (u, _UU03c0_) -> zipc (Coq_tApp (u, t)) _UU03c0_

(** val zip : (term * stack) -> term **)

let zip t =
  zipc (fst t) (snd t)

(** val decompose_stack : stack -> term list * stack **)

let rec decompose_stack _UU03c0_ = match _UU03c0_ with
| App (u, _UU03c0_0) ->
  let (l, _UU03c0_1) = decompose_stack _UU03c0_0 in ((u :: l), _UU03c0_1)
| _ -> ([], _UU03c0_)

(** val appstack : term list -> stack -> stack **)

let rec appstack l _UU03c0_ =
  match l with
  | [] -> _UU03c0_
  | u :: l0 -> App (u, (appstack l0 _UU03c0_))

(** val decompose_stack_at :
    stack -> nat -> ((term list * term) * stack) option **)

let rec decompose_stack_at _UU03c0_ n =
  match _UU03c0_ with
  | App (u, _UU03c0_0) ->
    (match n with
     | O -> ret (Obj.magic option_monad) (([], u), _UU03c0_0)
     | S n0 ->
       bind (Obj.magic option_monad) (decompose_stack_at _UU03c0_0 n0)
         (fun r ->
         let (y, _UU03c0_1) = r in
         let (l, v) = y in
         ret (Obj.magic option_monad) (((u :: l), v), _UU03c0_1)))
  | _ -> None

(** val fix_context_alt : (name * term) list -> context **)

let fix_context_alt l =
  rev (mapi (fun i d -> vass (fst d) (lift i O (snd d))) l)

(** val def_sig : term def -> name * term **)

let def_sig d =
  (d.dname, d.dtype)

(** val stack_context : stack -> context **)

let rec stack_context = function
| Empty -> []
| App (_, _UU03c0_0) -> stack_context _UU03c0_0
| Fix (_, _, _, _UU03c0_0) -> stack_context _UU03c0_0
| Fix_mfix_ty (_, _, _, _, _, _, _UU03c0_0) -> stack_context _UU03c0_0
| Fix_mfix_bd (na, ty, _, mfix1, mfix2, _, _UU03c0_0) ->
  app_context (stack_context _UU03c0_0)
    (fix_context_alt
      (app (map def_sig mfix1) ((na, ty) :: (map def_sig mfix2))))
| CoFix (_, _, _, _UU03c0_0) -> stack_context _UU03c0_0
| Case_p (_, _, _, _UU03c0_0) -> stack_context _UU03c0_0
| Case (_, _, _, _UU03c0_0) -> stack_context _UU03c0_0
| Case_brs (_, _, _, _, _, _, _UU03c0_0) -> stack_context _UU03c0_0
| Proj (_, _UU03c0_0) -> stack_context _UU03c0_0
| Prod_l (_, _, _UU03c0_0) -> stack_context _UU03c0_0
| Prod_r (na, a, _UU03c0_0) -> snoc (stack_context _UU03c0_0) (vass na a)
| Lambda_ty (_, _, _UU03c0_0) -> stack_context _UU03c0_0
| Lambda_tm (na, a, _UU03c0_0) -> snoc (stack_context _UU03c0_0) (vass na a)
| LetIn_bd (_, _, _, _UU03c0_0) -> stack_context _UU03c0_0
| LetIn_ty (_, _, _, _UU03c0_0) -> stack_context _UU03c0_0
| LetIn_in (na, b, b0, _UU03c0_0) ->
  snoc (stack_context _UU03c0_0) (vdef na b b0)
| Coq_coApp (_, _UU03c0_0) -> stack_context _UU03c0_0

(** val stack_cat : stack -> stack -> stack **)

let rec stack_cat _UU03c1_ _UU03b8_ =
  match _UU03c1_ with
  | Empty -> _UU03b8_
  | App (u, _UU03c1_0) -> App (u, (stack_cat _UU03c1_0 _UU03b8_))
  | Fix (f, n, args, _UU03c1_0) ->
    Fix (f, n, args, (stack_cat _UU03c1_0 _UU03b8_))
  | Fix_mfix_ty (na, bo, ra, mfix1, mfix2, idx, _UU03c1_0) ->
    Fix_mfix_ty (na, bo, ra, mfix1, mfix2, idx,
      (stack_cat _UU03c1_0 _UU03b8_))
  | Fix_mfix_bd (na, ty, ra, mfix1, mfix2, idx, _UU03c1_0) ->
    Fix_mfix_bd (na, ty, ra, mfix1, mfix2, idx,
      (stack_cat _UU03c1_0 _UU03b8_))
  | CoFix (f, n, args, _UU03c1_0) ->
    CoFix (f, n, args, (stack_cat _UU03c1_0 _UU03b8_))
  | Case_p (indn, c, brs, _UU03c1_0) ->
    Case_p (indn, c, brs, (stack_cat _UU03c1_0 _UU03b8_))
  | Case (indn, p, brs, _UU03c1_0) ->
    Case (indn, p, brs, (stack_cat _UU03c1_0 _UU03b8_))
  | Case_brs (indn, p, c, m, brs1, brs2, _UU03c1_0) ->
    Case_brs (indn, p, c, m, brs1, brs2, (stack_cat _UU03c1_0 _UU03b8_))
  | Proj (p, _UU03c1_0) -> Proj (p, (stack_cat _UU03c1_0 _UU03b8_))
  | Prod_l (na, b, _UU03c1_0) ->
    Prod_l (na, b, (stack_cat _UU03c1_0 _UU03b8_))
  | Prod_r (na, a, _UU03c1_0) ->
    Prod_r (na, a, (stack_cat _UU03c1_0 _UU03b8_))
  | Lambda_ty (na, u, _UU03c1_0) ->
    Lambda_ty (na, u, (stack_cat _UU03c1_0 _UU03b8_))
  | Lambda_tm (na, a, _UU03c1_0) ->
    Lambda_tm (na, a, (stack_cat _UU03c1_0 _UU03b8_))
  | LetIn_bd (na, b, u, _UU03c1_0) ->
    LetIn_bd (na, b, u, (stack_cat _UU03c1_0 _UU03b8_))
  | LetIn_ty (na, b, u, _UU03c1_0) ->
    LetIn_ty (na, b, u, (stack_cat _UU03c1_0 _UU03b8_))
  | LetIn_in (na, b, b0, _UU03c1_0) ->
    LetIn_in (na, b, b0, (stack_cat _UU03c1_0 _UU03b8_))
  | Coq_coApp (u, _UU03c1_0) -> Coq_coApp (u, (stack_cat _UU03c1_0 _UU03b8_))
