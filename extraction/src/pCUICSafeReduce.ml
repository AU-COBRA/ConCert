open BasicAst
open Datatypes
open List0
open Nat0
open PCUICAst
open PCUICLiftSubst
open PCUICNormal
open PCUICPosition
open PCUICTyping
open PCUICUnivSubst
open Universes0
open Config0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val inspect : 'a1 -> 'a1 **)

let inspect x =
  x

type construct_view =
| Coq_view_construct of inductive * nat * Instance.t
| Coq_view_other of term

(** val construct_viewc : term -> construct_view **)

let construct_viewc = function
| Coq_tConstruct (ind, n, ui) -> Coq_view_construct (ind, n, ui)
| x -> Coq_view_other x

type red_view =
| Coq_red_view_Rel of nat * stack
| Coq_red_view_LetIn of name * term * term * term * stack
| Coq_red_view_Const of kername * Instance.t * stack
| Coq_red_view_App of term * term * stack
| Coq_red_view_Lambda of name * term * term * term * stack
| Coq_red_view_Fix of term mfixpoint * nat * stack
| Coq_red_view_Case of inductive * nat * term * term * (nat * term) list
   * stack
| Coq_red_view_Proj of projection * term * stack
| Coq_red_view_other of term * stack

(** val red_viewc : term -> stack -> red_view **)

let red_viewc t0 _UU03c0_ =
  match t0 with
  | Coq_tRel n -> Coq_red_view_Rel (n, _UU03c0_)
  | Coq_tLambda (na, a, t1) ->
    (match _UU03c0_ with
     | App (t2, _UU03c0_0) -> Coq_red_view_Lambda (na, a, t1, t2, _UU03c0_0)
     | x -> Coq_red_view_other ((Coq_tLambda (na, a, t1)), x))
  | Coq_tLetIn (na, b, b0, t1) -> Coq_red_view_LetIn (na, b, b0, t1, _UU03c0_)
  | Coq_tApp (u, v) -> Coq_red_view_App (u, v, _UU03c0_)
  | Coq_tConst (k, ui) -> Coq_red_view_Const (k, ui, _UU03c0_)
  | Coq_tCase (indn, p, c, brs) ->
    let (i, n) = indn in Coq_red_view_Case (i, n, p, c, brs, _UU03c0_)
  | Coq_tProj (p, c) -> Coq_red_view_Proj (p, c, _UU03c0_)
  | Coq_tFix (mfix, idx) -> Coq_red_view_Fix (mfix, idx, _UU03c0_)
  | x -> Coq_red_view_other (x, _UU03c0_)

type construct_cofix_view =
| Coq_ccview_construct of inductive * nat * Instance.t
| Coq_ccview_cofix of term mfixpoint * nat
| Coq_ccview_other of term

(** val cc_viewc : term -> construct_cofix_view **)

let cc_viewc = function
| Coq_tConstruct (ind, n, ui) -> Coq_ccview_construct (ind, n, ui)
| Coq_tCoFix (mfix, idx) -> Coq_ccview_cofix (mfix, idx)
| x -> Coq_ccview_other x

(** val _reduce_stack :
    checker_flags -> RedFlags.t -> global_env_ext -> context -> term -> stack
    -> (term -> stack -> __ -> (term * stack)) -> (term * stack) **)

let _reduce_stack _ flags _UU03a3_ _UU0393_ t0 _UU03c0_ reduce =
  match red_viewc t0 _UU03c0_ with
  | Coq_red_view_Rel (c, _UU03c0_0) ->
    if flags.RedFlags.zeta
    then (match inspect
                  (nth_error (app_context _UU0393_ (stack_context _UU03c0_0))
                    c) with
          | Some c0 ->
            (match inspect (decl_body c0) with
             | Some t1 -> reduce (lift (S c) O t1) _UU03c0_0 __
             | None -> ((Coq_tRel c), _UU03c0_0))
          | None -> assert false (* absurd case *))
    else ((Coq_tRel c), _UU03c0_0)
  | Coq_red_view_LetIn (a, b, b0, c, _UU03c0_0) ->
    if flags.RedFlags.zeta
    then reduce (subst1 b O c) _UU03c0_0 __
    else ((Coq_tLetIn (a, b, b0, c)), _UU03c0_0)
  | Coq_red_view_Const (c, u, _UU03c0_0) ->
    if flags.RedFlags.delta
    then (match inspect (lookup_env (fst _UU03a3_) c) with
          | Some g ->
            (match g with
             | PCUICEnvironment.ConstantDecl c0 ->
               let { PCUICEnvironment.cst_type = _;
                 PCUICEnvironment.cst_body = cst_body0;
                 PCUICEnvironment.cst_universes = _ } = c0
               in
               (match cst_body0 with
                | Some t1 ->
                  let body' = subst_instance_constr u t1 in
                  reduce body' _UU03c0_0 __
                | None -> ((Coq_tConst (c, u)), _UU03c0_0))
             | PCUICEnvironment.InductiveDecl _ ->
               assert false (* absurd case *))
          | None -> assert false (* absurd case *))
    else ((Coq_tConst (c, u)), _UU03c0_0)
  | Coq_red_view_App (f, a, _UU03c0_0) -> reduce f (App (a, _UU03c0_0)) __
  | Coq_red_view_Lambda (na, a, t1, a0, args) ->
    if inspect flags.RedFlags.beta
    then reduce (subst1 a0 O t1) args __
    else ((Coq_tLambda (na, a, t1)), (App (a0, args)))
  | Coq_red_view_Fix (mfix, idx, _UU03c0_0) ->
    if flags.RedFlags.fix_
    then (match inspect (unfold_fix mfix idx) with
          | Some p ->
            let (n, t1) = p in
            (match inspect (decompose_stack_at _UU03c0_0 n) with
             | Some p0 ->
               let (p1, s) = p0 in
               let (l, t2) = p1 in
               let (t3, s0) = inspect (reduce t2 (Fix (mfix, idx, l, s)) __)
               in
               (match construct_viewc t3 with
                | Coq_view_construct (ind, n0, ui) ->
                  let (l0, _) = inspect (decompose_stack s0) in
                  reduce t1
                    (appstack l (App
                      ((mkApps (Coq_tConstruct (ind, n0, ui)) l0), s))) __
                | Coq_view_other t4 ->
                  let (l0, _) = inspect (decompose_stack s0) in
                  ((Coq_tFix (mfix, idx)),
                  (appstack l (App ((mkApps t4 l0), s)))))
             | None -> ((Coq_tFix (mfix, idx)), _UU03c0_0))
          | None -> ((Coq_tFix (mfix, idx)), _UU03c0_0))
    else ((Coq_tFix (mfix, idx)), _UU03c0_0)
  | Coq_red_view_Case (ind, par, p, c, brs, _UU03c0_0) ->
    if flags.RedFlags.iota
    then let (t1, s) =
           inspect (reduce c (Case ((ind, par), p, brs, _UU03c0_0)) __)
         in
         let (l, _) = inspect (decompose_stack s) in
         (match cc_viewc t1 with
          | Coq_ccview_construct (_, n, _) ->
            reduce (iota_red par n l brs) _UU03c0_0 __
          | Coq_ccview_cofix (mfix, idx) ->
            (match inspect (unfold_cofix mfix idx) with
             | Some p0 ->
               let (_, t2) = p0 in
               reduce (Coq_tCase ((ind, par), p, (mkApps t2 l), brs))
                 _UU03c0_0 __
             | None -> assert false (* absurd case *))
          | Coq_ccview_other t2 ->
            ((Coq_tCase ((ind, par), p, (mkApps t2 l), brs)), _UU03c0_0))
    else ((Coq_tCase ((ind, par), p, c, brs)), _UU03c0_0)
  | Coq_red_view_Proj (p, c, _UU03c0_0) ->
    let (p0, n) = p in
    let (i, n0) = p0 in
    if flags.RedFlags.iota
    then let (t1, s) = inspect (reduce c (Proj (((i, n0), n), _UU03c0_0)) __)
         in
         let (l, _) = inspect (decompose_stack s) in
         (match cc_viewc t1 with
          | Coq_ccview_construct (_, _, _) ->
            (match inspect (nth_error l (add n0 n)) with
             | Some t2 -> reduce t2 _UU03c0_0 __
             | None -> assert false (* absurd case *))
          | Coq_ccview_cofix (mfix, idx) ->
            (match inspect (unfold_cofix mfix idx) with
             | Some p1 ->
               let (_, t2) = p1 in
               reduce (Coq_tProj (((i, n0), n), (mkApps t2 l))) _UU03c0_0 __
             | None -> assert false (* absurd case *))
          | Coq_ccview_other t2 ->
            ((Coq_tProj (((i, n0), n), (mkApps t2 l))), _UU03c0_0))
    else ((Coq_tProj (((i, n0), n), c)), _UU03c0_0)
  | Coq_red_view_other (t1, _UU03c0_0) -> (t1, _UU03c0_0)

(** val reduce_stack_full_obligations_obligation_1 :
    checker_flags -> RedFlags.t -> global_env_ext -> context ->
    (term * stack) -> ((term * stack) -> __ -> __ -> (term * stack)) ->
    (term * stack) **)

let reduce_stack_full_obligations_obligation_1 cf flags _UU03a3_ _UU0393_ t' f =
  let (t0, s) = t' in
  _reduce_stack cf flags _UU03a3_ _UU0393_ t0 s (fun t'0 _UU03c0_' _ ->
    f (t'0, _UU03c0_') __ __)

(** val reduce_stack_full :
    checker_flags -> RedFlags.t -> global_env_ext -> context -> term -> stack
    -> (term * stack) **)

let reduce_stack_full cf flags _UU03a3_ _UU0393_ t0 _UU03c0_ =
  let rec fix_F x =
    reduce_stack_full_obligations_obligation_1 cf flags _UU03a3_ _UU0393_ x
      (fun y _ _ -> fix_F y)
  in fix_F (t0, _UU03c0_)

(** val reduce_stack :
    checker_flags -> RedFlags.t -> global_env_ext -> context -> term -> stack
    -> term * stack **)

let reduce_stack =
  reduce_stack_full

(** val reduce_term :
    checker_flags -> RedFlags.t -> global_env_ext -> context -> term -> term **)

let reduce_term cf flags _UU03a3_ _UU0393_ t0 =
  zip (reduce_stack cf flags _UU03a3_ _UU0393_ t0 Empty)
