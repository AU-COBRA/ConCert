open All_Forall
open BasicAst
open Classes0
open Datatypes
open EqdepFacts
open List0
open Nat0
open PCUICAst
open PCUICCumulativity
open PCUICEquality
open PCUICNormal
open PCUICPosition
open PCUICReflect
open PCUICSafeLemmata
open PCUICSafeReduce
open PCUICTyping
open PCUICUnivSubst
open Universes0
open Config0
open UGraph0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type state =
| Reduction
| Term
| Args
| Fallback

type pack = { st : state; tm1 : term; stk1 : stack; tm2 : term; stk2 : stack }

(** val leqb_term :
    checker_flags -> universes_graph -> term -> term -> bool **)

let leqb_term cf g =
  eqb_term_upto_univ (check_eqb_universe cf g) (check_leqb_universe cf g)

(** val eqb_term :
    checker_flags -> universes_graph -> term -> term -> bool **)

let eqb_term cf g =
  eqb_term_upto_univ (check_eqb_universe cf g) (check_eqb_universe cf g)

type coq_ConversionError =
| NotFoundConstants of kername * kername
| NotFoundConstant of kername
| LambdaNotConvertibleTypes of context * name * term * term * context * 
   name * term * term * coq_ConversionError
| ProdNotConvertibleDomains of context * name * term * term * context * 
   name * term * term * coq_ConversionError
| CaseOnDifferentInd of context * inductive * nat * term * term
   * (nat * term) list * context * inductive * nat * term * term
   * (nat * term) list
| CaseBranchNumMismatch of inductive * nat * context * term * term
   * (nat * term) list * nat * term * (nat * term) list * context * term
   * term * (nat * term) list * nat * term * (nat * term) list
| DistinctStuckProj of context * projection * term * context * projection
   * term
| CannotUnfoldFix of context * term mfixpoint * nat * context
   * term mfixpoint * nat
| FixRargMismatch of nat * context * term def * term mfixpoint
   * term mfixpoint * context * term def * term mfixpoint * term mfixpoint
| FixMfixMismatch of nat * context * term mfixpoint * context * term mfixpoint
| DistinctCoFix of context * term mfixpoint * nat * context * term mfixpoint
   * nat
| StackHeadError of conv_pb * context * term * term list * term * term list
   * context * term * term * term list * coq_ConversionError
| StackTailError of conv_pb * context * term * term list * term * term list
   * context * term * term * term list * coq_ConversionError
| StackMismatch of context * term * term list * term list * context * 
   term * term list
| HeadMistmatch of conv_pb * context * term * context * term

type coq_ConversionResult =
| Success
| Error of coq_ConversionError

type coq_Ret = conv_pb -> __ -> __ -> __ -> __ -> coq_ConversionResult

type coq_Aux =
  state -> term -> stack -> term -> stack -> __ -> __ -> __ -> __ -> coq_Ret

(** val _isconv_red :
    checker_flags -> global_env_ext -> context -> conv_pb -> term -> stack ->
    term -> stack -> coq_Aux -> coq_ConversionResult **)

let _isconv_red cf _UU03a3_ _UU0393_ leq t1 _UU03c0_1 t2 _UU03c0_2 aux =
  let (l, s) = inspect (decompose_stack _UU03c0_1) in
  let (l0, s0) = inspect (decompose_stack _UU03c0_2) in
  let (t0, s1) =
    inspect
      (reduce_stack cf nodelta_flags _UU03a3_
        (app_context _UU0393_ (stack_context _UU03c0_1)) t1
        (appstack l Empty))
  in
  let (t3, s2) =
    inspect
      (reduce_stack cf nodelta_flags _UU03a3_
        (app_context _UU0393_ (stack_context _UU03c0_2)) t2
        (appstack l0 Empty))
  in
  aux Term t0 (stack_cat s1 s) t3 (stack_cat s2 s0) __ __ __ __ leq __ __ __
    __

(** val unfold_one_fix :
    checker_flags -> global_env_ext -> context -> term mfixpoint -> nat ->
    stack -> (term * stack) option **)

let unfold_one_fix cf _UU03a3_ _UU0393_ mfix idx _UU03c0_ =
  match inspect (unfold_fix mfix idx) with
  | Some p ->
    let (n, t0) = p in
    (match inspect (decompose_stack_at _UU03c0_ n) with
     | Some p0 ->
       let (p1, s) = p0 in
       let (l, t1) = p1 in
       let (t2, s0) =
         inspect
           (reduce_stack cf RedFlags.default _UU03a3_
             (app_context _UU0393_ (stack_context s)) t1 Empty)
       in
       (match construct_viewc t2 with
        | Coq_view_construct (ind, n0, ui) ->
          Some (t0,
            (appstack l (App ((zipc (Coq_tConstruct (ind, n0, ui)) s0), s))))
        | Coq_view_other _ -> None)
     | None -> None)
  | None -> None

type prog_view =
| Coq_prog_view_App of term * term * term * term
| Coq_prog_view_Const of kername * Instance.t * kername * Instance.t
| Coq_prog_view_Lambda of name * term * term * name * term * term
| Coq_prog_view_Prod of name * term * term * name * term * term
| Coq_prog_view_Case of inductive * nat * term * term * (nat * term) list
   * inductive * nat * term * term * (nat * term) list
| Coq_prog_view_Proj of projection * term * projection * term
| Coq_prog_view_Fix of term mfixpoint * nat * term mfixpoint * nat
| Coq_prog_view_CoFix of term mfixpoint * nat * term mfixpoint * nat
| Coq_prog_view_other of term * term

(** val prog_viewc : term -> term -> prog_view **)

let prog_viewc u v =
  match u with
  | Coq_tProd (na, a, b) ->
    (match v with
     | Coq_tProd (na0, a0, b0) -> Coq_prog_view_Prod (na, a, b, na0, a0, b0)
     | x -> Coq_prog_view_other ((Coq_tProd (na, a, b)), x))
  | Coq_tLambda (na, a, t0) ->
    (match v with
     | Coq_tLambda (na0, a0, t1) ->
       Coq_prog_view_Lambda (na, a, t0, na0, a0, t1)
     | x -> Coq_prog_view_other ((Coq_tLambda (na, a, t0)), x))
  | Coq_tApp (u0, v0) ->
    (match v with
     | Coq_tApp (u1, v1) -> Coq_prog_view_App (u0, v0, u1, v1)
     | x -> Coq_prog_view_other ((Coq_tApp (u0, v0)), x))
  | Coq_tConst (k, ui) ->
    (match v with
     | Coq_tConst (k0, ui0) -> Coq_prog_view_Const (k, ui, k0, ui0)
     | x -> Coq_prog_view_other ((Coq_tConst (k, ui)), x))
  | Coq_tCase (indn, p, c, brs) ->
    let (i, n) = indn in
    (match v with
     | Coq_tCase (indn0, p0, c0, brs0) ->
       let (i0, n0) = indn0 in
       Coq_prog_view_Case (i, n, p, c, brs, i0, n0, p0, c0, brs0)
     | x -> Coq_prog_view_other ((Coq_tCase ((i, n), p, c, brs)), x))
  | Coq_tProj (p, c) ->
    (match v with
     | Coq_tProj (p0, c0) -> Coq_prog_view_Proj (p, c, p0, c0)
     | x -> Coq_prog_view_other ((Coq_tProj (p, c)), x))
  | Coq_tFix (mfix, idx) ->
    (match v with
     | Coq_tFix (mfix0, idx0) -> Coq_prog_view_Fix (mfix, idx, mfix0, idx0)
     | x -> Coq_prog_view_other ((Coq_tFix (mfix, idx)), x))
  | Coq_tCoFix (mfix, idx) ->
    (match v with
     | Coq_tCoFix (mfix0, idx0) ->
       Coq_prog_view_CoFix (mfix, idx, mfix0, idx0)
     | x -> Coq_prog_view_other ((Coq_tCoFix (mfix, idx)), x))
  | x -> Coq_prog_view_other (x, v)

(** val unfold_constants :
    checker_flags -> global_env_ext -> context -> conv_pb -> kername ->
    Instance.t -> stack -> kername -> Instance.t -> stack -> coq_Aux ->
    coq_ConversionResult **)

let unfold_constants _ _UU03a3_ _ leq c u _UU03c0_1 c' u' _UU03c0_2 aux =
  match inspect (lookup_env (fst_ctx _UU03a3_) c') with
  | Some g ->
    (match g with
     | PCUICEnvironment.ConstantDecl c0 ->
       let { PCUICEnvironment.cst_type = _; PCUICEnvironment.cst_body =
         cst_body0; PCUICEnvironment.cst_universes = _ } = c0
       in
       (match cst_body0 with
        | Some t0 ->
          aux Reduction (Coq_tConst (c, u)) _UU03c0_1
            (subst_instance_constr u' t0) _UU03c0_2 __ __ __ __ leq __ __ __
            __
        | None ->
          (match inspect (lookup_env (fst_ctx _UU03a3_) c) with
           | Some g0 ->
             (match g0 with
              | PCUICEnvironment.ConstantDecl c1 ->
                let { PCUICEnvironment.cst_type = _;
                  PCUICEnvironment.cst_body = cst_body1;
                  PCUICEnvironment.cst_universes = _ } = c1
                in
                (match cst_body1 with
                 | Some t0 ->
                   aux Reduction (subst_instance_constr u t0) _UU03c0_1
                     (Coq_tConst (c', u')) _UU03c0_2 __ __ __ __ leq __ __ __
                     __
                 | None -> Error (NotFoundConstants (c, c')))
              | PCUICEnvironment.InductiveDecl _ ->
                Error (NotFoundConstants (c, c')))
           | None -> Error (NotFoundConstants (c, c'))))
     | PCUICEnvironment.InductiveDecl _ ->
       (match inspect (lookup_env (fst_ctx _UU03a3_) c) with
        | Some g0 ->
          (match g0 with
           | PCUICEnvironment.ConstantDecl c0 ->
             let { PCUICEnvironment.cst_type = _; PCUICEnvironment.cst_body =
               cst_body0; PCUICEnvironment.cst_universes = _ } = c0
             in
             (match cst_body0 with
              | Some t0 ->
                aux Reduction (subst_instance_constr u t0) _UU03c0_1
                  (Coq_tConst (c', u')) _UU03c0_2 __ __ __ __ leq __ __ __ __
              | None -> Error (NotFoundConstants (c, c')))
           | PCUICEnvironment.InductiveDecl _ ->
             Error (NotFoundConstants (c, c')))
        | None -> Error (NotFoundConstants (c, c'))))
  | None ->
    (match inspect (lookup_env (fst_ctx _UU03a3_) c) with
     | Some g ->
       (match g with
        | PCUICEnvironment.ConstantDecl c0 ->
          let { PCUICEnvironment.cst_type = _; PCUICEnvironment.cst_body =
            cst_body0; PCUICEnvironment.cst_universes = _ } = c0
          in
          (match cst_body0 with
           | Some t0 ->
             aux Reduction (subst_instance_constr u t0) _UU03c0_1 (Coq_tConst
               (c', u')) _UU03c0_2 __ __ __ __ leq __ __ __ __
           | None -> Error (NotFoundConstants (c, c')))
        | PCUICEnvironment.InductiveDecl _ ->
          Error (NotFoundConstants (c, c')))
     | None -> Error (NotFoundConstants (c, c')))

(** val eqb_universe_instance :
    checker_flags -> universes_graph -> Level.t list -> Level.t list -> bool **)

let eqb_universe_instance cf g u v =
  forallb2 (check_eqb_universe cf g) (map Universe.make u)
    (map Universe.make v)

(** val isconv_branches_obligations_obligation_12 :
    checker_flags -> global_env_ext -> nat -> nat -> context -> inductive ->
    nat -> term -> term -> (nat * term) list -> term -> (nat * term) list ->
    stack -> term -> term -> (nat * term) list -> term -> (nat * term) list
    -> stack -> coq_Aux -> state -> term -> stack -> term -> stack -> conv_pb
    -> coq_ConversionResult **)

let isconv_branches_obligations_obligation_12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ aux s' t1' _UU03c0_1' t2' _UU03c0_2' leq =
  aux s' t1' _UU03c0_1' t2' _UU03c0_2' __ __ __ __ leq __ __ __ __

(** val isconv_branches :
    checker_flags -> global_env_ext -> context -> inductive -> nat -> term ->
    term -> (nat * term) list -> (nat * term) list -> stack -> term -> term
    -> (nat * term) list -> (nat * term) list -> stack -> coq_Aux ->
    coq_ConversionResult **)

let rec isconv_branches cf _UU03a3_ _UU0393_ ind par p c brs1 brs2 _UU03c0_ p' c' brs1' brs2' _UU03c0_' aux =
  match brs2 with
  | [] ->
    (match brs2' with
     | [] -> Success
     | _ :: _ -> assert false (* absurd case *))
  | p0 :: l ->
    let (n, t0) = p0 in
    (match brs2' with
     | [] -> assert false (* absurd case *)
     | p1 :: l0 ->
       let (n0, t1) = p1 in
       if inspect (reflect_nat.eqb n n0)
       then (match aux Reduction t0 (Case_brs ((ind, par), p, c, n, brs1, l,
                     _UU03c0_)) t1 (Case_brs ((ind, par), p', c', n0, brs1',
                     l0, _UU03c0_')) __ __ __ __ Conv __ __ __ __ with
             | Success ->
               isconv_branches cf _UU03a3_ _UU0393_ ind par p c
                 (app brs1 ((n, t0) :: [])) l _UU03c0_ p' c'
                 (app brs1' ((n0, t1) :: [])) l0 _UU03c0_'
                 (fun x x0 x1 x2 x3 _ _ _ _ x4 _ _ _ _ ->
                 isconv_branches_obligations_obligation_12 cf _UU03a3_ n n0
                   _UU0393_ ind par p c brs1 t0 l _UU03c0_ p' c' brs1' t1 l0
                   _UU03c0_' aux x x0 x1 x2 x3 x4)
             | Error e -> Error e)
       else Error (CaseBranchNumMismatch (ind, par,
              (app_context _UU0393_ (stack_context _UU03c0_)), p, c, brs1, n,
              t0, l, (app_context _UU0393_ (stack_context _UU03c0_')), p',
              c', brs1', n0, t1, l0)))

(** val isconv_branches'_obligations_obligation_5 :
    checker_flags -> global_env_ext -> context -> inductive -> nat -> term ->
    term -> (nat * term) list -> stack -> inductive -> nat -> term -> term ->
    (nat * term) list -> stack -> coq_Aux -> state -> term -> stack -> term
    -> stack -> conv_pb -> coq_ConversionResult **)

let isconv_branches'_obligations_obligation_5 _ _ _ ind par _ _ _ _ ind' par' _ _ _ _ aux s' t1' _UU03c0_1' t2' _UU03c0_2' leq =
  internal_eq_rew_r_dep par par' (fun _ aux0 ->
    internal_eq_rew_r_dep ind ind'
      (fun _ aux1 s'0 t1'0 _UU03c0_1'0 t2'0 _UU03c0_2'0 _ _ _ _ leq0 _ _ _ _ ->
      aux1 s'0 t1'0 _UU03c0_1'0 t2'0 _UU03c0_2'0 __ __ __ __ leq0 __ __ __ __)
      __ aux0) __ aux s' t1' _UU03c0_1' t2' _UU03c0_2' __ __ __ __ leq __ __
    __ __

(** val isconv_branches' :
    checker_flags -> global_env_ext -> context -> inductive -> nat -> term ->
    term -> (nat * term) list -> stack -> inductive -> nat -> term -> term ->
    (nat * term) list -> stack -> coq_Aux -> coq_ConversionResult **)

let isconv_branches' cf _UU03a3_ _UU0393_ ind par p c brs _UU03c0_ ind' par' p' c' brs' _UU03c0_' aux =
  isconv_branches cf _UU03a3_ _UU0393_ ind par p c [] brs _UU03c0_ p' c' []
    brs' _UU03c0_' (fun x x0 x1 x2 x3 _ _ _ _ x4 _ _ _ _ ->
    isconv_branches'_obligations_obligation_5 cf _UU03a3_ _UU0393_ ind par p
      c brs _UU03c0_ ind' par' p' c' brs' _UU03c0_' aux x x0 x1 x2 x3 x4)

(** val isconv_fix_types_obligations_obligation_10 :
    checker_flags -> global_env_ext -> term def -> term def -> context -> nat
    -> term mfixpoint -> term def list -> stack -> term mfixpoint -> term def
    list -> stack -> coq_Aux -> state -> term -> stack -> term -> stack ->
    conv_pb -> coq_ConversionResult **)

let isconv_fix_types_obligations_obligation_10 _ _ _ _ _ _ _ _ _ _ _ _ aux s' t1' _UU03c0_1' t2' _UU03c0_2' leq =
  aux s' t1' _UU03c0_1' t2' _UU03c0_2' __ __ __ __ leq __ __ __ __

(** val isconv_fix_types :
    checker_flags -> global_env_ext -> context -> nat -> term mfixpoint ->
    term mfixpoint -> stack -> term mfixpoint -> term mfixpoint -> stack ->
    coq_Aux -> coq_ConversionResult **)

let rec isconv_fix_types cf _UU03a3_ _UU0393_ idx mfix1 mfix2 _UU03c0_ mfix1' mfix2' _UU03c0_' aux =
  match mfix2 with
  | [] ->
    (match mfix2' with
     | [] -> Success
     | d :: l ->
       Error (FixMfixMismatch (idx,
         (app_context _UU0393_ (stack_context _UU03c0_)), (app mfix1 []),
         (app_context _UU0393_ (stack_context _UU03c0_')),
         (app mfix1' (d :: l)))))
  | d :: l ->
    (match mfix2' with
     | [] ->
       Error (FixMfixMismatch (idx,
         (app_context _UU0393_ (stack_context _UU03c0_)),
         (app mfix1 (d :: l)),
         (app_context _UU0393_ (stack_context _UU03c0_')), (app mfix1' [])))
     | d0 :: l0 ->
       if inspect (reflect_nat.eqb d.rarg d0.rarg)
       then (match aux Reduction d.dtype (Fix_mfix_ty (d.dname, d.dbody,
                     d.rarg, mfix1, l, idx, _UU03c0_)) d0.dtype (Fix_mfix_ty
                     (d0.dname, d0.dbody, d0.rarg, mfix1', l0, idx,
                     _UU03c0_')) __ __ __ __ Conv __ __ __ __ with
             | Success ->
               isconv_fix_types cf _UU03a3_ _UU0393_ idx
                 (app mfix1 (d :: [])) l _UU03c0_ (app mfix1' (d0 :: [])) l0
                 _UU03c0_' (fun x x0 x1 x2 x3 _ _ _ _ x4 _ _ _ _ ->
                 isconv_fix_types_obligations_obligation_10 cf _UU03a3_ d d0
                   _UU0393_ idx mfix1 l _UU03c0_ mfix1' l0 _UU03c0_' aux x x0
                   x1 x2 x3 x4)
             | Error e -> Error e)
       else Error (FixRargMismatch (idx,
              (app_context _UU0393_ (stack_context _UU03c0_)), d, mfix1, l,
              (app_context _UU0393_ (stack_context _UU03c0_')), d0, mfix1',
              l0)))

(** val isconv_fix_bodies_obligations_obligation_13 :
    checker_flags -> global_env_ext -> context -> nat -> term mfixpoint ->
    term def -> term def list -> stack -> term mfixpoint -> term def -> term
    def list -> stack -> coq_Aux -> state -> term -> stack -> term -> stack
    -> conv_pb -> coq_ConversionResult **)

let isconv_fix_bodies_obligations_obligation_13 _ _ _ _ _ _ _ _ _ _ _ _ aux s' t1' _UU03c0_1' t2' _UU03c0_2' leq =
  aux s' t1' _UU03c0_1' t2' _UU03c0_2' __ __ __ __ leq __ __ __ __

(** val isconv_fix_bodies :
    checker_flags -> global_env_ext -> context -> nat -> term mfixpoint ->
    term mfixpoint -> stack -> term mfixpoint -> term mfixpoint -> stack ->
    coq_Aux -> coq_ConversionResult **)

let rec isconv_fix_bodies cf _UU03a3_ _UU0393_ idx mfix1 mfix2 _UU03c0_ mfix1' mfix2' _UU03c0_' aux =
  match mfix2 with
  | [] ->
    (match mfix2' with
     | [] -> Success
     | _ :: _ -> assert false (* absurd case *))
  | d :: l ->
    (match mfix2' with
     | [] -> assert false (* absurd case *)
     | d0 :: l0 ->
       (match aux Reduction d.dbody (Fix_mfix_bd (d.dname, d.dtype, d.rarg,
                mfix1, l, idx, _UU03c0_)) d0.dbody (Fix_mfix_bd (d0.dname,
                d0.dtype, d0.rarg, mfix1', l0, idx, _UU03c0_')) __ __ __ __
                Conv __ __ __ __ with
        | Success ->
          isconv_fix_bodies cf _UU03a3_ _UU0393_ idx (app mfix1 (d :: [])) l
            _UU03c0_ (app mfix1' (d0 :: [])) l0 _UU03c0_'
            (fun x x0 x1 x2 x3 _ _ _ _ x4 _ _ _ _ ->
            isconv_fix_bodies_obligations_obligation_13 cf _UU03a3_ _UU0393_
              idx mfix1 d l _UU03c0_ mfix1' d0 l0 _UU03c0_' aux x x0 x1 x2 x3
              x4)
        | Error e -> Error e))

(** val isconv_fix_obligations_obligation_4 :
    checker_flags -> global_env_ext -> context -> term mfixpoint -> nat ->
    stack -> term mfixpoint -> nat -> stack -> coq_Aux -> state -> term ->
    stack -> term -> stack -> conv_pb -> coq_ConversionResult **)

let isconv_fix_obligations_obligation_4 _ _ _ _ idx _ _ idx' _ aux s' t1' _UU03c0_1' t2' _UU03c0_2' leq =
  internal_eq_rew_r_dep idx idx'
    (fun _ aux0 s'0 t1'0 _UU03c0_1'0 t2'0 _UU03c0_2'0 _ _ _ _ leq0 _ _ _ _ ->
    aux0 s'0 t1'0 _UU03c0_1'0 t2'0 _UU03c0_2'0 __ __ __ __ leq0 __ __ __ __)
    __ aux s' t1' _UU03c0_1' t2' _UU03c0_2' __ __ __ __ leq __ __ __ __

(** val isconv_fix_obligations_obligation_9 :
    checker_flags -> global_env_ext -> context -> term mfixpoint -> nat ->
    stack -> term mfixpoint -> nat -> stack -> coq_Aux -> state -> term ->
    stack -> term -> stack -> conv_pb -> coq_ConversionResult **)

let isconv_fix_obligations_obligation_9 _ _ _ _ idx _ _ idx' _ aux s' t1' _UU03c0_1' t2' _UU03c0_2' leq =
  internal_eq_rew_r_dep idx idx'
    (fun _ aux0 s'0 t1'0 _UU03c0_1'0 t2'0 _UU03c0_2'0 _ _ _ _ leq0 _ _ _ _ ->
    aux0 s'0 t1'0 _UU03c0_1'0 t2'0 _UU03c0_2'0 __ __ __ __ leq0 __ __ __ __)
    __ aux s' t1' _UU03c0_1' t2' _UU03c0_2' __ __ __ __ leq __ __ __ __

(** val isconv_fix :
    checker_flags -> global_env_ext -> context -> term mfixpoint -> nat ->
    stack -> term mfixpoint -> nat -> stack -> coq_Aux -> coq_ConversionResult **)

let isconv_fix cf _UU03a3_ _UU0393_ mfix idx _UU03c0_ mfix' idx' _UU03c0_' aux =
  match isconv_fix_types cf _UU03a3_ _UU0393_ idx [] mfix _UU03c0_ [] mfix'
          _UU03c0_' (fun x x0 x1 x2 x3 _ _ _ _ x4 _ _ _ _ ->
          isconv_fix_obligations_obligation_4 cf _UU03a3_ _UU0393_ mfix idx
            _UU03c0_ mfix' idx' _UU03c0_' aux x x0 x1 x2 x3 x4) with
  | Success ->
    isconv_fix_bodies cf _UU03a3_ _UU0393_ idx [] mfix _UU03c0_ [] mfix'
      _UU03c0_' (fun x x0 x1 x2 x3 _ _ _ _ x4 _ _ _ _ ->
      isconv_fix_obligations_obligation_9 cf _UU03a3_ _UU0393_ mfix idx
        _UU03c0_ mfix' idx' _UU03c0_' aux x x0 x1 x2 x3 x4)
  | Error e -> Error e

(** val _isconv_prog :
    checker_flags -> global_env_ext -> universes_graph -> context -> conv_pb
    -> term -> stack -> term -> stack -> coq_Aux -> coq_ConversionResult **)

let _isconv_prog cf _UU03a3_ g _UU0393_ leq t1 _UU03c0_1 t2 _UU03c0_2 aux =
  match prog_viewc t1 t2 with
  | Coq_prog_view_App (_, _, _, _) -> assert false (* absurd case *)
  | Coq_prog_view_Const (c1, u1, c2, u2) ->
    if eq_dec (coq_ReflectEq_EqDec reflect_string) c1 c2
    then if inspect (eqb_universe_instance cf g u1 u2)
         then (match aux Args (Coq_tConst (c1, u1)) _UU03c0_1 (Coq_tConst
                       (c2, u2)) _UU03c0_2 __ __ __ __ leq __ __ __ __ with
               | Success -> Success
               | Error _ ->
                 (match inspect (lookup_env (fst_ctx _UU03a3_) c1) with
                  | Some g0 ->
                    (match g0 with
                     | PCUICEnvironment.ConstantDecl c ->
                       let { PCUICEnvironment.cst_type = _;
                         PCUICEnvironment.cst_body = cst_body0;
                         PCUICEnvironment.cst_universes = _ } = c
                       in
                       (match cst_body0 with
                        | Some t0 ->
                          aux Reduction (subst_instance_constr u1 t0)
                            _UU03c0_1 (subst_instance_constr u2 t0) _UU03c0_2
                            __ __ __ __ leq __ __ __ __
                        | None -> Error (NotFoundConstant c1))
                     | PCUICEnvironment.InductiveDecl _ ->
                       Error (NotFoundConstant c1))
                  | None -> Error (NotFoundConstant c1)))
         else unfold_constants cf _UU03a3_ _UU0393_ leq c1 u1 _UU03c0_1 c2 u2
                _UU03c0_2 aux
    else unfold_constants cf _UU03a3_ _UU0393_ leq c1 u1 _UU03c0_1 c2 u2
           _UU03c0_2 aux
  | Coq_prog_view_Lambda (na1, a1, b1, na2, a2, b2) ->
    (match aux Reduction a1 (Lambda_ty (na1, b1, _UU03c0_1)) a2 (Lambda_ty
             (na2, b2, _UU03c0_2)) __ __ __ __ Conv __ __ __ __ with
     | Success ->
       aux Reduction b1 (Lambda_tm (na1, a1, _UU03c0_1)) b2 (Lambda_tm (na2,
         a2, _UU03c0_2)) __ __ __ __ leq __ __ __ __
     | Error e ->
       Error (LambdaNotConvertibleTypes
         ((app_context _UU0393_ (stack_context _UU03c0_1)), na1, a1, b1,
         (app_context _UU0393_ (stack_context _UU03c0_2)), na2, a2, b2, e)))
  | Coq_prog_view_Prod (na1, a1, b1, na2, a2, b2) ->
    (match aux Reduction a1 (Prod_l (na1, b1, _UU03c0_1)) a2 (Prod_l (na2,
             b2, _UU03c0_2)) __ __ __ __ Conv __ __ __ __ with
     | Success ->
       aux Reduction b1 (Prod_r (na1, a1, _UU03c0_1)) b2 (Prod_r (na2, a2,
         _UU03c0_2)) __ __ __ __ leq __ __ __ __
     | Error e ->
       Error (ProdNotConvertibleDomains
         ((app_context _UU0393_ (stack_context _UU03c0_1)), na1, a1, b1,
         (app_context _UU0393_ (stack_context _UU03c0_2)), na2, a2, b2, e)))
  | Coq_prog_view_Case (ind, par, p, c, brs, ind', par', p', c', brs') ->
    if inspect
         (eqb_term cf g (Coq_tCase ((ind, par), p, c, brs)) (Coq_tCase
           ((ind', par'), p', c', brs')))
    then aux Args (Coq_tCase ((ind, par), p, c, brs)) _UU03c0_1 (Coq_tCase
           ((ind', par'), p', c', brs')) _UU03c0_2 __ __ __ __ leq __ __ __ __
    else let refine =
           inspect
             (reduce_term cf RedFlags.default _UU03a3_
               (app_context _UU0393_ (stack_context _UU03c0_1)) c)
         in
         let refine0 =
           inspect
             (reduce_term cf RedFlags.default _UU03a3_
               (app_context _UU0393_ (stack_context _UU03c0_2)) c')
         in
         if inspect ((&&) (eqb_term cf g refine c) (eqb_term cf g refine0 c'))
         then if inspect
                   ((reflect_prod reflect_inductive reflect_nat).eqb (ind,
                     par) (ind', par'))
              then (match aux Reduction p (Case_p ((ind, par), c, brs,
                            _UU03c0_1)) p' (Case_p ((ind', par'), c', brs',
                            _UU03c0_2)) __ __ __ __ Conv __ __ __ __ with
                    | Success ->
                      (match aux Reduction c (Case ((ind, par), p, brs,
                               _UU03c0_1)) c' (Case ((ind', par'), p', brs',
                               _UU03c0_2)) __ __ __ __ Conv __ __ __ __ with
                       | Success ->
                         (match isconv_branches' cf _UU03a3_ _UU0393_ ind par
                                  p c brs _UU03c0_1 ind' par' p' c' brs'
                                  _UU03c0_2 aux with
                          | Success ->
                            aux Args (Coq_tCase ((ind, par), p, c, brs))
                              _UU03c0_1 (Coq_tCase ((ind', par'), p', c',
                              brs')) _UU03c0_2 __ __ __ __ leq __ __ __ __
                          | Error e -> Error e)
                       | Error e -> Error e)
                    | Error e -> Error e)
              else Error (CaseOnDifferentInd
                     ((app_context _UU0393_ (stack_context _UU03c0_1)), ind,
                     par, p, c, brs,
                     (app_context _UU0393_ (stack_context _UU03c0_2)), ind',
                     par', p', c', brs'))
         else aux Reduction (Coq_tCase ((ind, par), p, refine, brs))
                _UU03c0_1 (Coq_tCase ((ind', par'), p', refine0, brs'))
                _UU03c0_2 __ __ __ __ leq __ __ __ __
  | Coq_prog_view_Proj (p, c, p', c') ->
    if inspect
         ((reflect_prod (reflect_prod reflect_inductive reflect_nat)
            reflect_nat).eqb p p')
    then (match aux Reduction c (Proj (p, _UU03c0_1)) c' (Proj (p',
                  _UU03c0_2)) __ __ __ __ Conv __ __ __ __ with
          | Success ->
            aux Args (Coq_tProj (p, c)) _UU03c0_1 (Coq_tProj (p', c'))
              _UU03c0_2 __ __ __ __ leq __ __ __ __
          | Error e -> Error e)
    else Error (DistinctStuckProj
           ((app_context _UU0393_ (stack_context _UU03c0_1)), p, c,
           (app_context _UU0393_ (stack_context _UU03c0_2)), p', c'))
  | Coq_prog_view_Fix (mfix, idx, mfix', idx') ->
    if inspect (eqb_term cf g (Coq_tFix (mfix, idx)) (Coq_tFix (mfix', idx')))
    then aux Args (Coq_tFix (mfix, idx)) _UU03c0_1 (Coq_tFix (mfix', idx'))
           _UU03c0_2 __ __ __ __ leq __ __ __ __
    else (match inspect
                  (unfold_one_fix cf _UU03a3_ _UU0393_ mfix idx _UU03c0_1) with
          | Some p ->
            let (t0, s) = p in
            let (l, s0) = inspect (decompose_stack s) in
            let (t3, s1) =
              inspect
                (reduce_stack cf nodelta_flags _UU03a3_
                  (app_context _UU0393_ (stack_context s0)) t0
                  (appstack l Empty))
            in
            aux Term t3 (stack_cat s1 s0) (Coq_tFix (mfix', idx')) _UU03c0_2
              __ __ __ __ leq __ __ __ __
          | None ->
            (match inspect
                     (unfold_one_fix cf _UU03a3_ _UU0393_ mfix' idx'
                       _UU03c0_2) with
             | Some p ->
               let (t0, s) = p in
               let (l, s0) = inspect (decompose_stack s) in
               let (t3, s1) =
                 inspect
                   (reduce_stack cf nodelta_flags _UU03a3_
                     (app_context _UU0393_ (stack_context s0)) t0
                     (appstack l Empty))
               in
               aux Term (Coq_tFix (mfix, idx)) _UU03c0_1 t3 (stack_cat s1 s0)
                 __ __ __ __ leq __ __ __ __
             | None ->
               if inspect (reflect_nat.eqb idx idx')
               then (match isconv_fix cf _UU03a3_ _UU0393_ mfix idx _UU03c0_1
                             mfix' idx' _UU03c0_2 aux with
                     | Success ->
                       aux Args (Coq_tFix (mfix, idx)) _UU03c0_1 (Coq_tFix
                         (mfix', idx')) _UU03c0_2 __ __ __ __ leq __ __ __ __
                     | Error e -> Error e)
               else Error (CannotUnfoldFix
                      ((app_context _UU0393_ (stack_context _UU03c0_1)),
                      mfix, idx,
                      (app_context _UU0393_ (stack_context _UU03c0_2)),
                      mfix', idx'))))
  | Coq_prog_view_CoFix (mfix, idx, mfix', idx') ->
    if inspect
         (eqb_term cf g (Coq_tCoFix (mfix, idx)) (Coq_tCoFix (mfix', idx')))
    then aux Args (Coq_tCoFix (mfix, idx)) _UU03c0_1 (Coq_tCoFix (mfix',
           idx')) _UU03c0_2 __ __ __ __ leq __ __ __ __
    else Error (DistinctCoFix
           ((app_context _UU0393_ (stack_context _UU03c0_1)), mfix, idx,
           (app_context _UU0393_ (stack_context _UU03c0_2)), mfix', idx'))
  | Coq_prog_view_other (u, v) ->
    aux Fallback u _UU03c0_1 v _UU03c0_2 __ __ __ __ leq __ __ __ __

type coq_Aux' =
  term -> term -> term list -> term list -> stack -> __ -> __ -> __ -> __ ->
  coq_Ret

(** val _isconv_args'_obligations_obligation_13 :
    checker_flags -> global_env_ext -> context -> term -> term list -> term
    -> term list -> stack -> term -> term -> term list -> stack -> coq_Aux'
    -> term -> term -> term list -> term list -> stack -> conv_pb ->
    coq_ConversionResult **)

let _isconv_args'_obligations_obligation_13 _ _ _ _ _ _ _ _ _ _ _ _ aux u0 u3 ca1 a1 _UU03c1_2 leq =
  aux u0 u3 ca1 a1 _UU03c1_2 __ __ __ __ leq __ __ __ __

(** val _isconv_args' :
    checker_flags -> global_env_ext -> conv_pb -> context -> term -> term
    list -> term list -> stack -> term -> term list -> stack -> coq_Aux' ->
    coq_ConversionResult **)

let rec _isconv_args' cf _UU03a3_ leq _UU0393_ t1 args1 l1 _UU03c0_1 t2 l2 _UU03c0_2 aux =
  match l1 with
  | [] ->
    (match l2 with
     | [] -> Success
     | t0 :: l ->
       Error (StackMismatch
         ((app_context _UU0393_ (stack_context _UU03c0_1)), t1, args1, [],
         (app_context _UU0393_ (stack_context _UU03c0_2)), t2, (t0 :: l))))
  | t0 :: l ->
    (match l2 with
     | [] ->
       Error (StackMismatch
         ((app_context _UU0393_ (stack_context _UU03c0_1)), t1, args1,
         (t0 :: l), (app_context _UU0393_ (stack_context _UU03c0_2)), t2, []))
     | t3 :: l0 ->
       (match aux t0 t3 args1 l (Coq_coApp (t2, (appstack l0 _UU03c0_2))) __
                __ __ __ Conv __ __ __ __ with
        | Success ->
          (match _isconv_args' cf _UU03a3_ leq _UU0393_ t1
                   (app args1 (t0 :: [])) l _UU03c0_1 (Coq_tApp (t2, t3)) l0
                   _UU03c0_2 (fun x x0 x1 x2 x3 _ _ _ _ x4 _ _ _ _ ->
                   _isconv_args'_obligations_obligation_13 cf _UU03a3_
                     _UU0393_ t1 args1 t0 l _UU03c0_1 t2 t3 l0 _UU03c0_2 aux
                     x x0 x1 x2 x3 x4) with
           | Success -> Success
           | Error e ->
             Error (StackTailError (leq,
               (app_context _UU0393_ (stack_context _UU03c0_1)), t1, args1,
               t0, l, (app_context _UU0393_ (stack_context _UU03c0_2)), t2,
               t3, l0, e)))
        | Error e ->
          Error (StackHeadError (leq,
            (app_context _UU0393_ (stack_context _UU03c0_1)), t1, args1, t0,
            l, (app_context _UU0393_ (stack_context _UU03c0_2)), t2, t3, l0,
            e))))

(** val _isconv_args_obligations_obligation_7 :
    checker_flags -> global_env_ext -> stack -> term list -> stack -> stack
    -> term list -> stack -> conv_pb -> context -> term -> term -> coq_Aux ->
    term -> term -> term list -> term list -> stack -> conv_pb ->
    coq_ConversionResult **)

let _isconv_args_obligations_obligation_7 _ _ _ _ _ _ _ _UU03b8_1 _ _ t1 _ aux u1 u2 ca1 a1 _UU03c1_2 leq =
  aux Reduction u1 (Coq_coApp ((mkApps t1 ca1), (appstack a1 _UU03b8_1))) u2
    _UU03c1_2 __ __ __ __ leq __ __ __ __

(** val _isconv_args :
    checker_flags -> global_env_ext -> conv_pb -> context -> term -> stack ->
    term -> stack -> coq_Aux -> coq_ConversionResult **)

let _isconv_args cf _UU03a3_ leq _UU0393_ t1 _UU03c0_1 t2 _UU03c0_2 aux =
  let (l, s) = inspect (decompose_stack _UU03c0_1) in
  let (l0, s0) = inspect (decompose_stack _UU03c0_2) in
  _isconv_args' cf _UU03a3_ leq _UU0393_ t1 [] l s t2 l0 s0
    (fun x x0 x1 x2 x3 _ _ _ _ x4 _ _ _ _ ->
    _isconv_args_obligations_obligation_7 cf _UU03a3_ _UU03c0_2 l0 s0
      _UU03c0_1 l s leq _UU0393_ t1 t2 aux x x0 x1 x2 x3 x4)

(** val unfold_one_case :
    checker_flags -> global_env_ext -> context -> inductive -> nat -> term ->
    term -> (nat * term) list -> term option **)

let unfold_one_case cf _UU03a3_ _UU0393_ ind par p c brs =
  let (t0, s) =
    inspect (reduce_stack cf RedFlags.default _UU03a3_ _UU0393_ c Empty)
  in
  (match cc_viewc t0 with
   | Coq_ccview_construct (_, n, _) ->
     let (l, _) = inspect (decompose_stack s) in Some (iota_red par n l brs)
   | Coq_ccview_cofix (mfix, idx) ->
     (match inspect (unfold_cofix mfix idx) with
      | Some p0 ->
        let (_, t1) = p0 in
        let (l, _) = inspect (decompose_stack s) in
        Some (Coq_tCase ((ind, par), p, (mkApps t1 l), brs))
      | None -> None)
   | Coq_ccview_other _ -> None)

(** val unfold_one_proj :
    checker_flags -> global_env_ext -> context -> projection -> term -> term
    option **)

let unfold_one_proj cf _UU03a3_ _UU0393_ p c =
  let (p0, n) = p in
  let (i, n0) = p0 in
  let (t0, s) =
    inspect (reduce_stack cf RedFlags.default _UU03a3_ _UU0393_ c Empty)
  in
  (match cc_viewc t0 with
   | Coq_ccview_construct (_, _, _) ->
     let (l, _) = inspect (decompose_stack s) in
     inspect (nth_error l (add n0 n))
   | Coq_ccview_cofix (mfix, idx) ->
     let (l, _) = inspect (decompose_stack s) in
     (match inspect (unfold_cofix mfix idx) with
      | Some p1 ->
        let (_, t1) = p1 in Some (Coq_tProj (((i, n0), n), (mkApps t1 l)))
      | None -> None)
   | Coq_ccview_other _ -> None)

(** val reducible_head :
    checker_flags -> global_env_ext -> context -> term -> stack ->
    (term * stack) option **)

let reducible_head cf _UU03a3_ _UU0393_ t0 _UU03c0_ =
  match t0 with
  | Coq_tConst (k, ui) ->
    (match inspect (lookup_env (fst_ctx _UU03a3_) k) with
     | Some g ->
       (match g with
        | PCUICEnvironment.ConstantDecl c ->
          let { PCUICEnvironment.cst_type = _; PCUICEnvironment.cst_body =
            cst_body0; PCUICEnvironment.cst_universes = _ } = c
          in
          (match cst_body0 with
           | Some t1 -> Some ((subst_instance_constr ui t1), _UU03c0_)
           | None -> None)
        | PCUICEnvironment.InductiveDecl _ -> None)
     | None -> None)
  | Coq_tCase (indn, p, c, brs) ->
    let (i, n) = indn in
    (match inspect
             (unfold_one_case cf _UU03a3_
               (app_context _UU0393_ (stack_context _UU03c0_)) i n p c brs) with
     | Some t1 -> Some (t1, _UU03c0_)
     | None -> None)
  | Coq_tProj (p, c) ->
    (match inspect
             (unfold_one_proj cf _UU03a3_
               (app_context _UU0393_ (stack_context _UU03c0_)) p c) with
     | Some t1 -> Some (t1, _UU03c0_)
     | None -> None)
  | Coq_tFix (mfix, idx) ->
    unfold_one_fix cf _UU03a3_ _UU0393_ mfix idx _UU03c0_
  | _ -> None

(** val _isconv_fallback :
    checker_flags -> RedFlags.t -> global_env_ext -> universes_graph ->
    context -> conv_pb -> term -> stack -> term -> stack -> coq_Aux ->
    coq_ConversionResult **)

let _isconv_fallback cf _ _UU03a3_ g _UU0393_ leq t1 _UU03c0_1 t2 _UU03c0_2 aux =
  match inspect (reducible_head cf _UU03a3_ _UU0393_ t1 _UU03c0_1) with
  | Some p ->
    let (t0, s) = p in
    let (l, s0) = inspect (decompose_stack s) in
    let (t3, s1) =
      inspect
        (reduce_stack cf nodelta_flags _UU03a3_
          (app_context _UU0393_ (stack_context s)) t0 (appstack l Empty))
    in
    aux Term t3 (stack_cat s1 s0) t2 _UU03c0_2 __ __ __ __ leq __ __ __ __
  | None ->
    (match inspect (reducible_head cf _UU03a3_ _UU0393_ t2 _UU03c0_2) with
     | Some p ->
       let (t0, s) = p in
       let (l, s0) = inspect (decompose_stack s) in
       let (t3, s1) =
         inspect
           (reduce_stack cf nodelta_flags _UU03a3_
             (app_context _UU0393_ (stack_context s)) t0 (appstack l Empty))
       in
       aux Term t1 _UU03c0_1 t3 (stack_cat s1 s0) __ __ __ __ leq __ __ __ __
     | None ->
       (match inspect leq with
        | Conv ->
          if inspect (eqb_term cf g t1 t2)
          then aux Args t1 _UU03c0_1 t2 _UU03c0_2 __ __ __ __ Conv __ __ __ __
          else Error (HeadMistmatch (Conv,
                 (app_context _UU0393_ (stack_context _UU03c0_1)), t1,
                 (app_context _UU0393_ (stack_context _UU03c0_2)), t2))
        | Cumul ->
          if inspect (leqb_term cf g t1 t2)
          then aux Args t1 _UU03c0_1 t2 _UU03c0_2 __ __ __ __ Cumul __ __ __
                 __
          else Error (HeadMistmatch (Cumul,
                 (app_context _UU0393_ (stack_context _UU03c0_1)), t1,
                 (app_context _UU0393_ (stack_context _UU03c0_2)), t2))))

(** val _isconv :
    checker_flags -> RedFlags.t -> global_env_ext -> universes_graph -> state
    -> context -> term -> stack -> term -> stack -> coq_Aux -> conv_pb ->
    coq_ConversionResult **)

let _isconv cf flags _UU03a3_ g s _UU0393_ t1 _UU03c0_1 t2 _UU03c0_2 aux leq =
  match s with
  | Reduction ->
    _isconv_red cf _UU03a3_ _UU0393_ leq t1 _UU03c0_1 t2 _UU03c0_2 aux
  | Term ->
    _isconv_prog cf _UU03a3_ g _UU0393_ leq t1 _UU03c0_1 t2 _UU03c0_2 aux
  | Args ->
    _isconv_args cf _UU03a3_ leq _UU0393_ t1 _UU03c0_1 t2 _UU03c0_2 aux
  | Fallback ->
    _isconv_fallback cf flags _UU03a3_ g _UU0393_ leq t1 _UU03c0_1 t2
      _UU03c0_2 aux

(** val isconv_full_obligations_obligation_1 :
    checker_flags -> RedFlags.t -> global_env_ext -> universes_graph ->
    context -> term -> stack -> pack -> (pack -> __ -> __ -> __ -> coq_Ret)
    -> conv_pb -> coq_ConversionResult **)

let isconv_full_obligations_obligation_1 cf flags _UU03a3_ g _UU0393_ _ _ pp f leq =
  _isconv cf flags _UU03a3_ g pp.st _UU0393_ pp.tm1 pp.stk1 pp.tm2 pp.stk2
    (fun s' t1' _UU03c0_1' t2' _UU03c0_2' _ _ _ _ ->
    f { st = s'; tm1 = t1'; stk1 = _UU03c0_1'; tm2 = t2'; stk2 = _UU03c0_2' }
      __ __ __) leq

(** val isconv_full :
    checker_flags -> RedFlags.t -> global_env_ext -> universes_graph -> state
    -> context -> term -> stack -> term -> stack -> conv_pb ->
    coq_ConversionResult **)

let isconv_full cf flags _UU03a3_ g s _UU0393_ t1 _UU03c0_1 t2 _UU03c0_2 leq =
  let rec fix_F x x0 =
    isconv_full_obligations_obligation_1 cf flags _UU03a3_ g _UU0393_ t1
      _UU03c0_1 x (fun y _ _ _ x1 _ _ _ _ -> fix_F y x1) x0
  in fix_F { st = s; tm1 = t1; stk1 = _UU03c0_1; tm2 = t2; stk2 = _UU03c0_2 }
       leq

(** val isconv :
    checker_flags -> RedFlags.t -> global_env_ext -> universes_graph ->
    context -> conv_pb -> term -> stack -> term -> stack ->
    coq_ConversionResult **)

let isconv cf flags _UU03a3_ g _UU0393_ leq t1 _UU03c0_1 t2 _UU03c0_2 =
  isconv_full cf flags _UU03a3_ g Reduction _UU0393_ t1 _UU03c0_1 t2
    _UU03c0_2 leq

(** val isconv_term :
    checker_flags -> RedFlags.t -> global_env_ext -> universes_graph ->
    context -> conv_pb -> term -> term -> coq_ConversionResult **)

let isconv_term cf flags _UU03a3_ g _UU0393_ leq t1 t2 =
  isconv cf flags _UU03a3_ g _UU0393_ leq t1 Empty t2 Empty
