open BasicAst
open Datatypes
open EAst
open Extract
open Init
open List0
open PCUICAst
open PCUICAstUtils
open PCUICLiftSubst
open PCUICSafeChecker
open PCUICSafeReduce
open PCUICTyping
open Specif
open Universes0
open Config0
open Monad_utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val normal_dec :
    global_env_ext -> context -> term -> __ typing_result **)

let rec normal_dec _UU03a3_ _UU0393_ = function
| Coq_tRel n ->
  let n0 = Obj.magic n in
  let filtered_var = option_map decl_body (nth_error _UU0393_ n0) in
  (match filtered_var with
   | Some o ->
     (match o with
      | Some _ ->
        Obj.magic (TypeError (Msg
          ('h'::('n'::('f'::(' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('n'::('o'::('r'::('m'::('a'::('l'::(' '::('f'::('o'::('r'::('m'::[]))))))))))))))))))))))))))))))))
      | None -> Obj.magic ret typing_monad __)
   | None -> Obj.magic ret typing_monad __)
| Coq_tVar _ -> Obj.magic ret typing_monad __
| Coq_tSort _ -> Obj.magic ret typing_monad __
| Coq_tProd (na, a, b) ->
  let na0 = Obj.magic na in
  let a0 = Obj.magic a in
  let b0 = Obj.magic b in
  Obj.magic bind typing_monad (Obj.magic normal_dec _UU03a3_ _UU0393_ a0)
    (fun _ ->
    bind typing_monad
      (Obj.magic normal_dec _UU03a3_ (snoc _UU0393_ (vass na0 a0)) b0)
      (fun _ -> ret typing_monad __))
| Coq_tLambda (na, a, b) ->
  let na0 = Obj.magic na in
  let a0 = Obj.magic a in
  let b0 = Obj.magic b in
  Obj.magic bind typing_monad (Obj.magic normal_dec _UU03a3_ _UU0393_ a0)
    (fun _ ->
    bind typing_monad
      (Obj.magic normal_dec _UU03a3_ (snoc _UU0393_ (vass na0 a0)) b0)
      (fun _ -> ret typing_monad __))
| Coq_tLetIn (_, _, _, _) ->
  TypeError (Msg
    ('h'::('n'::('f'::(' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('n'::('o'::('r'::('m'::('a'::('l'::(' '::('f'::('o'::('r'::('m'::[])))))))))))))))))))))))))))))))
| Coq_tConst (c, _) ->
  let c0 = Obj.magic c in
  let filtered_var = lookup_env (fst_ctx _UU03a3_) c0 in
  (match filtered_var with
   | Some g ->
     (match g with
      | PCUICEnvironment.ConstantDecl c1 ->
        let { PCUICEnvironment.cst_type = _; PCUICEnvironment.cst_body =
          cst_body0; PCUICEnvironment.cst_universes = _ } = c1
        in
        (match cst_body0 with
         | Some _ ->
           Obj.magic (TypeError (Msg
             ('h'::('n'::('f'::(' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('n'::('o'::('r'::('m'::('a'::('l'::(' '::('f'::('o'::('r'::('m'::[]))))))))))))))))))))))))))))))))
         | None -> Obj.magic ret typing_monad __)
      | PCUICEnvironment.InductiveDecl _ -> Obj.magic ret typing_monad __)
   | None -> Obj.magic ret typing_monad __)
| Coq_tInd (_, _) -> Obj.magic ret typing_monad __
| Coq_tConstruct (_, _, _) -> Obj.magic ret typing_monad __
| Coq_tCase (_, _, _, _) ->
  TypeError (Msg
    ('h'::('n'::('f'::(' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('n'::('o'::('r'::('m'::('a'::('l'::(' '::('f'::('o'::('r'::('m'::[])))))))))))))))))))))))))))))))
| Coq_tProj (_, _) ->
  TypeError (Msg
    ('h'::('n'::('f'::(' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('n'::('o'::('r'::('m'::('a'::('l'::(' '::('f'::('o'::('r'::('m'::[])))))))))))))))))))))))))))))))
| _ ->
  TypeError (Msg
    ('n'::('o'::('t'::(' '::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('e'::('d'::[]))))))))))))))))

(** val reduce_to_sort' :
    global_env_ext -> context -> term -> ((Universe.t, __) sigT, __) sum
    typing_result **)

let reduce_to_sort' _UU03a3_ _UU0393_ t0 = match t0 with
| Coq_tSort u ->
  let u0 = Obj.magic u in
  Obj.magic ret typing_monad (Coq_inl (Coq_existT (u0, __)))
| _ ->
  let filtered_var = hnf extraction_checker_flags _UU03a3_ _UU0393_ t0 in
  (match filtered_var with
   | Coq_tSort u -> Obj.magic ret typing_monad (Coq_inl (Coq_existT (u, __)))
   | x ->
     let filtered_var0 = normal_dec _UU03a3_ _UU0393_ x in
     (match filtered_var0 with
      | Checked _ -> Obj.magic ret typing_monad (Coq_inr __)
      | TypeError t1 -> Obj.magic (TypeError t1)))

(** val reduce_to_prod' :
    global_env_ext -> context -> term -> ((name, (term, (term, __) sigT)
    sigT) sigT, __) sum typing_result **)

let reduce_to_prod' _UU03a3_ _UU0393_ t0 = match t0 with
| Coq_tProd (na, a, b) ->
  let na0 = Obj.magic na in
  let a0 = Obj.magic a in
  let b0 = Obj.magic b in
  Obj.magic ret typing_monad (Coq_inl (Coq_existT (na0, (Coq_existT (a0,
    (Coq_existT (b0, __)))))))
| _ ->
  let filtered_var = hnf extraction_checker_flags _UU03a3_ _UU0393_ t0 in
  (match filtered_var with
   | Coq_tProd (na, a, b) ->
     Obj.magic ret typing_monad (Coq_inl (Coq_existT (na, (Coq_existT (a,
       (Coq_existT (b, __)))))))
   | x ->
     let filtered_var0 = normal_dec _UU03a3_ _UU0393_ x in
     (match filtered_var0 with
      | Checked _ -> Obj.magic ret typing_monad (Coq_inr __)
      | TypeError _ ->
        Obj.magic (TypeError (Msg
          ('h'::('n'::('f'::(' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('n'::('o'::('r'::('m'::('a'::('l'::(' '::('f'::('o'::('r'::('m'::[]))))))))))))))))))))))))))))))))))

(** val is_arity :
    global_env_ext -> PCUICEnvironment.context -> term -> bool typing_result **)

let is_arity _UU03a3_ a a0 =
  let rec fix_F x =
    let _UU0393_ = pr1 x in
    let t0 = pr1 (pr2 (pr2 x)) in
    (match reduce_to_sort' _UU03a3_ _UU0393_ t0 with
     | Checked a1 ->
       (match a1 with
        | Coq_inl _ -> ret (Obj.magic typing_monad) true
        | Coq_inr _ ->
          (match inspect (reduce_to_prod' _UU03a3_ _UU0393_ t0) with
           | Checked a2 ->
             (match a2 with
              | Coq_inl s ->
                let Coq_existT (x0, s0) = s in
                let Coq_existT (x1, s1) = s0 in
                let Coq_existT (x2, _) = s1 in
                (match let y = (snoc _UU0393_ (vass x0 x1)),(__,(x2,__)) in
                       fix_F y with
                 | Checked a3 -> ret (Obj.magic typing_monad) a3
                 | TypeError t1 -> TypeError t1)
              | Coq_inr _ -> ret (Obj.magic typing_monad) false)
           | TypeError t1 -> TypeError t1))
     | TypeError t1 -> TypeError t1)
  in fix_F (a,(__,(a0,__)))

(** val is_erasable :
    global_env_ext -> context -> term -> bool typing_result **)

let is_erasable sigma gamma t0 =
  bind (Obj.magic typing_monad)
    (Obj.magic make_graph_and_infer extraction_checker_flags sigma gamma t0)
    (fun pat ->
    let Coq_existT (t1, _) = pat in
    let t2 = Obj.magic t1 in
    Obj.magic bind typing_monad (Obj.magic is_arity sigma gamma t2) (fun b ->
      if b
      then ret typing_monad true
      else bind typing_monad
             (Obj.magic make_graph_and_infer extraction_checker_flags sigma
               gamma t2) (fun pat0 ->
             let Coq_existT (k, _) = pat0 in
             bind typing_monad
               (Obj.magic reduce_to_sort extraction_checker_flags sigma gamma
                 k) (fun pat1 ->
               let Coq_existT (u, _) = pat1 in
               let filtered_var = Universe.is_prop u in
               if filtered_var
               then ret typing_monad true
               else ret typing_monad false))))

(** val flag_of_type :
    global_env_ext -> context -> term -> bool typing_result **)

let flag_of_type sigma gamma ty =
  bind (Obj.magic typing_monad)
    (Obj.magic make_graph_and_infer extraction_checker_flags sigma gamma ty)
    (fun _ ->
    Obj.magic bind typing_monad (Obj.magic is_arity sigma gamma ty) (fun b ->
      if b then ret typing_monad true else ret typing_monad false))

(** val erase_mfix_obligation_1 :
    global_env_ext -> PCUICEnvironment.context -> term BasicAst.mfixpoint ->
    __ typing_result **)

let erase_mfix_obligation_1 _UU03a3_ _UU0393_ defs =
  let s = wf_ext_is_graph extraction_checker_flags _UU03a3_ in
  let Coq_existT (x, _) = s in
  let x0 =
    let rec check_types mfix acc =
      match mfix with
      | [] -> ret typing_monad __
      | def :: mfix0 ->
        bind typing_monad
          (Obj.magic infer_type extraction_checker_flags _UU03a3_
            (fun x0 _ -> infer extraction_checker_flags _UU03a3_ x x0)
            _UU0393_ def.dtype) (fun _ ->
          bind typing_monad
            (check_types mfix0
              (snoc acc
                (vass def.BasicAst.dname (lift (length acc) O def.dtype))))
            (fun _ -> ret typing_monad __))
    in check_types defs []
  in
  (match x0 with
   | Checked _ -> Obj.magic (Checked __)
   | TypeError t0 -> TypeError t0)

(** val erase_mfix :
    global_env_ext -> (context -> __ -> term -> E.term typing_result) ->
    PCUICEnvironment.context -> term BasicAst.mfixpoint -> E.term mfixpoint
    typing_result **)

let erase_mfix _UU03a3_ erase0 _UU0393_ defs =
  let _UU0393_' = app (fix_context defs) _UU0393_ in
  monad_map (Obj.magic typing_monad) (fun d ->
    bind (Obj.magic typing_monad)
      (Obj.magic erase_mfix_obligation_1 _UU03a3_ _UU0393_ defs) (fun _ ->
      bind (Obj.magic typing_monad)
        (Obj.magic erase0 _UU0393_' __ d.BasicAst.dbody) (fun dbody' ->
        ret (Obj.magic typing_monad) { E.dname = d.BasicAst.dname; E.dbody =
          dbody'; E.rarg = d.BasicAst.rarg }))) defs

(** val erase : global_env_ext -> context -> term -> E.term typing_result **)

let rec erase _UU03a3_ _UU0393_ t0 =
  match is_erasable _UU03a3_ _UU0393_ t0 with
  | Checked a ->
    if a
    then ret (Obj.magic typing_monad) E.Coq_tBox
    else (match t0 with
          | Coq_tRel n -> ret (Obj.magic typing_monad) (E.Coq_tRel n)
          | Coq_tVar i -> ret (Obj.magic typing_monad) (E.Coq_tVar i)
          | Coq_tEvar (n, l) ->
            bind (Obj.magic typing_monad)
              (monad_map (Obj.magic typing_monad) (fun t1 ->
                erase _UU03a3_ _UU0393_ t1) l) (fun l' ->
              ret (Obj.magic typing_monad) (E.Coq_tEvar (n, l')))
          | Coq_tLambda (na, a0, t1) ->
            bind (Obj.magic typing_monad)
              (erase _UU03a3_ ((vass na a0) :: _UU0393_) t1) (fun t' ->
              let dummy =
                match flag_of_type _UU03a3_ _UU0393_ a0 with
                | Checked a1 -> a1
                | TypeError _ -> false
              in
              ret (Obj.magic typing_monad) (E.Coq_tLambda ({ E.binder_name =
                na; E.binder_dummy = dummy }, t')))
          | Coq_tLetIn (na, b, b0, t1) ->
            bind (Obj.magic typing_monad) (erase _UU03a3_ _UU0393_ b)
              (fun b' ->
              bind (Obj.magic typing_monad)
                (erase _UU03a3_ ((vdef na b b0) :: _UU0393_) t1) (fun t1' ->
                let dummy =
                  match flag_of_type _UU03a3_ _UU0393_ b0 with
                  | Checked a0 -> a0
                  | TypeError _ -> false
                in
                ret (Obj.magic typing_monad) (E.Coq_tLetIn ({ E.binder_name =
                  na; E.binder_dummy = dummy }, b', t1'))))
          | Coq_tApp (u, v) ->
            bind (Obj.magic typing_monad) (erase _UU03a3_ _UU0393_ u)
              (fun f' ->
              bind (Obj.magic typing_monad) (erase _UU03a3_ _UU0393_ v)
                (fun l' -> ret (Obj.magic typing_monad) (E.Coq_tApp (f', l'))))
          | Coq_tConst (k, _) -> ret (Obj.magic typing_monad) (E.Coq_tConst k)
          | Coq_tConstruct (ind, n, _) ->
            ret (Obj.magic typing_monad) (E.Coq_tConstruct (ind, n))
          | Coq_tCase (indn, _, c, brs) ->
            bind (Obj.magic typing_monad) (erase _UU03a3_ _UU0393_ c)
              (fun c' ->
              bind (Obj.magic typing_monad)
                (monad_map (Obj.magic typing_monad) (fun x ->
                  bind (Obj.magic typing_monad)
                    (erase _UU03a3_ _UU0393_ (snd x)) (fun x' ->
                    ret (Obj.magic typing_monad) ((fst x), x'))) brs)
                (fun brs' ->
                ret (Obj.magic typing_monad) (E.Coq_tCase (indn, c', brs'))))
          | Coq_tProj (p, c) ->
            bind (Obj.magic typing_monad) (erase _UU03a3_ _UU0393_ c)
              (fun c' -> ret (Obj.magic typing_monad) (E.Coq_tProj (p, c')))
          | Coq_tFix (mfix, idx) ->
            bind (Obj.magic typing_monad)
              (Obj.magic erase_mfix _UU03a3_ (fun _UU0393_0 _ t1 ->
                erase _UU03a3_ _UU0393_0 t1) _UU0393_ mfix) (fun mfix' ->
              ret (Obj.magic typing_monad) (E.Coq_tFix (mfix', idx)))
          | Coq_tCoFix (mfix, idx) ->
            bind (Obj.magic typing_monad)
              (Obj.magic erase_mfix _UU03a3_ (fun _UU0393_0 _ t1 ->
                erase _UU03a3_ _UU0393_0 t1) _UU0393_ mfix) (fun mfix' ->
              ret (Obj.magic typing_monad) (E.Coq_tCoFix (mfix', idx)))
          | _ -> ret (Obj.magic typing_monad) E.Coq_tBox)
  | TypeError t1 -> TypeError t1

(** val optM : 'a1 coq_Monad -> 'a2 option -> ('a2 -> 'a1) -> 'a1 **)

let optM h x f =
  match x with
  | Some x0 -> bind h (f x0) (fun y -> ret h (Some y))
  | None -> ret h None

(** val erase_constant_body :
    global_env_ext -> constant_body -> E.constant_body typing_result **)

let erase_constant_body _UU03a3_ cb =
  bind (Obj.magic typing_monad) (Obj.magic erase _UU03a3_ [] (cst_type cb))
    (fun _ ->
    bind (Obj.magic typing_monad)
      (optM (Obj.magic typing_monad) (cst_body cb) (fun b ->
        Obj.magic erase _UU03a3_ [] b)) (fun body ->
      ret (Obj.magic typing_monad) body))

(** val lift_opt_typing : 'a1 option -> type_error -> 'a1 typing_result **)

let lift_opt_typing a e =
  match a with
  | Some x -> ret (Obj.magic typing_monad) x
  | None -> raise (Obj.magic monad_exc) e

(** val erase_one_inductive_body :
    global_env_ext -> nat -> context -> one_inductive_body ->
    E.one_inductive_body typing_result **)

let erase_one_inductive_body _UU03a3_ npars arities oib =
  bind (Obj.magic typing_monad)
    (lift_opt_typing
      (Obj.magic decompose_prod_n_assum [] npars (ind_type oib))
      (NotAnInductive (ind_type oib))) (fun _ ->
    bind (Obj.magic typing_monad)
      (Obj.magic erase _UU03a3_ [] (ind_type oib)) (fun _ ->
      bind (Obj.magic typing_monad)
        (monad_map (Obj.magic typing_monad) (fun pat ->
          let (y0, z) = pat in
          let (x, y) = y0 in
          bind (Obj.magic typing_monad) (Obj.magic erase _UU03a3_ arities y)
            (fun y' -> ret (Obj.magic typing_monad) ((x, y'), z)))
          (ind_ctors oib)) (fun ctors ->
        bind (Obj.magic typing_monad)
          (monad_map (Obj.magic typing_monad) (fun pat ->
            let (x, y) = pat in
            bind (Obj.magic typing_monad) (Obj.magic erase _UU03a3_ [] y)
              (fun y' -> ret (Obj.magic typing_monad) (x, y')))
            (ind_projs oib)) (fun projs ->
          ret (Obj.magic typing_monad) { E.ind_name = (ind_name oib);
            E.ind_kelim = (ind_kelim oib); E.ind_ctors = ctors; E.ind_projs =
            projs }))))

(** val erase_mutual_inductive_body :
    PCUICEnvironment.global_env_ext -> mutual_inductive_body ->
    E.mutual_inductive_body typing_result **)

let erase_mutual_inductive_body _UU03a3_ mib =
  let bds = ind_bodies mib in
  let arities = arities_context bds in
  bind (Obj.magic typing_monad)
    (monad_map (Obj.magic typing_monad)
      (Obj.magic erase_one_inductive_body _UU03a3_ (ind_npars mib) arities)
      bds) (fun bodies ->
    ret (Obj.magic typing_monad) { E.ind_npars = (ind_npars mib);
      E.ind_bodies = bodies })

(** val erase_global_decls :
    PCUICEnvironment.global_env -> E.global_declarations typing_result **)

let rec erase_global_decls = function
| [] -> Obj.magic ret typing_monad []
| p :: _UU03a3_0 ->
  let (kn, g) = p in
  (match g with
   | PCUICEnvironment.ConstantDecl cb ->
     let kn0 = Obj.magic kn in
     let cb0 = Obj.magic cb in
     let _UU03a3_1 = Obj.magic _UU03a3_0 in
     Obj.magic bind typing_monad
       (Obj.magic erase_constant_body (_UU03a3_1, (cst_universes cb0)) cb0)
       (fun cb' ->
       bind typing_monad (Obj.magic erase_global_decls _UU03a3_1)
         (fun _UU03a3_' ->
         ret typing_monad ((kn0, (E.ConstantDecl cb')) :: _UU03a3_')))
   | PCUICEnvironment.InductiveDecl mib ->
     let kn0 = Obj.magic kn in
     let mib0 = Obj.magic mib in
     let _UU03a3_1 = Obj.magic _UU03a3_0 in
     Obj.magic bind typing_monad
       (Obj.magic erase_mutual_inductive_body (_UU03a3_1,
         (ind_universes mib0)) mib0) (fun mib' ->
       bind typing_monad (Obj.magic erase_global_decls _UU03a3_1)
         (fun _UU03a3_' ->
         ret typing_monad ((kn0, (E.InductiveDecl mib')) :: _UU03a3_'))))

(** val erase_global :
    PCUICEnvironment.global_env -> E.global_declarations typing_result **)

let erase_global _UU03a3_ =
  bind (Obj.magic typing_monad) (erase_global_decls _UU03a3_)
    (fun _UU03a3_' -> ret (Obj.magic typing_monad) _UU03a3_')
