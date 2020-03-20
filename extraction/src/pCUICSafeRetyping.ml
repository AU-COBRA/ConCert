open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICLiftSubst
open PCUICSafeChecker
open PCUICTyping
open PCUICUnivSubst
open Specif
open Universes0
open Config0
open Monad_utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val type_of_as_sort :
    checker_flags -> global_env_ext -> (context -> term -> __ -> (term, __)
    sigT typing_result) -> context -> term -> Universe.t typing_result **)

let type_of_as_sort cf _UU03a3_ type_of0 _UU0393_ t0 =
  bind (Obj.magic typing_monad) (Obj.magic type_of0 _UU0393_ t0 __)
    (fun tx ->
    bind (Obj.magic typing_monad)
      (Obj.magic reduce_to_sort cf _UU03a3_ _UU0393_ (projT1 tx)) (fun wfs ->
      ret (Obj.magic typing_monad) (projT1 wfs)))

(** val option_or :
    'a1 option -> type_error -> ('a1, __) sigT typing_result **)

let option_or a e =
  match a with
  | Some d ->
    let d0 = Obj.magic d in Obj.magic ret typing_monad (Coq_existT (d0, __))
  | None -> Obj.magic raise monad_exc e

(** val type_of :
    checker_flags -> global_env_ext -> context -> term -> (term, __) sigT
    typing_result **)

let rec type_of cf _UU03a3_ _UU0393_ = function
| Coq_tRel n ->
  bind (Obj.magic typing_monad)
    (option_or
      (option_map (fun x -> lift (S n) O (decl_type x))
        (nth_error _UU0393_ n)) (UnboundRel n)) (fun t1 ->
    ret (Obj.magic typing_monad) (Coq_existT ((projT1 t1), __)))
| Coq_tVar n -> raise (Obj.magic monad_exc) (UnboundVar n)
| Coq_tEvar (ev, _) -> raise (Obj.magic monad_exc) (UnboundEvar ev)
| Coq_tSort s ->
  ret (Obj.magic typing_monad) (Coq_existT ((Coq_tSort (Universe.try_suc s)),
    __))
| Coq_tProd (n, t1, b) ->
  bind (Obj.magic typing_monad)
    (Obj.magic type_of_as_sort cf _UU03a3_ (fun _UU0393_0 t2 _ ->
      type_of cf _UU03a3_ _UU0393_0 t2) _UU0393_ t1) (fun s1 ->
    bind (Obj.magic typing_monad)
      (Obj.magic type_of_as_sort cf _UU03a3_ (fun _UU0393_0 t2 _ ->
        type_of cf _UU03a3_ _UU0393_0 t2) (snoc _UU0393_ (vass n t1)) b)
      (fun s2 ->
      ret (Obj.magic typing_monad) (Coq_existT ((Coq_tSort
        (Universe.sort_of_product s1 s2)), __))))
| Coq_tLambda (n, t1, b) ->
  bind (Obj.magic typing_monad)
    (type_of cf _UU03a3_ (snoc _UU0393_ (vass n t1)) b) (fun t2 ->
    ret (Obj.magic typing_monad) (Coq_existT ((Coq_tProd (n, t1,
      (projT1 t2))), __)))
| Coq_tLetIn (n, b, b_ty, b') ->
  bind (Obj.magic typing_monad)
    (type_of cf _UU03a3_ (snoc _UU0393_ (vdef n b b_ty)) b') (fun b'_ty ->
    ret (Obj.magic typing_monad) (Coq_existT ((Coq_tLetIn (n, b, b_ty,
      (projT1 b'_ty))), __)))
| Coq_tApp (t1, a) ->
  bind (Obj.magic typing_monad) (type_of cf _UU03a3_ _UU0393_ t1) (fun ty ->
    bind (Obj.magic typing_monad)
      (Obj.magic reduce_to_prod cf _UU03a3_ _UU0393_ (projT1 ty)) (fun pi ->
      ret (Obj.magic typing_monad) (Coq_existT
        ((subst1 a O (projT1 (projT2 (projT2 pi)))), __))))
| Coq_tConst (cst, u) ->
  let filtered_var = lookup_env (fst _UU03a3_) cst in
  (match filtered_var with
   | Some g ->
     (match g with
      | PCUICEnvironment.ConstantDecl d ->
        let d0 = Obj.magic d in
        let ty = subst_instance_constr u (cst_type d0) in
        Obj.magic ret typing_monad (Coq_existT (ty, __))
      | PCUICEnvironment.InductiveDecl _ ->
        Obj.magic raise monad_exc (UndeclaredConstant cst))
   | None -> Obj.magic raise monad_exc (UndeclaredConstant cst))
| Coq_tInd (ind, u) ->
  bind (Obj.magic typing_monad) (Obj.magic lookup_ind_decl _UU03a3_ ind)
    (fun d ->
    let ty = subst_instance_constr u (ind_type (projT1 (projT2 d))) in
    ret (Obj.magic typing_monad) (Coq_existT (ty, __)))
| Coq_tConstruct (ind, k, u) ->
  bind (Obj.magic typing_monad) (Obj.magic lookup_ind_decl _UU03a3_ ind)
    (fun d ->
    let filtered_var = nth_error (ind_ctors (projT1 (projT2 d))) k in
    (match filtered_var with
     | Some cdecl ->
       let cdecl0 = Obj.magic cdecl in
       Obj.magic ret typing_monad (Coq_existT
         ((type_of_constructor (projT1 d) cdecl0 (ind, k) u), __))
     | None -> Obj.magic raise monad_exc (UndeclaredConstructor (ind, k))))
| Coq_tCase (indn, p, c, _) ->
  let (_, par) = indn in
  bind (Obj.magic typing_monad) (type_of cf _UU03a3_ _UU0393_ c) (fun ty ->
    bind (Obj.magic typing_monad)
      (Obj.magic reduce_to_ind cf _UU03a3_ _UU0393_ (projT1 ty))
      (fun indargs ->
      ret (Obj.magic typing_monad) (Coq_existT
        ((mkApps p
           (app (skipn par (projT1 (projT2 (projT2 indargs)))) (c :: []))),
        __))))
| Coq_tProj (p, c) ->
  let (p0, k) = p in
  let (ind, _) = p0 in
  bind (Obj.magic typing_monad) (Obj.magic lookup_ind_decl _UU03a3_ ind)
    (fun d ->
    let filtered_var = nth_error (ind_projs (projT1 (projT2 d))) k in
    (match filtered_var with
     | Some pdecl ->
       let pdecl0 = Obj.magic pdecl in
       Obj.magic bind typing_monad (Obj.magic type_of cf _UU03a3_ _UU0393_ c)
         (fun c_ty ->
         bind typing_monad
           (Obj.magic reduce_to_ind cf _UU03a3_ _UU0393_ (projT1 c_ty))
           (fun indargs ->
           let ty = snd pdecl0 in
           ret typing_monad (Coq_existT
             ((subst (c :: (rev (projT1 (projT2 (projT2 indargs))))) O
                (subst_instance_constr (projT1 (projT2 indargs)) ty)), __))))
     | None -> assert false (* absurd case *)))
| Coq_tFix (mfix, n) ->
  let filtered_var = nth_error mfix n in
  (match filtered_var with
   | Some f ->
     let f0 = Obj.magic f in
     Obj.magic ret typing_monad (Coq_existT (f0.dtype, __))
   | None -> Obj.magic raise monad_exc (IllFormedFix (mfix, n)))
| Coq_tCoFix (mfix, n) ->
  let filtered_var = nth_error mfix n in
  (match filtered_var with
   | Some f ->
     let f0 = Obj.magic f in
     Obj.magic ret typing_monad (Coq_existT (f0.dtype, __))
   | None -> Obj.magic raise monad_exc (IllFormedFix (mfix, n)))
