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
open PCUICSafeRetyping
open Specif
open Universes0
open Config0
open Monad_utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val is_arity :
    global_env_ext -> PCUICEnvironment.context -> term -> bool typing_result **)

let is_arity _UU03a3_ a a0 =
  let rec fix_F x =
    let _UU0393_ = pr1 x in
    let t = pr1 (pr2 (pr2 x)) in
    (match reduce_to_sort extraction_checker_flags _UU03a3_ _UU0393_ t with
     | Checked _ -> ret (Obj.magic typing_monad) true
     | TypeError _ ->
       (match inspect
                (reduce_to_prod extraction_checker_flags _UU03a3_ _UU0393_ t) with
        | Checked a1 ->
          let Coq_existT (x0, s) = a1 in
          let Coq_existT (x1, s0) = s in
          let Coq_existT (x2, _) = s0 in
          (match let y = (snoc _UU0393_ (vass x0 x1)),(__,(x2,__)) in fix_F y with
           | Checked a2 -> ret (Obj.magic typing_monad) a2
           | TypeError t0 -> TypeError t0)
        | TypeError t0 ->
          (match t0 with
           | NotAProduct (_, _) -> ret (Obj.magic typing_monad) false
           | x0 -> TypeError x0)))
  in fix_F (a,(__,(a0,__)))

(** val is_erasable :
    global_env_ext -> context -> term -> bool typing_result **)

let is_erasable sigma gamma t =
  bind (Obj.magic typing_monad)
    (Obj.magic type_of extraction_checker_flags sigma gamma t) (fun pat ->
    let Coq_existT (t0, _) = pat in
    let t1 = Obj.magic t0 in
    Obj.magic bind typing_monad (Obj.magic is_arity sigma gamma t1) (fun b ->
      if b
      then ret typing_monad true
      else bind typing_monad
             (Obj.magic type_of extraction_checker_flags sigma gamma t1)
             (fun pat0 ->
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
  bind (Obj.magic typing_monad) (Obj.magic is_arity sigma gamma ty) (fun b ->
    if b
    then ret (Obj.magic typing_monad) true
    else ret (Obj.magic typing_monad) false)

(** val is_box : E.term -> bool **)

let is_box = function
| E.Coq_tBox -> true
| _ -> false

(** val erase_mfix_obligation_1 :
    global_env_ext -> context_decl list -> term BasicAst.mfixpoint -> term
    BasicAst.def -> __ typing_result **)

let erase_mfix_obligation_1 _ _ _ _ =
  Checked __

(** val erase_mfix :
    global_env_ext -> (context -> term -> __ -> E.term typing_result) ->
    context_decl list -> term BasicAst.mfixpoint -> E.term mfixpoint
    typing_result **)

let erase_mfix _UU03a3_ erase0 _UU0393_ defs =
  let _UU0393_' = app (fix_context defs) _UU0393_ in
  monad_map (Obj.magic typing_monad) (fun d ->
    bind (Obj.magic typing_monad)
      (Obj.magic erase_mfix_obligation_1 _UU03a3_ _UU0393_ defs d) (fun _ ->
      bind (Obj.magic typing_monad)
        (Obj.magic erase0 _UU0393_' d.BasicAst.dbody __) (fun dbody' ->
        ret (Obj.magic typing_monad) { E.dname = d.BasicAst.dname; E.dbody =
          dbody'; E.rarg = d.BasicAst.rarg }))) defs

(** val erase : global_env_ext -> context -> term -> E.term typing_result **)

let rec erase _UU03a3_ _UU0393_ t =
  match is_erasable _UU03a3_ _UU0393_ t with
  | Checked a ->
    if a
    then ret (Obj.magic typing_monad) E.Coq_tBox
    else (match t with
          | Coq_tRel n -> ret (Obj.magic typing_monad) (E.Coq_tRel n)
          | Coq_tVar i -> ret (Obj.magic typing_monad) (E.Coq_tVar i)
          | Coq_tEvar (n, l) ->
            bind (Obj.magic typing_monad)
              (monad_map (Obj.magic typing_monad) (fun x ->
                erase _UU03a3_ _UU0393_ x) l) (fun l' ->
              ret (Obj.magic typing_monad) (E.Coq_tEvar (n, l')))
          | Coq_tLambda (na, a0, t0) ->
            bind (Obj.magic typing_monad)
              (erase _UU03a3_ ((vass na a0) :: _UU0393_) t0) (fun t' ->
              let dummy =
                match flag_of_type _UU03a3_ _UU0393_ a0 with
                | Checked a1 -> a1
                | TypeError _ -> false
              in
              ret (Obj.magic typing_monad) (E.Coq_tLambda ({ E.binder_name =
                na; E.binder_dummy = dummy }, t')))
          | Coq_tLetIn (na, b, b0, t0) ->
            bind (Obj.magic typing_monad) (erase _UU03a3_ _UU0393_ b)
              (fun b' ->
              bind (Obj.magic typing_monad)
                (erase _UU03a3_ ((vdef na b b0) :: _UU0393_) t0) (fun t1' ->
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
              if is_box c'
              then (match brs with
                    | [] ->
                      ret (Obj.magic typing_monad) (E.Coq_tCase (indn, c',
                        []))
                    | p0 :: _ ->
                      let (a0, b) = p0 in
                      bind (Obj.magic typing_monad)
                        (erase _UU03a3_ _UU0393_ b) (fun b' ->
                        ret (Obj.magic typing_monad)
                          (E.mkApps b' (repeat E.Coq_tBox a0))))
              else bind (Obj.magic typing_monad)
                     (monad_map (Obj.magic typing_monad) (fun x ->
                       bind (Obj.magic typing_monad)
                         (erase _UU03a3_ _UU0393_ (snd x)) (fun x' ->
                         ret (Obj.magic typing_monad) ((fst x), x'))) brs)
                     (fun brs' ->
                     ret (Obj.magic typing_monad) (E.Coq_tCase (indn, c',
                       brs'))))
          | Coq_tProj (p, c) ->
            bind (Obj.magic typing_monad) (erase _UU03a3_ _UU0393_ c)
              (fun c' ->
              if is_box c'
              then ret (Obj.magic typing_monad) E.Coq_tBox
              else ret (Obj.magic typing_monad) (E.Coq_tProj (p, c')))
          | Coq_tFix (mfix, idx) ->
            bind (Obj.magic typing_monad)
              (Obj.magic erase_mfix _UU03a3_ (fun _UU0393_0 t0 _ ->
                erase _UU03a3_ _UU0393_0 t0) _UU0393_ mfix) (fun mfix' ->
              ret (Obj.magic typing_monad) (E.Coq_tFix (mfix', idx)))
          | Coq_tCoFix (mfix, idx) ->
            bind (Obj.magic typing_monad)
              (Obj.magic erase_mfix _UU03a3_ (fun _UU0393_0 t0 _ ->
                erase _UU03a3_ _UU0393_0 t0) _UU0393_ mfix) (fun mfix' ->
              ret (Obj.magic typing_monad) (E.Coq_tCoFix (mfix', idx)))
          | _ -> ret (Obj.magic typing_monad) E.Coq_tBox)
  | TypeError t0 -> TypeError t0

(** val erase_constant_body :
    PCUICEnvironment.global_env_ext -> constant_body -> E.constant_body
    typing_result **)

let erase_constant_body _UU03a3_ cb =
  bind (Obj.magic typing_monad)
    (let filtered_var = cst_body cb in
     match filtered_var with
     | Some b ->
       let b0 = Obj.magic b in
       Obj.magic bind typing_monad (Obj.magic erase _UU03a3_ [] b0) (fun t ->
         ret typing_monad (Some t))
     | None -> Obj.magic ret typing_monad None) (fun body ->
    ret (Obj.magic typing_monad) body)

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
    Obj.magic bind typing_monad
      (monad_map typing_monad (fun pat ->
        let (p, z) = pat in
        let (x, y) = p in
        bind typing_monad (Obj.magic erase _UU03a3_ arities y) (fun y' ->
          ret typing_monad ((x, y'), z))) (ind_ctors oib)) (fun ctors ->
      bind typing_monad
        (monad_map typing_monad (fun pat ->
          let (x, y) = pat in
          bind typing_monad (Obj.magic erase _UU03a3_ [] y) (fun y' ->
            ret typing_monad (x, y'))) (ind_projs oib)) (fun projs ->
        ret typing_monad { E.ind_name = (ind_name oib); E.ind_kelim =
          (ind_kelim oib); E.ind_ctors = ctors; E.ind_projs = projs })))

(** val erase_mutual_inductive_body :
    global_env_ext -> mutual_inductive_body -> E.mutual_inductive_body
    typing_result **)

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
