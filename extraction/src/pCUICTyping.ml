open BasicAst
open Datatypes
open List0
open MCList
open PCUICAst
open PCUICAstUtils
open PCUICLiftSubst
open PCUICUnivSubst
open Universes0
open Monad_utils

(** val lookup_env :
    PCUICEnvironment.global_env -> ident -> PCUICEnvironment.global_decl
    option **)

let rec lookup_env _UU03a3_ id =
  match _UU03a3_ with
  | [] -> None
  | d :: tl -> if ident_eq id (fst d) then Some (snd d) else lookup_env tl id

(** val on_udecl_decl :
    (universes_decl -> 'a1) -> PCUICEnvironment.global_decl -> 'a1 **)

let on_udecl_decl f = function
| PCUICEnvironment.ConstantDecl cb -> f (PCUICEnvironment.cst_universes cb)
| PCUICEnvironment.InductiveDecl mb -> f (PCUICEnvironment.ind_universes mb)

(** val monomorphic_udecl_decl :
    PCUICEnvironment.global_decl -> ContextSet.t **)

let monomorphic_udecl_decl =
  on_udecl_decl monomorphic_udecl

(** val monomorphic_levels_decl :
    PCUICEnvironment.global_decl -> LevelSet.t **)

let monomorphic_levels_decl x =
  fst (monomorphic_udecl_decl x)

(** val monomorphic_constraints_decl :
    PCUICEnvironment.global_decl -> ConstraintSet.t **)

let monomorphic_constraints_decl x =
  snd (monomorphic_udecl_decl x)

(** val universes_decl_of_decl :
    PCUICEnvironment.global_decl -> universes_decl **)

let universes_decl_of_decl =
  on_udecl_decl (fun x -> x)

(** val global_levels : PCUICEnvironment.global_env -> LevelSet.t **)

let global_levels _UU03a3_ =
  fold_right (fun decl lvls ->
    LevelSet.union (monomorphic_levels_decl (snd decl)) lvls)
    (coq_LevelSet_pair Level.Coq_lSet Level.Coq_lProp) _UU03a3_

(** val global_constraints :
    PCUICEnvironment.global_env -> ConstraintSet.t **)

let global_constraints _UU03a3_ =
  fold_right (fun decl ctrs ->
    ConstraintSet.union (monomorphic_constraints_decl (snd decl)) ctrs)
    ConstraintSet.empty _UU03a3_

(** val global_ext_levels : PCUICEnvironment.global_env_ext -> LevelSet.t **)

let global_ext_levels _UU03a3_ =
  LevelSet.union (levels_of_udecl (snd _UU03a3_))
    (global_levels (fst _UU03a3_))

(** val global_ext_constraints :
    PCUICEnvironment.global_env_ext -> ConstraintSet.t **)

let global_ext_constraints _UU03a3_ =
  ConstraintSet.union (constraints_of_udecl (snd _UU03a3_))
    (global_constraints (fst _UU03a3_))

(** val inds :
    kername -> Instance.t -> one_inductive_body list -> term list **)

let inds ind u l =
  let rec aux = function
  | O -> []
  | S n0 ->
    (Coq_tInd ({ inductive_mind = ind; inductive_ind = n0 }, u)) :: (aux n0)
  in aux (length l)

(** val type_of_constructor :
    mutual_inductive_body -> ((ident * term) * nat) -> (inductive * nat) ->
    Level.t list -> term **)

let type_of_constructor mdecl cdecl c u =
  let mind = (fst c).inductive_mind in
  subst (inds mind u (ind_bodies mdecl)) O
    (subst_instance_constr u (snd (fst cdecl)))

(** val fix_subst : term mfixpoint -> term list **)

let fix_subst l =
  let rec aux = function
  | O -> []
  | S n0 -> (Coq_tFix (l, n0)) :: (aux n0)
  in aux (length l)

(** val unfold_fix : term mfixpoint -> nat -> (nat * term) option **)

let unfold_fix mfix idx =
  match nth_error mfix idx with
  | Some d ->
    if isLambda d.dbody
    then Some (d.rarg, (subst (fix_subst mfix) O d.dbody))
    else None
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

(** val tDummy : term **)

let tDummy =
  Coq_tVar []

(** val iota_red : nat -> nat -> term list -> (nat * term) list -> term **)

let iota_red npar c args brs =
  mkApps (snd (nth c brs (O, tDummy))) (skipn npar args)

(** val destArity :
    context_decl list -> term -> (context_decl list * Universe.t) option **)

let rec destArity _UU0393_ = function
| Coq_tSort s -> Some (_UU0393_, s)
| Coq_tProd (na, t1, b) -> destArity (snoc _UU0393_ (vass na t1)) b
| Coq_tLetIn (na, b, b_ty, b') ->
  destArity (snoc _UU0393_ (vdef na b b_ty)) b'
| _ -> None

(** val fix_guard : term mfixpoint -> bool **)

let fix_guard = (fun x -> true)

(** val ind_guard : mutual_inductive_body -> bool **)

let ind_guard = (fun x -> true)

(** val instantiate_params_subst :
    context_decl list -> term list -> term list -> term -> (term list * term)
    option **)

let rec instantiate_params_subst params pars s ty =
  match params with
  | [] -> (match pars with
           | [] -> Some (s, ty)
           | _ :: _ -> None)
  | d :: params0 ->
    (match decl_body d with
     | Some b ->
       (match ty with
        | Coq_tLetIn (_, _, _, b') ->
          instantiate_params_subst params0 pars ((subst s O b) :: s) b'
        | _ -> None)
     | None ->
       (match ty with
        | Coq_tProd (_, _, b) ->
          (match pars with
           | [] -> None
           | hd :: tl -> instantiate_params_subst params0 tl (hd :: s) b)
        | _ -> None))

(** val instantiate_params : context -> term list -> term -> term option **)

let instantiate_params params pars ty =
  match instantiate_params_subst (rev params) pars [] ty with
  | Some p -> let (s, ty0) = p in Some (subst s O ty0)
  | None -> None

(** val build_branches_type :
    inductive -> mutual_inductive_body -> one_inductive_body -> term list ->
    Instance.t -> term -> (nat * term) option list **)

let build_branches_type ind mdecl idecl params u p =
  let inds0 = inds ind.inductive_mind u (ind_bodies mdecl) in
  let branch_type = fun i pat ->
    let (y, ar) = pat in
    let (_, t0) = y in
    let ty = subst inds0 O (subst_instance_constr u t0) in
    (match instantiate_params (subst_instance_context u (ind_params mdecl))
             params ty with
     | Some ty0 ->
       let (sign, ccl) = decompose_prod_assum [] ty0 in
       let nargs = length sign in
       let allargs = snd (decompose_app ccl) in
       let (paramrels, args) = chop (ind_npars mdecl) allargs in
       let cstr = Coq_tConstruct (ind, i, u) in
       let args0 =
         app args
           ((mkApps cstr (app paramrels (to_extended_list sign))) :: [])
       in
       Some (ar, (it_mkProd_or_LetIn sign (mkApps (lift nargs O p) args0)))
     | None -> None)
  in
  mapi branch_type (ind_ctors idecl)

(** val build_case_predicate_type :
    inductive -> mutual_inductive_body -> one_inductive_body -> term list ->
    Instance.t -> Universe.t -> term option **)

let build_case_predicate_type ind mdecl idecl params u ps =
  bind (Obj.magic option_monad)
    (instantiate_params (subst_instance_context u (ind_params mdecl)) params
      (subst_instance_constr u (ind_type idecl))) (fun x ->
    bind (Obj.magic option_monad) (Obj.magic destArity [] x) (fun x0 ->
      let inddecl = { decl_name = (Coq_nNamed (ind_name idecl)); decl_body =
        None; decl_type =
        (mkApps (Coq_tInd (ind, u))
          (app (map (lift (length (fst x0)) O) params)
            (to_extended_list (fst x0)))) }
      in
      ret (Obj.magic option_monad)
        (it_mkProd_or_LetIn (snoc (fst x0) inddecl) (Coq_tSort ps))))
