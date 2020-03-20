open BasicAst
open Datatypes
open List0
open MCList
open MCProd
open MCString
open Nat0
open Universes0

module type Term =
 sig
  type term

  val tRel : nat -> term

  val tSort : Universe.t -> term

  val tProd : name -> term -> term -> term

  val tLambda : name -> term -> term -> term

  val tLetIn : name -> term -> term -> term -> term

  val tInd : inductive -> Instance.t -> term

  val mkApps : term -> term list -> term
 end

module Environment =
 functor (T:Term) ->
 struct
  type context_decl = { decl_name : name; decl_body : T.term option;
                        decl_type : T.term }

  (** val decl_name : context_decl -> name **)

  let decl_name c =
    c.decl_name

  (** val decl_body : context_decl -> T.term option **)

  let decl_body c =
    c.decl_body

  (** val decl_type : context_decl -> T.term **)

  let decl_type c =
    c.decl_type

  (** val vass : name -> T.term -> context_decl **)

  let vass x a =
    { decl_name = x; decl_body = None; decl_type = a }

  (** val vdef : name -> T.term -> T.term -> context_decl **)

  let vdef x t0 a =
    { decl_name = x; decl_body = (Some t0); decl_type = a }

  type context = context_decl list

  (** val snoc : 'a1 list -> 'a1 -> 'a1 list **)

  let snoc _UU0393_ d =
    d :: _UU0393_

  (** val map_decl : (T.term -> T.term) -> context_decl -> context_decl **)

  let map_decl f d =
    { decl_name = (decl_name d); decl_body = (option_map f (decl_body d));
      decl_type = (f (decl_type d)) }

  (** val map_context :
      (T.term -> T.term) -> context_decl list -> context_decl list **)

  let map_context f c =
    map (map_decl f) c

  (** val fold_context : (nat -> T.term -> T.term) -> context -> context **)

  let fold_context f _UU0393_ =
    rev (mapi (fun k' decl -> map_decl (f k') decl) (rev _UU0393_))

  type one_inductive_body = { ind_name : ident; ind_type : T.term;
                              ind_kelim : sort_family;
                              ind_ctors : ((ident * T.term) * nat) list;
                              ind_projs : (ident * T.term) list }

  (** val ind_name : one_inductive_body -> ident **)

  let ind_name o =
    o.ind_name

  (** val ind_type : one_inductive_body -> T.term **)

  let ind_type o =
    o.ind_type

  (** val ind_kelim : one_inductive_body -> sort_family **)

  let ind_kelim o =
    o.ind_kelim

  (** val ind_ctors : one_inductive_body -> ((ident * T.term) * nat) list **)

  let ind_ctors o =
    o.ind_ctors

  (** val ind_projs : one_inductive_body -> (ident * T.term) list **)

  let ind_projs o =
    o.ind_projs

  (** val map_one_inductive_body :
      nat -> nat -> (nat -> T.term -> T.term) -> nat -> one_inductive_body ->
      one_inductive_body **)

  let map_one_inductive_body npars arities f _ m =
    let { ind_name = ind_name0; ind_type = ind_type0; ind_kelim = ind_kelim0;
      ind_ctors = ind_ctors0; ind_projs = ind_projs0 } = m
    in
    { ind_name = ind_name0; ind_type = (f O ind_type0); ind_kelim =
    ind_kelim0; ind_ctors = (map (on_pi2 (f arities)) ind_ctors0);
    ind_projs = (map (on_snd (f (S npars))) ind_projs0) }

  type mutual_inductive_body = { ind_finite : recursivity_kind;
                                 ind_npars : nat; ind_params : context;
                                 ind_bodies : one_inductive_body list;
                                 ind_universes : universes_decl;
                                 ind_variance : Variance.t list option }

  (** val ind_finite : mutual_inductive_body -> recursivity_kind **)

  let ind_finite m =
    m.ind_finite

  (** val ind_npars : mutual_inductive_body -> nat **)

  let ind_npars m =
    m.ind_npars

  (** val ind_params : mutual_inductive_body -> context **)

  let ind_params m =
    m.ind_params

  (** val ind_bodies : mutual_inductive_body -> one_inductive_body list **)

  let ind_bodies m =
    m.ind_bodies

  (** val ind_universes : mutual_inductive_body -> universes_decl **)

  let ind_universes m =
    m.ind_universes

  (** val ind_variance : mutual_inductive_body -> Variance.t list option **)

  let ind_variance m =
    m.ind_variance

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl }

  (** val cst_type : constant_body -> T.term **)

  let cst_type c =
    c.cst_type

  (** val cst_body : constant_body -> T.term option **)

  let cst_body c =
    c.cst_body

  (** val cst_universes : constant_body -> universes_decl **)

  let cst_universes c =
    c.cst_universes

  (** val map_constant_body :
      (T.term -> T.term) -> constant_body -> constant_body **)

  let map_constant_body f decl =
    { cst_type = (f (cst_type decl)); cst_body =
      (option_map f (cst_body decl)); cst_universes = (cst_universes decl) }

  type global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body

  (** val global_decl_rect :
      (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
      -> 'a1 **)

  let global_decl_rect f f0 = function
  | ConstantDecl x -> f x
  | InductiveDecl x -> f0 x

  (** val global_decl_rec :
      (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
      -> 'a1 **)

  let global_decl_rec f f0 = function
  | ConstantDecl x -> f x
  | InductiveDecl x -> f0 x

  type global_env = (kername * global_decl) list

  type global_env_ext = global_env * universes_decl

  (** val fst_ctx : global_env_ext -> global_env **)

  let fst_ctx =
    fst

  (** val empty_ext : global_env -> global_env_ext **)

  let empty_ext _UU03a3_ =
    (_UU03a3_, (Monomorphic_ctx ContextSet.empty))

  type program = global_env * T.term

  (** val app_context : context -> context -> context **)

  let app_context _UU0393_ _UU0393_' =
    app _UU0393_' _UU0393_

  (** val mkLambda_or_LetIn : context_decl -> T.term -> T.term **)

  let mkLambda_or_LetIn d t0 =
    match decl_body d with
    | Some b -> T.tLetIn (decl_name d) b (decl_type d) t0
    | None -> T.tLambda (decl_name d) (decl_type d) t0

  (** val it_mkLambda_or_LetIn : context -> T.term -> T.term **)

  let it_mkLambda_or_LetIn l t0 =
    fold_left (fun acc d -> mkLambda_or_LetIn d acc) l t0

  (** val mkProd_or_LetIn : context_decl -> T.term -> T.term **)

  let mkProd_or_LetIn d t0 =
    match decl_body d with
    | Some b -> T.tLetIn (decl_name d) b (decl_type d) t0
    | None -> T.tProd (decl_name d) (decl_type d) t0

  (** val it_mkProd_or_LetIn : context -> T.term -> T.term **)

  let it_mkProd_or_LetIn l t0 =
    fold_left (fun acc d -> mkProd_or_LetIn d acc) l t0

  (** val reln : T.term list -> nat -> context_decl list -> T.term list **)

  let rec reln l p = function
  | [] -> l
  | c :: hyps ->
    let { decl_name = _; decl_body = decl_body0; decl_type = _ } = c in
    (match decl_body0 with
     | Some _ -> reln l (add p (S O)) hyps
     | None -> reln ((T.tRel p) :: l) (add p (S O)) hyps)

  (** val to_extended_list_k : context_decl list -> nat -> T.term list **)

  let to_extended_list_k _UU0393_ k =
    reln [] k _UU0393_

  (** val to_extended_list : context_decl list -> T.term list **)

  let to_extended_list _UU0393_ =
    to_extended_list_k _UU0393_ O

  (** val reln_alt : nat -> context_decl list -> T.term list **)

  let rec reln_alt p = function
  | [] -> []
  | y :: _UU0393_0 ->
    let { decl_name = _; decl_body = decl_body0; decl_type = _ } = y in
    (match decl_body0 with
     | Some _ -> reln_alt (add p (S O)) _UU0393_0
     | None -> (T.tRel p) :: (reln_alt (add p (S O)) _UU0393_0))

  (** val arities_context : one_inductive_body list -> context_decl list **)

  let arities_context l =
    rev_map (fun ind -> vass (Coq_nNamed (ind_name ind)) (ind_type ind)) l

  (** val context_assumptions : context -> nat **)

  let rec context_assumptions = function
  | [] -> O
  | d :: _UU0393_0 ->
    (match decl_body d with
     | Some _ -> context_assumptions _UU0393_0
     | None -> S (context_assumptions _UU0393_0))

  (** val map_mutual_inductive_body :
      (nat -> T.term -> T.term) -> mutual_inductive_body ->
      mutual_inductive_body **)

  let map_mutual_inductive_body f m =
    let { ind_finite = finite; ind_npars = ind_npars0; ind_params = ind_pars;
      ind_bodies = ind_bodies0; ind_universes = ind_universes0;
      ind_variance = ind_variance0 } = m
    in
    let arities = arities_context ind_bodies0 in
    let pars = fold_context f ind_pars in
    { ind_finite = finite; ind_npars = ind_npars0; ind_params = pars;
    ind_bodies =
    (mapi
      (map_one_inductive_body (context_assumptions pars) (length arities) f)
      ind_bodies0); ind_universes = ind_universes0; ind_variance =
    ind_variance0 }

  (** val lookup_mind_decl :
      ident -> global_env -> mutual_inductive_body option **)

  let rec lookup_mind_decl id = function
  | [] -> None
  | p :: tl ->
    let (kn, g) = p in
    (match g with
     | ConstantDecl _ -> lookup_mind_decl id tl
     | InductiveDecl d ->
       if eq_string kn id then Some d else lookup_mind_decl id tl)
 end
