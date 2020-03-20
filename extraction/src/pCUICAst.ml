open BasicAst
open Datatypes
open List0
open MCList
open Nat0
open Universes0

module Coq__1 = struct
 type term =
 | Coq_tRel of nat
 | Coq_tVar of ident
 | Coq_tEvar of nat * term list
 | Coq_tSort of Universe.t
 | Coq_tProd of name * term * term
 | Coq_tLambda of name * term * term
 | Coq_tLetIn of name * term * term * term
 | Coq_tApp of term * term
 | Coq_tConst of kername * Instance.t
 | Coq_tInd of inductive * Instance.t
 | Coq_tConstruct of inductive * nat * Instance.t
 | Coq_tCase of (inductive * nat) * term * term * (nat * term) list
 | Coq_tProj of projection * term
 | Coq_tFix of term mfixpoint * nat
 | Coq_tCoFix of term mfixpoint * nat
end
include Coq__1

(** val mkApps : term -> term list -> term **)

let rec mkApps t0 = function
| [] -> t0
| u :: us0 -> mkApps (Coq_tApp (t0, u)) us0

(** val isLambda : term -> bool **)

let isLambda = function
| Coq_tLambda (_, _, _) -> true
| _ -> false

module PCUICTerm =
 struct
  type term = Coq__1.term

  (** val tRel : nat -> Coq__1.term **)

  let tRel x =
    Coq_tRel x

  (** val tSort : Universe.t -> Coq__1.term **)

  let tSort x =
    Coq_tSort x

  (** val tProd : name -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tProd x x0 x1 =
    Coq_tProd (x, x0, x1)

  (** val tLambda : name -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tLambda x x0 x1 =
    Coq_tLambda (x, x0, x1)

  (** val tLetIn :
      name -> Coq__1.term -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tLetIn x x0 x1 x2 =
    Coq_tLetIn (x, x0, x1, x2)

  (** val tInd : inductive -> Instance.t -> Coq__1.term **)

  let tInd x x0 =
    Coq_tInd (x, x0)

  (** val mkApps : Coq__1.term -> Coq__1.term list -> Coq__1.term **)

  let mkApps =
    mkApps
 end

module PCUICEnvironment = Environment.Environment(PCUICTerm)

type context_decl = PCUICEnvironment.context_decl = { decl_name : name;
                                                      decl_body : PCUICTerm.term
                                                                  option;
                                                      decl_type : PCUICTerm.term }

(** val decl_name : context_decl -> name **)

let decl_name c =
  c.decl_name

(** val decl_body : context_decl -> PCUICTerm.term option **)

let decl_body c =
  c.decl_body

(** val decl_type : context_decl -> PCUICTerm.term **)

let decl_type c =
  c.decl_type

(** val vass : name -> PCUICTerm.term -> context_decl **)

let vass x a =
  { decl_name = x; decl_body = None; decl_type = a }

(** val vdef : name -> PCUICTerm.term -> PCUICTerm.term -> context_decl **)

let vdef x t0 a =
  { decl_name = x; decl_body = (Some t0); decl_type = a }

type context = context_decl list

(** val snoc : 'a1 list -> 'a1 -> 'a1 list **)

let snoc _UU0393_ d =
  d :: _UU0393_

(** val map_decl :
    (PCUICTerm.term -> PCUICTerm.term) -> context_decl -> context_decl **)

let map_decl f d =
  { decl_name = (decl_name d); decl_body = (option_map f (decl_body d));
    decl_type = (f (decl_type d)) }

(** val map_context :
    (PCUICTerm.term -> PCUICTerm.term) -> context_decl list -> context_decl
    list **)

let map_context f c =
  map (map_decl f) c

type one_inductive_body = PCUICEnvironment.one_inductive_body = { ind_name : 
                                                                  ident;
                                                                  ind_type : 
                                                                  PCUICTerm.term;
                                                                  ind_kelim : 
                                                                  sort_family;
                                                                  ind_ctors : 
                                                                  ((ident * PCUICTerm.term) * nat)
                                                                  list;
                                                                  ind_projs : 
                                                                  (ident * PCUICTerm.term)
                                                                  list }

(** val ind_name : one_inductive_body -> ident **)

let ind_name o =
  o.ind_name

(** val ind_type : one_inductive_body -> PCUICTerm.term **)

let ind_type o =
  o.ind_type

(** val ind_kelim : one_inductive_body -> sort_family **)

let ind_kelim o =
  o.ind_kelim

(** val ind_ctors :
    one_inductive_body -> ((ident * PCUICTerm.term) * nat) list **)

let ind_ctors o =
  o.ind_ctors

(** val ind_projs : one_inductive_body -> (ident * PCUICTerm.term) list **)

let ind_projs o =
  o.ind_projs

type mutual_inductive_body = PCUICEnvironment.mutual_inductive_body = { 
ind_finite : recursivity_kind; ind_npars : nat; ind_params : context;
ind_bodies : one_inductive_body list; ind_universes : universes_decl;
ind_variance : Variance.t list option }

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

type constant_body = PCUICEnvironment.constant_body = { cst_type : PCUICTerm.term;
                                                        cst_body : PCUICTerm.term
                                                                   option;
                                                        cst_universes : 
                                                        universes_decl }

(** val cst_type : constant_body -> PCUICTerm.term **)

let cst_type c =
  c.cst_type

(** val cst_body : constant_body -> PCUICTerm.term option **)

let cst_body c =
  c.cst_body

(** val cst_universes : constant_body -> universes_decl **)

let cst_universes c =
  c.cst_universes

type global_decl = PCUICEnvironment.global_decl =
| ConstantDecl of constant_body
| InductiveDecl of mutual_inductive_body

type global_env = (kername * global_decl) list

type global_env_ext = global_env * universes_decl

(** val fst_ctx : global_env_ext -> global_env **)

let fst_ctx =
  fst

(** val empty_ext : global_env -> global_env_ext **)

let empty_ext _UU03a3_ =
  (_UU03a3_, (Monomorphic_ctx ContextSet.empty))

(** val app_context : context -> context -> context **)

let app_context _UU0393_ _UU0393_' =
  app _UU0393_' _UU0393_

(** val mkProd_or_LetIn : context_decl -> PCUICTerm.term -> PCUICTerm.term **)

let mkProd_or_LetIn d t0 =
  match decl_body d with
  | Some b -> PCUICTerm.tLetIn (decl_name d) b (decl_type d) t0
  | None -> PCUICTerm.tProd (decl_name d) (decl_type d) t0

(** val it_mkProd_or_LetIn : context -> PCUICTerm.term -> PCUICTerm.term **)

let it_mkProd_or_LetIn l t0 =
  fold_left (fun acc d -> mkProd_or_LetIn d acc) l t0

(** val reln :
    PCUICTerm.term list -> nat -> context_decl list -> PCUICTerm.term list **)

let rec reln l p = function
| [] -> l
| c :: hyps ->
  let { decl_name = _; decl_body = decl_body0; decl_type = _ } = c in
  (match decl_body0 with
   | Some _ -> reln l (add p (S O)) hyps
   | None -> reln ((PCUICTerm.tRel p) :: l) (add p (S O)) hyps)

(** val to_extended_list_k :
    context_decl list -> nat -> PCUICTerm.term list **)

let to_extended_list_k _UU0393_ k =
  reln [] k _UU0393_

(** val to_extended_list : context_decl list -> PCUICTerm.term list **)

let to_extended_list _UU0393_ =
  to_extended_list_k _UU0393_ O

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
