open BasicAst
open Datatypes
open List0
open Universes0

module Coq__1 = struct
 type term =
 | Coq_tRel of nat
 | Coq_tVar of ident
 | Coq_tEvar of nat * term list
 | Coq_tSort of Universe.t
 | Coq_tCast of term * cast_kind * term
 | Coq_tProd of name * term * term
 | Coq_tLambda of name * term * term
 | Coq_tLetIn of name * term * term * term
 | Coq_tApp of term * term list
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

let mkApps t0 us = match us with
| [] -> t0
| _ :: _ ->
  (match t0 with
   | Coq_tApp (f, args) -> Coq_tApp (f, (app args us))
   | _ -> Coq_tApp (t0, us))

module TemplateTerm =
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

module TemplateEnvironment = Environment.Environment(TemplateTerm)

type context_decl = TemplateEnvironment.context_decl = { decl_name : 
                                                         name;
                                                         decl_body : 
                                                         TemplateTerm.term
                                                         option;
                                                         decl_type : 
                                                         TemplateTerm.term }

(** val decl_name : context_decl -> name **)

let decl_name c =
  c.decl_name

(** val decl_body : context_decl -> TemplateTerm.term option **)

let decl_body c =
  c.decl_body

(** val decl_type : context_decl -> TemplateTerm.term **)

let decl_type c =
  c.decl_type

(** val vass : name -> TemplateTerm.term -> context_decl **)

let vass x a =
  { decl_name = x; decl_body = None; decl_type = a }

(** val vdef :
    name -> TemplateTerm.term -> TemplateTerm.term -> context_decl **)

let vdef x t0 a =
  { decl_name = x; decl_body = (Some t0); decl_type = a }

type context = context_decl list

(** val map_decl :
    (TemplateTerm.term -> TemplateTerm.term) -> context_decl -> context_decl **)

let map_decl f d =
  { decl_name = (decl_name d); decl_body = (option_map f (decl_body d));
    decl_type = (f (decl_type d)) }

(** val map_context :
    (TemplateTerm.term -> TemplateTerm.term) -> context_decl list ->
    context_decl list **)

let map_context f c =
  map (map_decl f) c

type one_inductive_body = TemplateEnvironment.one_inductive_body = { 
ind_name : ident; ind_type : TemplateTerm.term; ind_kelim : sort_family;
ind_ctors : ((ident * TemplateTerm.term) * nat) list;
ind_projs : (ident * TemplateTerm.term) list }

(** val ind_name : one_inductive_body -> ident **)

let ind_name o =
  o.ind_name

(** val ind_type : one_inductive_body -> TemplateTerm.term **)

let ind_type o =
  o.ind_type

(** val ind_kelim : one_inductive_body -> sort_family **)

let ind_kelim o =
  o.ind_kelim

(** val ind_ctors :
    one_inductive_body -> ((ident * TemplateTerm.term) * nat) list **)

let ind_ctors o =
  o.ind_ctors

(** val ind_projs : one_inductive_body -> (ident * TemplateTerm.term) list **)

let ind_projs o =
  o.ind_projs

type mutual_inductive_body = TemplateEnvironment.mutual_inductive_body = { 
ind_finite : recursivity_kind; ind_npars : nat; ind_params : context;
ind_bodies : one_inductive_body list; ind_universes : universes_decl;
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

type constant_body = TemplateEnvironment.constant_body = { cst_type : 
                                                           TemplateTerm.term;
                                                           cst_body : 
                                                           TemplateTerm.term
                                                           option;
                                                           cst_universes : 
                                                           universes_decl }

(** val cst_type : constant_body -> TemplateTerm.term **)

let cst_type c =
  c.cst_type

(** val cst_body : constant_body -> TemplateTerm.term option **)

let cst_body c =
  c.cst_body

(** val cst_universes : constant_body -> universes_decl **)

let cst_universes c =
  c.cst_universes

type global_decl = TemplateEnvironment.global_decl =
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

type program = global_env * TemplateTerm.term
