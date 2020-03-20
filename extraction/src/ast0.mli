open BasicAst
open Datatypes
open List0
open Universes0

module Coq__1 : sig
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
include module type of struct include Coq__1 end

val mkApps : term -> term list -> term

module TemplateTerm :
 sig
  type term = Coq__1.term

  val tRel : nat -> Coq__1.term

  val tSort : Universe.t -> Coq__1.term

  val tProd : name -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tLambda : name -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tLetIn :
    name -> Coq__1.term -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tInd : inductive -> Instance.t -> Coq__1.term

  val mkApps : Coq__1.term -> Coq__1.term list -> Coq__1.term
 end

module TemplateEnvironment :
 sig
  type context_decl = { decl_name : name;
                        decl_body : TemplateTerm.term option;
                        decl_type : TemplateTerm.term }

  val decl_name : context_decl -> name

  val decl_body : context_decl -> TemplateTerm.term option

  val decl_type : context_decl -> TemplateTerm.term

  val vass : name -> TemplateTerm.term -> context_decl

  val vdef : name -> TemplateTerm.term -> TemplateTerm.term -> context_decl

  type context = context_decl list

  val snoc : 'a1 list -> 'a1 -> 'a1 list

  val map_decl :
    (TemplateTerm.term -> TemplateTerm.term) -> context_decl -> context_decl

  val map_context :
    (TemplateTerm.term -> TemplateTerm.term) -> context_decl list ->
    context_decl list

  val fold_context :
    (nat -> TemplateTerm.term -> TemplateTerm.term) -> context -> context

  type one_inductive_body = { ind_name : ident; ind_type : TemplateTerm.term;
                              ind_kelim : sort_family;
                              ind_ctors : ((ident * TemplateTerm.term) * nat)
                                          list;
                              ind_projs : (ident * TemplateTerm.term) list }

  val ind_name : one_inductive_body -> ident

  val ind_type : one_inductive_body -> TemplateTerm.term

  val ind_kelim : one_inductive_body -> sort_family

  val ind_ctors :
    one_inductive_body -> ((ident * TemplateTerm.term) * nat) list

  val ind_projs : one_inductive_body -> (ident * TemplateTerm.term) list

  val map_one_inductive_body :
    nat -> nat -> (nat -> TemplateTerm.term -> TemplateTerm.term) -> nat ->
    one_inductive_body -> one_inductive_body

  type mutual_inductive_body = { ind_finite : recursivity_kind;
                                 ind_npars : nat; ind_params : context;
                                 ind_bodies : one_inductive_body list;
                                 ind_universes : universes_decl;
                                 ind_variance : Variance.t list option }

  val ind_finite : mutual_inductive_body -> recursivity_kind

  val ind_npars : mutual_inductive_body -> nat

  val ind_params : mutual_inductive_body -> context

  val ind_bodies : mutual_inductive_body -> one_inductive_body list

  val ind_universes : mutual_inductive_body -> universes_decl

  val ind_variance : mutual_inductive_body -> Variance.t list option

  type constant_body = { cst_type : TemplateTerm.term;
                         cst_body : TemplateTerm.term option;
                         cst_universes : universes_decl }

  val cst_type : constant_body -> TemplateTerm.term

  val cst_body : constant_body -> TemplateTerm.term option

  val cst_universes : constant_body -> universes_decl

  val map_constant_body :
    (TemplateTerm.term -> TemplateTerm.term) -> constant_body -> constant_body

  type global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body

  val global_decl_rect :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val global_decl_rec :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  type global_env = (kername * global_decl) list

  type global_env_ext = global_env * universes_decl

  val fst_ctx : global_env_ext -> global_env

  val empty_ext : global_env -> global_env_ext

  type program = global_env * TemplateTerm.term

  val app_context : context -> context -> context

  val mkLambda_or_LetIn :
    context_decl -> TemplateTerm.term -> TemplateTerm.term

  val it_mkLambda_or_LetIn : context -> TemplateTerm.term -> TemplateTerm.term

  val mkProd_or_LetIn : context_decl -> TemplateTerm.term -> TemplateTerm.term

  val it_mkProd_or_LetIn : context -> TemplateTerm.term -> TemplateTerm.term

  val reln :
    TemplateTerm.term list -> nat -> context_decl list -> TemplateTerm.term
    list

  val to_extended_list_k : context_decl list -> nat -> TemplateTerm.term list

  val to_extended_list : context_decl list -> TemplateTerm.term list

  val reln_alt : nat -> context_decl list -> TemplateTerm.term list

  val arities_context : one_inductive_body list -> context_decl list

  val context_assumptions : context -> nat

  val map_mutual_inductive_body :
    (nat -> TemplateTerm.term -> TemplateTerm.term) -> mutual_inductive_body
    -> mutual_inductive_body

  val lookup_mind_decl : ident -> global_env -> mutual_inductive_body option
 end

type context_decl = TemplateEnvironment.context_decl = { decl_name : 
                                                         name;
                                                         decl_body : 
                                                         TemplateTerm.term
                                                         option;
                                                         decl_type : 
                                                         TemplateTerm.term }

val decl_name : context_decl -> name

val decl_body : context_decl -> TemplateTerm.term option

val decl_type : context_decl -> TemplateTerm.term

val vass : name -> TemplateTerm.term -> context_decl

val vdef : name -> TemplateTerm.term -> TemplateTerm.term -> context_decl

type context = context_decl list

val map_decl :
  (TemplateTerm.term -> TemplateTerm.term) -> context_decl -> context_decl

val map_context :
  (TemplateTerm.term -> TemplateTerm.term) -> context_decl list ->
  context_decl list

type one_inductive_body = TemplateEnvironment.one_inductive_body = { 
ind_name : ident; ind_type : TemplateTerm.term; ind_kelim : sort_family;
ind_ctors : ((ident * TemplateTerm.term) * nat) list;
ind_projs : (ident * TemplateTerm.term) list }

val ind_name : one_inductive_body -> ident

val ind_type : one_inductive_body -> TemplateTerm.term

val ind_kelim : one_inductive_body -> sort_family

val ind_ctors : one_inductive_body -> ((ident * TemplateTerm.term) * nat) list

val ind_projs : one_inductive_body -> (ident * TemplateTerm.term) list

type mutual_inductive_body = TemplateEnvironment.mutual_inductive_body = { 
ind_finite : recursivity_kind; ind_npars : nat; ind_params : context;
ind_bodies : one_inductive_body list; ind_universes : universes_decl;
ind_variance : Variance.t list option }

val ind_finite : mutual_inductive_body -> recursivity_kind

val ind_npars : mutual_inductive_body -> nat

val ind_params : mutual_inductive_body -> context

val ind_bodies : mutual_inductive_body -> one_inductive_body list

val ind_universes : mutual_inductive_body -> universes_decl

val ind_variance : mutual_inductive_body -> Variance.t list option

type constant_body = TemplateEnvironment.constant_body = { cst_type : 
                                                           TemplateTerm.term;
                                                           cst_body : 
                                                           TemplateTerm.term
                                                           option;
                                                           cst_universes : 
                                                           universes_decl }

val cst_type : constant_body -> TemplateTerm.term

val cst_body : constant_body -> TemplateTerm.term option

val cst_universes : constant_body -> universes_decl

type global_decl = TemplateEnvironment.global_decl =
| ConstantDecl of constant_body
| InductiveDecl of mutual_inductive_body

type global_env = (kername * global_decl) list

type global_env_ext = global_env * universes_decl

val fst_ctx : global_env_ext -> global_env

val empty_ext : global_env -> global_env_ext

type program = global_env * TemplateTerm.term
