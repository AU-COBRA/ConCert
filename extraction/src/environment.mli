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

module Environment :
 functor (T:Term) ->
 sig
  type context_decl = { decl_name : name; decl_body : T.term option;
                        decl_type : T.term }

  val decl_name : context_decl -> name

  val decl_body : context_decl -> T.term option

  val decl_type : context_decl -> T.term

  val vass : name -> T.term -> context_decl

  val vdef : name -> T.term -> T.term -> context_decl

  type context = context_decl list

  val snoc : 'a1 list -> 'a1 -> 'a1 list

  val map_decl : (T.term -> T.term) -> context_decl -> context_decl

  val map_context :
    (T.term -> T.term) -> context_decl list -> context_decl list

  val fold_context : (nat -> T.term -> T.term) -> context -> context

  type one_inductive_body = { ind_name : ident; ind_type : T.term;
                              ind_kelim : sort_family;
                              ind_ctors : ((ident * T.term) * nat) list;
                              ind_projs : (ident * T.term) list }

  val ind_name : one_inductive_body -> ident

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> sort_family

  val ind_ctors : one_inductive_body -> ((ident * T.term) * nat) list

  val ind_projs : one_inductive_body -> (ident * T.term) list

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> nat -> one_inductive_body ->
    one_inductive_body

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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = global_env * T.term

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> context_decl list -> T.term list

  val to_extended_list_k : context_decl list -> nat -> T.term list

  val to_extended_list : context_decl list -> T.term list

  val reln_alt : nat -> context_decl list -> T.term list

  val arities_context : one_inductive_body list -> context_decl list

  val context_assumptions : context -> nat

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val lookup_mind_decl : ident -> global_env -> mutual_inductive_body option
 end
