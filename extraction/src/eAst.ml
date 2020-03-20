open BasicAst
open Datatypes
open List0
open Universes0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'term def = { dname : name; dbody : 'term; rarg : nat }

(** val dname : 'a1 def -> name **)

let dname d =
  d.dname

(** val dbody : 'a1 def -> 'a1 **)

let dbody d =
  d.dbody

(** val rarg : 'a1 def -> nat **)

let rarg d =
  d.rarg

(** val map_def : ('a1 -> 'a1) -> 'a1 def -> 'a1 def **)

let map_def f d =
  { dname = d.dname; dbody = (f d.dbody); rarg = d.rarg }

(** val test_def : ('a1 -> bool) -> 'a1 def -> bool **)

let test_def f d =
  f d.dbody

type 'term mfixpoint = 'term def list

type aname = { binder_name : name; binder_dummy : bool }

(** val binder_name : aname -> name **)

let binder_name a =
  a.binder_name

(** val binder_dummy : aname -> bool **)

let binder_dummy a =
  a.binder_dummy

(** val aname_to_name : aname -> name **)

let aname_to_name a =
  a.binder_name

type term =
| Coq_tBox
| Coq_tRel of nat
| Coq_tVar of ident
| Coq_tEvar of nat * term list
| Coq_tLambda of aname * term
| Coq_tLetIn of aname * term * term
| Coq_tApp of term * term
| Coq_tConst of kername
| Coq_tConstruct of inductive * nat
| Coq_tCase of (inductive * nat) * term * (nat * term) list
| Coq_tProj of projection * term
| Coq_tFix of term mfixpoint * nat
| Coq_tCoFix of term mfixpoint * nat

(** val term_rect :
    'a1 -> (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) ->
    (aname -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 ->
    'a1) -> (term -> 'a1 -> term -> 'a1 -> 'a1) -> (kername -> 'a1) ->
    (inductive -> nat -> 'a1) -> ((inductive * nat) -> term -> 'a1 ->
    (nat * term) list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) -> (term
    mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> term -> 'a1 **)

let rec term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
| Coq_tBox -> f
| Coq_tRel n -> f0 n
| Coq_tVar i -> f1 i
| Coq_tEvar (n, l) -> f2 n l
| Coq_tLambda (a, t0) ->
  f3 a t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0)
| Coq_tLetIn (a, t0, t1) ->
  f4 a t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0) t1
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t1)
| Coq_tApp (t0, t1) ->
  f5 t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0) t1
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t1)
| Coq_tConst k -> f6 k
| Coq_tConstruct (i, n) -> f7 i n
| Coq_tCase (p, t0, l) ->
  f8 p t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0) l
| Coq_tProj (p, t0) ->
  f9 p t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0)
| Coq_tFix (m, n) -> f10 m n
| Coq_tCoFix (m, n) -> f11 m n

(** val term_rec :
    'a1 -> (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) ->
    (aname -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 ->
    'a1) -> (term -> 'a1 -> term -> 'a1 -> 'a1) -> (kername -> 'a1) ->
    (inductive -> nat -> 'a1) -> ((inductive * nat) -> term -> 'a1 ->
    (nat * term) list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) -> (term
    mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> term -> 'a1 **)

let rec term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
| Coq_tBox -> f
| Coq_tRel n -> f0 n
| Coq_tVar i -> f1 i
| Coq_tEvar (n, l) -> f2 n l
| Coq_tLambda (a, t0) ->
  f3 a t0 (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0)
| Coq_tLetIn (a, t0, t1) ->
  f4 a t0 (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0) t1
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t1)
| Coq_tApp (t0, t1) ->
  f5 t0 (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0) t1
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t1)
| Coq_tConst k -> f6 k
| Coq_tConstruct (i, n) -> f7 i n
| Coq_tCase (p, t0, l) ->
  f8 p t0 (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0) l
| Coq_tProj (p, t0) ->
  f9 p t0 (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 t0)
| Coq_tFix (m, n) -> f10 m n
| Coq_tCoFix (m, n) -> f11 m n

(** val mkApps : term -> term list -> term **)

let rec mkApps t = function
| [] -> t
| a :: args -> mkApps (Coq_tApp (t, a)) args

(** val mkApp : term -> term -> term **)

let mkApp t u =
  Coq_tApp (t, u)

(** val isApp : term -> bool **)

let isApp = function
| Coq_tApp (_, _) -> true
| _ -> false

(** val isLambda : term -> bool **)

let isLambda = function
| Coq_tLambda (_, _) -> true
| _ -> false

type definition_entry = { definition_entry_body : term;
                          definition_entry_opaque : bool }

(** val definition_entry_body : definition_entry -> term **)

let definition_entry_body d =
  d.definition_entry_body

(** val definition_entry_opaque : definition_entry -> bool **)

let definition_entry_opaque d =
  d.definition_entry_opaque

type constant_entry =
| ParameterEntry
| DefinitionEntry of definition_entry

(** val constant_entry_rect :
    (__ -> 'a1) -> (definition_entry -> 'a1) -> constant_entry -> 'a1 **)

let constant_entry_rect f f0 = function
| ParameterEntry -> f __
| DefinitionEntry x -> f0 x

(** val constant_entry_rec :
    (__ -> 'a1) -> (definition_entry -> 'a1) -> constant_entry -> 'a1 **)

let constant_entry_rec f f0 = function
| ParameterEntry -> f __
| DefinitionEntry x -> f0 x

type recursivity_kind =
| Finite
| CoFinite
| BiFinite

(** val recursivity_kind_rect :
    'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1 **)

let recursivity_kind_rect f f0 f1 = function
| Finite -> f
| CoFinite -> f0
| BiFinite -> f1

(** val recursivity_kind_rec :
    'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1 **)

let recursivity_kind_rec f f0 f1 = function
| Finite -> f
| CoFinite -> f0
| BiFinite -> f1

type local_entry =
| LocalDef of term
| LocalAssum of term

(** val local_entry_rect :
    (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1 **)

let local_entry_rect f f0 = function
| LocalDef x -> f x
| LocalAssum x -> f0 x

(** val local_entry_rec :
    (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1 **)

let local_entry_rec f f0 = function
| LocalDef x -> f x
| LocalAssum x -> f0 x

type one_inductive_entry = { mind_entry_typename : ident;
                             mind_entry_arity : term;
                             mind_entry_template : bool;
                             mind_entry_consnames : ident list;
                             mind_entry_lc : term list }

(** val mind_entry_typename : one_inductive_entry -> ident **)

let mind_entry_typename o =
  o.mind_entry_typename

(** val mind_entry_arity : one_inductive_entry -> term **)

let mind_entry_arity o =
  o.mind_entry_arity

(** val mind_entry_template : one_inductive_entry -> bool **)

let mind_entry_template o =
  o.mind_entry_template

(** val mind_entry_consnames : one_inductive_entry -> ident list **)

let mind_entry_consnames o =
  o.mind_entry_consnames

(** val mind_entry_lc : one_inductive_entry -> term list **)

let mind_entry_lc o =
  o.mind_entry_lc

type mutual_inductive_entry = { mind_entry_record : ident option option;
                                mind_entry_finite : recursivity_kind;
                                mind_entry_params : (ident * local_entry) list;
                                mind_entry_inds : one_inductive_entry list;
                                mind_entry_private : bool option }

(** val mind_entry_record : mutual_inductive_entry -> ident option option **)

let mind_entry_record m =
  m.mind_entry_record

(** val mind_entry_finite : mutual_inductive_entry -> recursivity_kind **)

let mind_entry_finite m =
  m.mind_entry_finite

(** val mind_entry_params :
    mutual_inductive_entry -> (ident * local_entry) list **)

let mind_entry_params m =
  m.mind_entry_params

(** val mind_entry_inds :
    mutual_inductive_entry -> one_inductive_entry list **)

let mind_entry_inds m =
  m.mind_entry_inds

(** val mind_entry_private : mutual_inductive_entry -> bool option **)

let mind_entry_private m =
  m.mind_entry_private

type context_decl = { decl_name : name; decl_body : term option }

(** val decl_name : context_decl -> name **)

let decl_name c =
  c.decl_name

(** val decl_body : context_decl -> term option **)

let decl_body c =
  c.decl_body

(** val vass : name -> context_decl **)

let vass x =
  { decl_name = x; decl_body = None }

(** val vdef : name -> term -> context_decl **)

let vdef x t =
  { decl_name = x; decl_body = (Some t) }

type context = context_decl list

(** val map_decl : (term -> term) -> context_decl -> context_decl **)

let map_decl f d =
  { decl_name = d.decl_name; decl_body = (option_map f d.decl_body) }

(** val map_context :
    (term -> term) -> context_decl list -> context_decl list **)

let map_context f c =
  map (map_decl f) c

(** val snoc : 'a1 list -> 'a1 -> 'a1 list **)

let snoc _UU0393_ d =
  d :: _UU0393_

type one_inductive_body = { ind_name : ident; ind_kelim : sort_family;
                            ind_ctors : ((ident * term) * nat) list;
                            ind_projs : (ident * term) list }

(** val ind_name : one_inductive_body -> ident **)

let ind_name o =
  o.ind_name

(** val ind_kelim : one_inductive_body -> sort_family **)

let ind_kelim o =
  o.ind_kelim

(** val ind_ctors : one_inductive_body -> ((ident * term) * nat) list **)

let ind_ctors o =
  o.ind_ctors

(** val ind_projs : one_inductive_body -> (ident * term) list **)

let ind_projs o =
  o.ind_projs

type mutual_inductive_body = { ind_npars : nat;
                               ind_bodies : one_inductive_body list }

(** val ind_npars : mutual_inductive_body -> nat **)

let ind_npars m =
  m.ind_npars

(** val ind_bodies : mutual_inductive_body -> one_inductive_body list **)

let ind_bodies m =
  m.ind_bodies

type constant_body =
  term option
  (* singleton inductive, whose constructor was Build_constant_body *)

(** val cst_body : constant_body -> term option **)

let cst_body c =
  c

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

type global_declarations = (kername * global_decl) list

type global_context = global_declarations

type program = global_declarations * term
