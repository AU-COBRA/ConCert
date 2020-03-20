open Ast0
open BasicAst
open Datatypes
open List0
open MCProd
open PCUICAst
open Universes0

(** val trans : Ast0.term -> term **)

let rec trans = function
| Ast0.Coq_tRel n -> Coq_tRel n
| Ast0.Coq_tVar n -> Coq_tVar n
| Ast0.Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map trans args))
| Ast0.Coq_tSort u -> Coq_tSort u
| Coq_tCast (c, _, t0) ->
  Coq_tApp ((Coq_tLambda (Coq_nAnon, (trans t0), (Coq_tRel O))), (trans c))
| Ast0.Coq_tProd (na, a, b) -> Coq_tProd (na, (trans a), (trans b))
| Ast0.Coq_tLambda (na, t0, m) -> Coq_tLambda (na, (trans t0), (trans m))
| Ast0.Coq_tLetIn (na, b, t0, b') ->
  Coq_tLetIn (na, (trans b), (trans t0), (trans b'))
| Ast0.Coq_tApp (u, v) -> mkApps (trans u) (map trans v)
| Ast0.Coq_tConst (c, u) -> Coq_tConst (c, u)
| Ast0.Coq_tInd (c, u) -> Coq_tInd (c, u)
| Ast0.Coq_tConstruct (c, k, u) -> Coq_tConstruct (c, k, u)
| Ast0.Coq_tCase (ind, p, c, brs) ->
  let brs' = map (on_snd trans) brs in
  Coq_tCase (ind, (trans p), (trans c), brs')
| Ast0.Coq_tProj (p, c) -> Coq_tProj (p, (trans c))
| Ast0.Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def trans trans) mfix in Coq_tFix (mfix', idx)
| Ast0.Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def trans trans) mfix in Coq_tCoFix (mfix', idx)

(** val trans_decl : Ast0.context_decl -> context_decl **)

let trans_decl d =
  let { Ast0.decl_name = na; Ast0.decl_body = b; Ast0.decl_type = t } = d in
  { decl_name = na; decl_body = (option_map trans b); decl_type = (trans t) }

(** val trans_local : Ast0.context_decl list -> context_decl list **)

let trans_local _UU0393_ =
  map trans_decl _UU0393_

(** val trans_one_ind_body : Ast0.one_inductive_body -> one_inductive_body **)

let trans_one_ind_body d =
  { ind_name = (Ast0.ind_name d); ind_type = (trans (Ast0.ind_type d));
    ind_kelim = (Ast0.ind_kelim d); ind_ctors =
    (map (fun pat ->
      let (y0, z) = pat in let (x, y) = y0 in ((x, (trans y)), z))
      (Ast0.ind_ctors d)); ind_projs =
    (map (fun pat -> let (x, y) = pat in (x, (trans y))) (Ast0.ind_projs d)) }

(** val trans_constant_body : Ast0.constant_body -> constant_body **)

let trans_constant_body bd =
  { cst_type = (trans (Ast0.cst_type bd)); cst_body =
    (option_map trans (Ast0.cst_body bd)); cst_universes =
    (Ast0.cst_universes bd) }

(** val trans_minductive_body :
    Ast0.mutual_inductive_body -> mutual_inductive_body **)

let trans_minductive_body md =
  { ind_finite = (Ast0.ind_finite md); ind_npars = (Ast0.ind_npars md);
    ind_params = (trans_local (Ast0.ind_params md)); ind_bodies =
    (map trans_one_ind_body (Ast0.ind_bodies md)); ind_universes =
    (Ast0.ind_universes md); ind_variance = (Ast0.ind_variance md) }

(** val trans_global_decl : Ast0.global_decl -> global_decl **)

let trans_global_decl = function
| Ast0.ConstantDecl bd -> ConstantDecl (trans_constant_body bd)
| Ast0.InductiveDecl bd -> InductiveDecl (trans_minductive_body bd)

(** val trans_global_decls :
    Ast0.global_env -> (kername * global_decl) list **)

let trans_global_decls d =
  map (on_snd trans_global_decl) d

(** val trans_global :
    Ast0.global_env_ext -> (kername * global_decl) list * universes_decl **)

let trans_global _UU03a3_ =
  ((trans_global_decls (fst _UU03a3_)), (snd _UU03a3_))
