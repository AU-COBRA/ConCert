open Ast0
open BasicAst
open Datatypes
open List0
open MCProd
open PCUICAst
open Universes0

val trans : Ast0.term -> term

val trans_decl : Ast0.context_decl -> context_decl

val trans_local : Ast0.context_decl list -> context_decl list

val trans_one_ind_body : Ast0.one_inductive_body -> one_inductive_body

val trans_constant_body : Ast0.constant_body -> constant_body

val trans_minductive_body :
  Ast0.mutual_inductive_body -> mutual_inductive_body

val trans_global_decl : Ast0.global_decl -> global_decl

val trans_global_decls : Ast0.global_env -> (kername * global_decl) list

val trans_global :
  Ast0.global_env_ext -> (kername * global_decl) list * universes_decl
