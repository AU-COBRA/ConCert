open Ast0
open Universes0

(** val on_udecl_decl :
    (universes_decl -> 'a1) -> TemplateEnvironment.global_decl -> 'a1 **)

let on_udecl_decl f = function
| TemplateEnvironment.ConstantDecl cb ->
  f (TemplateEnvironment.cst_universes cb)
| TemplateEnvironment.InductiveDecl mb ->
  f (TemplateEnvironment.ind_universes mb)

(** val monomorphic_udecl_decl :
    TemplateEnvironment.global_decl -> ContextSet.t **)

let monomorphic_udecl_decl =
  on_udecl_decl monomorphic_udecl
