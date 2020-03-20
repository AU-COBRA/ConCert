open Ast0
open Universes0

val on_udecl_decl :
  (universes_decl -> 'a1) -> TemplateEnvironment.global_decl -> 'a1

val monomorphic_udecl_decl : TemplateEnvironment.global_decl -> ContextSet.t
