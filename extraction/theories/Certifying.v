(** * Term and proof generation for the certifying transforms *)
From Coq Require Import List PeanoNat Bool Ascii String.
From MetaCoq.Template Require Import Kernames All Ast Reflect Checker.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require StringExtra.


Open Scope string.

Import ListNotations.
Import MonadNotation.

Definition get_def_name (name : kername) : string :=
  StringExtra.replace_char "." "_" (string_of_kername name).

Definition change_modpath (mpath : modpath) (suffix : string) (to_rename : kername -> bool)
  : term -> term :=
  fix go (t : term) : term :=
    match t with
    | tRel n => t
    | tVar id => t
    | tSort s => t
    | tEvar ev args => tEvar ev (map go args)
    | tCast t kind v => tCast (go t) kind (go v)
    | tProd na ty body => tProd na (go ty) (go body)
    | tLambda na ty body => tLambda na (go ty) (go body)
    | tLetIn na def def_ty body =>
      tLetIn na (go def) (go def_ty) (go body)
    | tApp f args => tApp (go f) (map go args)
    | tConst kn u => if to_rename kn then
                      tConst (mpath, get_def_name kn ++ suffix) u
                    else t
    | tInd ind u => t
    | tConstruct ind idx u => t
    | tCase ind_and_nbparams type_info discr branches =>
      tCase ind_and_nbparams (go type_info)
            (go discr) (map (on_snd go) branches)
    | tProj proj t => tProj proj (go t)
    | tFix mfix idx => tFix (map (map_def go go) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def go go) mfix) idx
    | tInt _ => t
    | tFloat _ => t
  end.

Fixpoint map_constants_global_env (k : kername -> kername) (f : constant_body -> constant_body) (Σ : global_env) : global_env :=
  match Σ with
  | [] => []
  | (kn, ConstantDecl cb) :: Σ' => (k kn, ConstantDecl (f cb)) :: map_constants_global_env k f Σ'
  | gd :: Σ' => gd :: map_constants_global_env k f Σ'
  end.

Definition add_suffix_global_env (mpath : modpath) (suffix : string) (expansion_ignore : kername -> bool) (Σ : global_env) :=
  map_constants_global_env
    (fun kn => (mpath,get_def_name kn ++ suffix))
    (fun cb => {| cst_type := change_modpath mpath suffix expansion_ignore cb.(cst_type);
               cst_body := b <- cb.(cst_body);;
                           Some (change_modpath mpath suffix expansion_ignore b);
               cst_universes := cb.(cst_universes) |}) Σ.

Definition generate_proof_term (ty: term) (kn1 kn2 : kername) : term × term :=
  let proof_ty :=
      tApp <% @eq %> [ty; tConst kn1 []; tConst kn2 []] in
  let proof_body :=
      tApp <% @eq_refl %> [ty; tConst kn2 []] in
      (proof_ty, proof_body).

Definition gen_prog (ty body : term) (kn : kername) : TemplateMonad unit
  := tmBind (tmUnquoteTyped Type ty)
            (fun A => ucst <- tmUnquoteTyped A body ;;
                   tmDefinition kn.2 ucst;;
                   ret tt).

Definition gen_proof (suffix : string) (Σ : global_env) (mpath : modpath) (kn : kername)  : TemplateMonad unit :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
    let kn_after := (mpath, get_def_name kn ++ suffix) in
    '(p_ty, p_t) <- tmEval lazy (generate_proof_term cb.(cst_type) kn kn_after) ;;
    tmBind (tmUnquoteTyped Type p_ty)
           (fun B =>
              uproof <- tmUnquoteTyped B p_t ;;
              tmDefinition (kn_after.2 ++ "_convertible") uproof ;;
              tmPrint B)
  | _ => tmFail ("Not a defined constant" ++ string_of_kername kn)
  end.

Definition is_none {A} (o : option A) :=
  match o with
  | Some _ => false
  | None => true
  end.

(** Given the two environments [Σ1] and [Σ2] we trverse the first and lookup constants with the same name in the second. If such a constant is found, we compare the codies for (syntactic) equality. If they are not equal, we expect them to be convertible, so we generate a new definition and save the name to [affected] list, which is returned when we traversed all definition in [Σ1]  *)
Definition traverse_env (mpath : modpath) (suffix: string) :=
  fix go (affected : KernameSet.t) (Σ1 Σ2 : global_env) : TemplateMonad KernameSet.t :=
    match Σ1 with
    | [] => ret affected
    | (kn, ConstantDecl cb1) :: Σtail =>
      match lookup_env Σ2 kn with
      | Some (ConstantDecl cb2) =>
        match cb1, cb2 with
        | Build_constant_body ty1 (Some body1) _,
          (Build_constant_body ty2 (Some body2) _) =>
          new_body2 <- tmEval lazy (change_modpath mpath suffix (fun kn => KernameSet.mem kn affected) body2);;
          new_ty2 <-tmEval lazy (change_modpath mpath suffix (fun kn => KernameSet.mem kn affected) ty2);;
          if @Checker.eq_term config.default_checker_flags init_graph body1 new_body2 then
            go affected Σtail Σ2
          else
            gen_prog new_ty2 new_body2 (mpath, get_def_name kn ++ suffix);;
            go (KernameSet.add kn affected) Σtail Σ2
        | _,_ => go affected Σtail Σ2
        end
      | Some _ | None => go affected Σtail Σ2
      end
    | _ :: Σtail => go affected Σtail Σ2
    end.

(** We generate new definitions using [traverse_env] and then generate the proofs for all affected seeds.
The proof is just [eq_refl], since we expect that the generated definitions are convertible to the originals.
At this point all the affected definitions have been added to the current scope given by [mpath] *)
Definition gen_defs_and_proofs (Σold Σnew : global_env) (mpath : modpath) (suffix: string) (seeds : KernameSet.t) : TemplateMonad unit :=
  let filter_decls Σ := filter (fun '(kn,gd) =>
                                  match gd with
                                  | ConstantDecl cb => negb (is_none cb.(cst_body))
                                  | _ => false
                                  end) Σ in
  affected_defs <- traverse_env mpath suffix KernameSet.empty (List.rev (filter_decls Σold)) (filter_decls Σnew);;
  let affected_seeds := KernameSet.inter affected_defs seeds in
  monad_iter (gen_proof suffix Σnew mpath) (KernameSet.elements affected_seeds).
