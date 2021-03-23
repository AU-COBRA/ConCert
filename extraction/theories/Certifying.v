From Coq Require Import List PeanoNat Bool Ascii String.
From MetaCoq.Template Require Import Kernames All Ast.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require StringExtra.


Open Scope string.

Import ListNotations.
Import MonadNotation.

Definition get_def_name (name : kername) : string :=
  StringExtra.replace_char "." "_" (string_of_kername name).

Definition change_modpath (mpath : modpath) (suffix : string) (expansion_ignore : kername -> bool)
  : term -> term :=
  fix go (t : term) : term :=
    match t with
    | tRel n => t
    | tVar id => t
    | tSort s => t
    | tEvar ev args => tEvar ev (map (go) args)
    | tCast t kind v => tCast (go t) kind (go v)
    | tProd na ty body => tProd na (go ty) (go body)
    | tLambda na ty body => tLambda na (go ty) (go body)
    | tLetIn na def def_ty body =>
      tLetIn na (go def) (go def_ty) (go body)
    | tApp f args => tApp (go f) (map (go) args)
    | tConst kn u => if expansion_ignore kn then t
                    else tConst (mpath, get_def_name kn ++ suffix) u
    | tInd ind u => t
    | tConstruct ind idx u => t
    | tCase ind_and_nbparams type_info discr branches =>
      tCase ind_and_nbparams (go type_info)
            (go discr) (map (on_snd (go)) branches)
    | tProj proj t => tProj proj (go t)
    | tFix mfix idx => tFix (map (map_def (go) (go)) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def (go) (go)) mfix) idx
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
    (fun cb => {| cst_type := cb.(cst_type);
               cst_body := b <- cb.(cst_body);;
                           Some (change_modpath mpath suffix expansion_ignore b);
               cst_universes := cb.(cst_universes) |}) Σ.


Definition generate_proof (Σ1 Σ2 : global_env) (kn1 kn2 : kername) : TemplateMonad (term × term × term × term) :=
  match lookup_env Σ1 kn1, lookup_env Σ2 kn2  with
  | Some (ConstantDecl cb1), Some (ConstantDecl cb2) =>
    match cb1.(cst_body), cb2.(cst_body) with
    | Some _, Some exp_body =>
      let ty := cb1.(cst_type) in
      let proof_ty :=
          tApp (tInd
                  {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq");
                     inductive_ind := 0 |} [])
               [ty; tConst kn1 []; tConst kn2 []] in
      let proof_body := tApp (tConstruct
                          {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq");
                             inductive_ind := 0 |} 0 [])
                       [ty;tConst kn1 []] in
      ret (cb1.(cst_type), (exp_body, (proof_ty, proof_body)))
    | _,_ => tmFail "No body"
    end
  | None, _ => tmFail ("Not found: " ++ kn1.2)
  | _, None => tmFail ("Not found: " ++ kn2.2)
  | _,_ => tmFail "Not a constant"
  end.

Definition gen_proof_prog (Σ1 Σ2 : global_env) (kn1 kn2 : kername) : TemplateMonad unit :=
  '(exp_ty, (exp_t, (p_ty, p_t))) <- generate_proof Σ1 Σ2 kn1 kn2 ;;
  tmBind (tmUnquoteTyped Type exp_ty)
         (fun A => ucst <- tmUnquoteTyped A exp_t ;;
                 tmDefinition kn2.2 ucst;;
            tmBind (tmUnquoteTyped Type p_ty)
                   (fun B =>
                      uproof <- tmUnquoteTyped B p_t ;;
                      tmDefinition (kn2.2 ++ "_correct") uproof ;;
                      tmPrint B)).

Definition is_none {A} (o : option A) :=
  match o with
  | Some _ => false
  | None => true
  end.

Definition gen_defs_and_proofs (Σ : global_env) (mpath : modpath) (suffix: string) (ignore : kername -> bool)  : TemplateMonad unit :=
  let Σdecls := filter (fun '(kn,gd) => match gd with
                                    | ConstantDecl cb => negb (is_none cb.(cst_body))
                                    | _ => false
                                     end) Σ in
  Σdecls' <- tmEval lazy (add_suffix_global_env mpath suffix ignore Σdecls) ;;
  monad_iter (fun kn1 =>
                if ignore kn1 then ret tt
                else
                  gen_proof_prog Σ Σdecls' kn1 (mpath, get_def_name kn1 ++ suffix))
             (List.rev (map fst Σdecls)).
