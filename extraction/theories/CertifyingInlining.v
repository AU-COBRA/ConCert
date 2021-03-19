From Coq Require Import List String Bool Basics.

From ConCert.Extraction Require Import CertifyingEta.
From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Utils.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Section inlining.
  Context (should_inline : kername -> bool).
  Context (Σ : global_env).

  Fixpoint contains_const (t : term) : bool :=
    match t with
    | tRel n => false
    | tVar id => false
    | tEvar ev args => existsb contains_const args
    | tSort s => false
    | tCast t kind v => contains_const t
                       || contains_const v
    | tProd na ty body => contains_const ty
                         || contains_const body
    | tLambda na ty body => contains_const ty
                           || contains_const body
    | tLetIn na def def_ty body => contains_const def_ty
                                  || contains_const body
    | tApp f args => contains_const f
                    || existsb contains_const args
    | tConst c u => should_inline c
    | tInd ind u => false
    | tConstruct ind idx u => false
    | tCase ind_nbparams_relevance type_info discr branches =>
      contains_const type_info
      || contains_const discr
      || existsb (contains_const ∘ snd) branches
    | tProj proj t0 => contains_const t0
    | tFix mfix idx =>
      existsb id (map (fun d => contains_const d.(dtype) ||
                             contains_const d.(dbody)) mfix)
    | tCoFix mfix idx =>
      existsb id (map (fun d => contains_const d.(dtype) ||
                             contains_const d.(dbody)) mfix)
    | tInt i => false
    | tFloat f => false
  end.

  Fixpoint beta_body (body : term) (args : list term) {struct args} : term :=
    match args with
    | [] => body
    | a :: args =>
      match body with
      | tLambda na _ body => beta_body (body{0 := a}) args
      | _ => mkApps body (a :: args)
      end
    end.

  Definition iota_body (body : term) : term :=
    match body with
    | tCase (ind, pars, _) _ discr brs =>
      let (hd, args) := decompose_app discr in
      match hd with
      | tConstruct _ c _ =>
        match nth_error brs c with
        | Some (_, br) => beta_body br (skipn pars args)
        | None => body
        end
      | _ => body
      end
    | t => t
    end.

  Definition inline_const (kn : kername) (u : Instance.t) (args : list term) : term :=
    let const := tConst kn u in
    match lookup_env Σ kn with
    | Some (ConstantDecl cst) =>
      match cst_body cst with
      | Some body (* once told me *) =>
        (* Often the first beta will expose an iota (record projection),
               and the projected field is often a function, so we do another beta *)
              let (hd, args) := decompose_app (beta_body body args) in
              beta_body (iota_body hd) args
      | None => tApp const args
      end
    | _ => tApp const args
    end.

  Fixpoint inline (t : term) : term :=
    match t with
    | tRel n => t
    | tVar id => t
    | tEvar ev args =>
      tEvar ev (map inline args)
    | tSort s => t
    | tCast t kind v => tCast (inline t) kind (inline v)
    | tProd na ty body => tProd na (inline ty) (inline body)
    | tLambda na ty body => tLambda na ty (inline body)
    | tLetIn na def def_ty body => tLetIn na (inline def) (inline def_ty) (inline body)

    | tApp hd args =>
      let args := map inline args in
      match hd with
      | tConst kn u =>
        if should_inline kn then
           inline_const kn u args
        else tApp hd args
      | _ => tApp hd args
      end
    | tConst kn u =>
      if should_inline kn then
        inline_const kn u []
      else t
    | tInd _ _ => t
    | tConstruct ind idx u => t
    | tCase ind_info type_info discr branches =>
      tCase ind_info (inline type_info) (inline discr)
            (map (on_snd inline) branches)
    | tProj _ t0 => inline t0
    | tFix mfix idx =>
      let mfix' := map (map_def inline inline) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map (map_def inline inline) mfix in
      tCoFix mfix' idx
    | tInt _ => t
    | tFloat _ => t
    end.

  Definition inline_in_constant_body cst :=
    {| cst_type := cst_type cst;
       cst_universes := cst_universes cst;
       cst_body := option_map inline (cst_body cst) |}.

  Definition inline_in_decl d :=
    match d with
    | ConstantDecl cst => ConstantDecl (inline_in_constant_body cst)
    | _ => d
    end.

  Definition inline_in_env : global_env:=
  let newΣ :=
      fold_right (fun '(kn, decl) Σ => (kn, inline_in_decl decl) :: Σ) [] Σ in
  filter (fun '(kn, _) => negb (should_inline kn)) newΣ.

  Definition affected_by_inlining (kn : kername) : bool:=
    match lookup_env Σ kn with
    | Some (ConstantDecl cst) =>
      match cst_body cst with
      | Some body => contains_const body
      | _ => false
      end
    | _ => false
    end.

End inlining.


Definition inline_global_env_template
           (mpath : modpath)
           (Σ : global_env)
           (should_inline : kername -> bool)
  : TemplateMonad global_env :=
  let suffix := "_after_inlining" in
  Σinlined <- tmEval lazy (inline_in_env should_inline Σ);;
  gen_defs_and_proofs Σinlined mpath suffix
                      (fun kn => should_inline kn
                              || negb (affected_by_inlining should_inline Σ kn));;
  ret Σinlined.

(* Mainly for testing purposes *)
Definition inline_def {A} (mpath : modpath)
           (should_inline : kername -> bool)
           (def : A) : TemplateMonad _ :=
  p <- tmQuoteRecTransp def false ;;
  kn <- Common.extract_def_name def ;;
  inline_global_env_template mpath p.1 should_inline.


Definition template_inline (should_inline : kername -> bool): TemplateTransform :=
  fun Σ => Ok (timed "Inlining" (fun _ => inline_in_env should_inline Σ)).

Module Tests.

  (* Inlining into the local *)
  Module Ex1.
    Definition foo : nat -> nat := fun x => x + 1.
    Definition bar : nat -> nat := fun x => foo (x * 2).

    Definition baz : nat -> nat := fun x => foo x + bar x.

    MetaCoq Run (env <- inline_def <%% baz %%>.1
                          (fun kn => eq_kername <%% foo %%> kn)
                          baz;;
                 t <- tmEval lazy (map (Basics.compose snd fst) env);;
                 tmPrint t).
  End Ex1.

  (* Inlining into the definition from the standard library *)
  Module Ex2.
    Definition anchor := 0.

    MetaCoq Run (inline_def <%% anchor %%>.1
                          (fun kn => eq_kername <%% Nat.add %%> kn )
                          mult).
  End Ex2.
End Tests.
