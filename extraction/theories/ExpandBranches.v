From Coq Require Import Arith.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import Utils.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Template Require Import utils.

Fixpoint expand_branch (ar : nat) (body : term) : term :=
  match ar with
  | 0 => body
  | S ar =>
    match body with
    | tLambda na body => tLambda na (expand_branch ar body)
    | _ => tLambda nAnon (expand_branch ar (tApp (lift0 1 body) (tRel 0)))
    end
  end.

Fixpoint expand_branches (t : term) : term :=
  match t with
  | tBox => t
  | tRel _ => t
  | tVar _ => t
  | tEvar n ts => tEvar n (map expand_branches ts)
  | tLambda na body => tLambda na (expand_branches body)
  | tLetIn na val body => tLetIn na (expand_branches val) (expand_branches body)
  | tApp hd arg => tApp (expand_branches hd) (expand_branches arg)
  | tConst _ => t
  | tConstruct _ _ => t
  | tCase p discr brs =>
    let on_branch '(ar, t) := (ar, expand_branch ar (expand_branches t)) in
    tCase p (expand_branches discr) (map on_branch brs)
  | tProj p t => tProj p (expand_branches t)
  | tFix defs i => tFix (map (map_def expand_branches) defs) i
  | tCoFix defs i => tCoFix (map (map_def expand_branches) defs) i
  | tPrim _ => t
  end.

Definition expand_constant_body cst :=
  {| cst_type := cst_type cst;
     cst_body := option_map expand_branches (cst_body cst) |}.

Definition expand_decl d :=
  match d with
  | ConstantDecl cst => ConstantDecl (expand_constant_body cst)
  | _ => d
  end.

Definition expand_env (Σ : global_env) : global_env :=
  map (on_snd expand_decl) Σ.

Definition transform : ExtractTransform :=
  fun Σ => Ok (timed "Expansion of match branches" (fun _ => expand_env Σ)).
