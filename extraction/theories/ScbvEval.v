From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import WcbvEvalAux.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import Morphisms.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import RelationClasses.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import ETyping.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Import EAstUtils.

Section seval.
Context (Σ : global_declarations).
Inductive seval : term -> term -> Prop :=
| seval_box_app a t t' :
    eval a tBox ->
    eval t t' ->
    eval (tApp a t) tBox

| seval_beta f na b a a' res :
    eval f (tLambda na b) ->
    eval a a' ->
    eval (csubst a' 0 b) res ->
    eval (tApp f a) res

| seval_zeta na b0 b0' b1 res :
    eval b0 b0' ->
    eval (csubst b0' 0 b1) res ->
    eval (tLetIn na b0 b1) res

| seval_iota ind pars discr c args brs res :
    eval discr (mkApps (tConstruct ind c) args) ->
    eval (iota_red pars c args brs) res ->
    eval (tCase (ind, pars) discr brs) res

| seval_iota_sing ind pars discr brs n f res :
    eval discr tBox ->
    brs = [ (n,f) ] ->
    eval (mkApps f (repeat tBox n)) res ->
    eval (tCase (ind, pars) discr brs) res

| seval_fix f mfix idx argsv a av narg fn res :
    eval f (mkApps (tFix mfix idx) argsv) ->
    eval a av ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    #|argsv| = narg ->
    is_constructor_app_or_box av ->
    eval (tApp (mkApps fn argsv) av) res ->
    eval (tApp f a) res

| seval_fix_value f mfix idx argsv a av narg fn :
    eval f (mkApps (tFix mfix idx) argsv) ->
    eval a av ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    (#|argsv| <> narg \/ (#|argsv| = narg /\ ~~is_constructor_app_or_box av)) ->
    eval (tApp f a) (tApp (mkApps (tFix mfix idx) argsv) av)

| sred_cofix_case ip mfix idx args narg fn brs res :
    cunfold_cofix mfix idx = Some (narg, fn) ->
    eval (tCase ip (mkApps fn args) brs) res ->
    eval (tCase ip (mkApps (tCoFix mfix idx) args) brs) res

| sred_cofix_proj p mfix idx args narg fn res :
    cunfold_cofix mfix idx = Some (narg, fn) ->
    eval (tProj p (mkApps fn args)) res ->
    eval (tProj p (mkApps (tCoFix mfix idx) args)) res

| seval_delta c decl body (isdecl : declared_constant Σ c decl) res :
    decl.(cst_body) = Some body ->
    eval body res ->
    eval (tConst c) res

| seval_proj i pars arg discr args k res :
    eval discr (mkApps (tConstruct i k) args) ->
    eval (List.nth (pars + arg) args tDummy) res ->
    eval (tProj (i, pars, arg) discr) res

| seval_proj_box i pars arg discr :
    eval discr tBox ->
    eval (tProj (i, pars, arg) discr) tBox

| seval_app_cong f f' a a' :
    eval f f' ->
    ~~ (isLambda f' || isFixApp f' || isBox f') ->
    eval a a' ->
    eval (tApp f a) (tApp f' a')

| seval_atom_rel i : eval (tRel i) (tRel i)
| seval_atom_box : eval tBox tBox
| seval_atom_lambda na body body' :
    eval body body' ->
    eval (tLambda na body) (tLambda na body')
| seval_atom_construct ind c : eval (tConstruct ind c) (tConstruct ind c)
| seval_atom_fix defs defs' n :

    Forall2 eval (map dbody defs) (map dbody defs')

with seval_defs
