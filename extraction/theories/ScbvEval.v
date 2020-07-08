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
Inductive eval : term -> term -> Prop :=
(** Reductions *)
| eval_box a t t' :
    eval a tBox ->
    eval t t' ->
    eval (tApp a t) tBox

(** Beta *)
| eval_beta f na b a a' res :
    eval f (tLambda na b) ->
    eval a a' ->
    eval (csubst a' 0 b) res ->
    eval (tApp f a) res

(** Let *)
| eval_zeta na b0 b0' b1 res :
    eval b0 b0' ->
    eval (csubst b0' 0 b1) res ->
    eval (tLetIn na b0 b1) res

(** Case *)
| eval_iota ind pars discr c args brs res :
    eval discr (mkApps (tConstruct ind c) args) ->
    eval (iota_red pars c args brs) res ->
    eval (tCase (ind, pars) discr brs) res

(** Singleton case on a proof *)
| eval_iota_sing ind pars discr brs n f res :
    eval discr tBox ->
    brs = [ (n,f) ] ->
    eval (mkApps f (repeat tBox n)) res ->
    eval (tCase (ind, pars) discr brs) res

(** Fix unfolding, with guard *)
| eval_fix f mfix idx argsv a av narg fn res :
    eval f (mkApps (tFix mfix idx) argsv) ->
    eval a av ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    #|argsv| = narg ->
             is_constructor_app_or_box av ->
             eval (tApp (mkApps fn argsv) av) res ->
             eval (tApp f a) res

(** Fix stuck, with guard *)
| eval_fix_value f mfix idx argsv a av narg fn :
    eval f (mkApps (tFix mfix idx) argsv) ->
    eval a av ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    (#|argsv| <> narg \/ (#|argsv| = narg /\ ~~is_constructor_app_or_box av)) ->
    eval (tApp f a) (tApp (mkApps (tFix mfix idx) argsv) av)

(** CoFix-case unfolding *)
| red_cofix_case ip mfix idx args narg fn brs res :
    cunfold_cofix mfix idx = Some (narg, fn) ->
    eval (tCase ip (mkApps fn args) brs) res ->
    eval (tCase ip (mkApps (tCoFix mfix idx) args) brs) res

(** CoFix-proj unfolding *)
| red_cofix_proj p mfix idx args narg fn res :
    cunfold_cofix mfix idx = Some (narg, fn) ->
    eval (tProj p (mkApps fn args)) res ->
    eval (tProj p (mkApps (tCoFix mfix idx) args)) res

(** Constant unfolding *)
| eval_delta c decl body (isdecl : declared_constant Σ c decl) res :
    decl.(cst_body) = Some body ->
    eval body res ->
    eval (tConst c) res

(** Proj *)
| eval_proj i pars arg discr args k res :
    eval discr (mkApps (tConstruct i k) args) ->
    eval (List.nth (pars + arg) args tDummy) res ->
    eval (tProj (i, pars, arg) discr) res

(** Proj *)
| eval_proj_box i pars arg discr :
    eval discr tBox ->
    eval (tProj (i, pars, arg) discr) tBox

(** Atoms (non redex-producing heads) applied to values are values *)
| eval_app_cong f f' a a' :
    eval f f' ->
    ~~ (isLambda f' || isFixApp f' || isBox f') ->
    eval a a' ->
    eval (tApp f a) (tApp f' a')

| eval_atom_rel i : eval (tRel i) (tRel i)
| eval_atom_box : eval tBox tBox
| eval_atom_lambda na body body' :
    eval body body' ->
    eval (tLambda na body) (tLambda na body')
| eval_atom_construct ind c : eval (tConstruct ind c) (tConstruct ind c)
| eval_atom_fix defs defs' n :

    Forall2 eval (map dbody defs) (map dbody defs')

(** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
(* | eval_evar n l l' : *)
(*     Forall2 eval l l' -> *)
(*     eval (tEvar n l) (tEvar n l') *)


(** Atoms are values (includes abstractions, cofixpoints and constructors) *)
| eval_atom t : atom t -> eval t t.
