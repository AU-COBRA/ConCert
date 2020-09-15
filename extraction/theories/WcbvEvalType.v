From Coq Require Import Bool.
From Coq Require Import List.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import ETyping.
From MetaCoq.Erasure Require EWcbvEval.
From MetaCoq.Template Require Import utils.

Notation atom := EWcbvEval.atom.
Notation cunfold_fix := EWcbvEval.cunfold_fix.
Notation cunfold_cofix := EWcbvEval.cunfold_cofix.
Notation isFixApp := EWcbvEval.isFixApp.
Notation closed_unfold_fix_cunfold_eq := EWcbvEval.closed_unfold_fix_cunfold_eq.
Notation closed_unfold_cofix_cunfold_eq := EWcbvEval.closed_unfold_cofix_cunfold_eq.
Notation isStuckFix := EWcbvEval.isStuckFix.
Notation isFixApp_mkApps := EWcbvEval.isFixApp_mkApps.
Notation substl := EWcbvEval.substl.

Import ListNotations.
Open Scope bool.

Section Wcbv.
  Context (Σ : global_declarations).

  Inductive eval : term -> term -> Type :=
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
      (#|argsv| <> narg \/ (#|argsv| = narg /\ negb (is_constructor_app_or_box av))) ->
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
  | eval_proj i pars arg discr args res :
      eval discr (mkApps (tConstruct i 0) args) ->
      eval (List.nth (pars + arg) args tDummy) res ->
      eval (tProj (i, pars, arg) discr) res

  (** Proj *)
  | eval_proj_box i pars arg discr :
      eval discr tBox ->
      eval (tProj (i, pars, arg) discr) tBox

  (** Atoms (non redex-producing heads) applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      negb (isLambda f' || isFixApp f' || isBox f') ->
      eval a a' ->
      eval (tApp f a) (tApp f' a')

  (** Atoms are values (includes abstractions, cofixpoints and constructors) *)
  | eval_atom t : atom t -> eval t t.
End Wcbv.

Derive Signature for eval.

Notation "Σ ⊢ s ▷ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.
Notation "Σ 'p⊢' s ▷ t" := (EWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma evalT_eval {Σ s t} :
  Σ ⊢ s ▷ t ->
  Σ p⊢ s ▷ t.
Proof. induction 1; eauto using EWcbvEval.eval. Qed.

Lemma eval_evalT {Σ s t} :
  Σ p⊢ s ▷ t ->
  ∥Σ ⊢ s ▷ t∥.
Proof. induction 1; sq; eauto using eval. Qed.

Lemma eval_deterministic {Σ t v v'} :
  Σ ⊢ t ▷ v ->
  Σ ⊢ t ▷ v' ->
  v = v'.
Proof.
  intros ev1 ev2.
  eapply EWcbvEval.eval_deterministic; eauto using evalT_eval.
Qed.

Lemma eval_mkApps_tCoFix Σ mfix idx args v :
  Σ ⊢ mkApps (tCoFix mfix idx) args ▷ v ->
  exists args', v = mkApps (tCoFix mfix idx) args'.
Proof.
  intros ev.
  eapply EWcbvEval.eval_mkApps_tCoFix; eauto using evalT_eval.
Qed.
