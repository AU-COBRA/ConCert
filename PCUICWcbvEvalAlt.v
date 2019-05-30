(* A verison of WcbvEval with values as a separate inductive type  *)
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils univ BasicAst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance default_checker_flags.

(** * Weak (head) call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction.

  TODO: CoFixpoints *)

  Inductive value :=
  | vpRel : nat -> value
  | vpEvar : nat -> list term -> value
  | vpLambda : name -> term -> term -> value
  | vpProd : name -> term -> term -> value
  | vpInd : inductive -> universe_instance -> value
  | vpConstruct : inductive -> nat -> universe_instance -> list value -> value.

Section Wcbv.
  Context (Σ : global_declarations) (Γ : context).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> value -> Prop :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' res :
      eval f (vpLambda na t b) ->
      eval a a' ->
      eval (subst10 a' b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (subst10 b0' b1) res ->
      eval (tLetIn na b0 t b1) res

  (** Local variables: defined or undefined *)
  | eval_rel_def i (isdecl : i < List.length Γ) body res :
      (safe_nth Γ (exist _ i isdecl)).(decl_body) = Some body ->
      eval (lift0 (S i) body) res ->
      eval (tRel i) res

  | eval_rel_undef i (isdecl : i < List.length Γ) :
      (safe_nth Γ (exist _ i isdecl)).(decl_body) = None ->
      eval (tRel i) (tRel i)

  (** Case *)
  | eval_iota ind pars discr c u args p brs res :
      eval discr (mkApps (tConstruct ind c u) args) ->
      eval (iota_red pars c args brs) res ->
      eval (tCase (ind, pars) p discr brs) res

  (** Fix unfolding, with guard *)
  | eval_fix mfix idx args args' narg fn res :
      unfold_fix mfix idx = Some (narg, fn) ->
      Forall2 eval args args' -> (* FIXME should we reduce the args after the recursive arg here? *)
      is_constructor narg args' = true ->
      eval (mkApps fn args') res ->
      eval (mkApps (tFix mfix idx) args) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance_constr u body) res ->
      eval (tConst c u) res

  (** Proj *)
  | eval_proj i pars arg discr args k u res :
      eval discr (mkApps (tConstruct i k u) args) ->
      eval (List.nth (pars + arg) args tDummy) res ->
      eval (tProj (i, pars, arg) discr) res

  (* TODO CoFix *)
  | eval_abs na M N : eval (tLambda na M N) (tLambda na M N)

  | eval_prod na b t b' t' :
      eval b b' -> eval t t' -> eval (tProd na b t) (tProd na b' t')

  | eval_app_ind t i u a a' :
      eval t (tInd i u) ->
      Forall2 eval a a' ->
      eval (mkApps t a) (mkApps (tInd i u) a')

  | eval_app_constr f i k u a a' :
      eval f (tConstruct i k u) ->
      Forall2 eval a a' ->
      eval (mkApps f a) (mkApps (tConstruct i k u) a').
