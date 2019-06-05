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
  | vpFix : mfixpoint term -> nat -> value
  | vpProd : name -> term -> term -> value
  | vpInd : inductive -> universe_instance -> list value -> value
  | vpConstruct : inductive -> nat -> universe_instance -> list value -> value.


  Fixpoint value_to_term (v : value): term :=
    match v with
    | vpRel i => tRel i
    | vpEvar x x0 => tEvar x x0
    | vpLambda x x0 x1 => tLambda x x0 x1
    | vpFix mfix n => tFix mfix n
    | vpProd x x0 x1 => tProd x x0 x1
    | vpInd ind u vs => mkApps (tInd ind u) (map value_to_term vs)
    | vpConstruct ind n u vs => mkApps (tConstruct ind n u) (map value_to_term vs)
    end.

  Notation "'terms' ts" := (map value_to_term ts) (at level 50).

  Definition is_vcontructor (v : value):=
    match v with
    | vpConstruct _ _ _ _ => true
    | _ => false
    end.

Section Wcbv.

  Open Scope list.
  Context (Σ : global_declarations) (Γ : context).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> value -> Prop :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' res :
      eval f (vpLambda na t b) ->
      eval a a' ->
      eval (subst10 (value_to_term a') b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (subst10 (value_to_term b0') b1) res ->
      eval (tLetIn na b0 t b1) res

  (** Local variables: defined or undefined *)
  | eval_rel_def i (isdecl : i < List.length Γ) body res :
      (safe_nth Γ (exist _ i isdecl)).(decl_body) = Some body ->
      eval (lift0 (S i) body) res ->
      eval (tRel i) res

  | eval_rel_undef i (isdecl : i < List.length Γ) :
      (safe_nth Γ (exist _ i isdecl)).(decl_body) = None ->
      eval (tRel i) (vpRel i)

  (** Case *)
  | eval_iota ind pars discr c u args p brs res :
      eval discr (vpConstruct ind c u args) ->
      eval (iota_red pars c (terms args) brs) res ->
      eval (tCase (ind, pars) p discr brs) res
  (** Fix unfolding, with guard *)
  (* assuming that the fixpoint is defined by recursion of the first arg *)

  | eval_fix idx mfix f fn b a v res :
      eval f (vpFix mfix idx) ->
      unfold_fix mfix idx = Some (0, fn) ->
      eval a v ->
      is_vcontructor v = true ->
      eval (subst10 (value_to_term v) b) res ->
      eval (tApp f a) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance_constr u body) res ->
      eval (tConst c u) res

  (** Proj *)
  (* Not sure about this *)
  (* | eval_proj i pars arg discr args k u res : *)
  (*     eval discr (vpConstruct i k u args) -> *)
  (*     eval (List.nth (pars + arg) args tDummy) res -> *)
  (*     eval (tProj (i, pars, arg) discr) res *)

  (* TODO CoFix *)
  | eval_abs na M N : eval (tLambda na M N) (vpLambda na M N)

  | eval_prod na b t :
      eval (tProd na b t) (vpProd na b t)

  | eval_app_ind t i u a v l :
      eval t (vpInd i u l) ->
      eval a v ->
      eval (tApp t a) (vpInd i u (l ++ [v]))

  | eval_app_constr t i k u a v l :
      eval t (vpConstruct i u k l) ->
      eval a v ->
      eval (tApp t a) (vpConstruct i u k (l ++ [v])).

End Wcbv.