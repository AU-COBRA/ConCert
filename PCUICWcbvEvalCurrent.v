(* Distributed under the terms of the MIT license.   *)
(* Copied from the MetaCoq repo. Eventually, will be replced with the
actual version from MetaCoq after making it compatible with Coq 8.10 *)
Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec Lia CRelationClasses.
From Template Require Import config utils AstUtils.
Import Template.BasicAst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Set Asymmetric Patterns.
Require Import ssreflect ssrbool.

Local Ltac inv H := inversion H; subst.

(** * Weak-head call-by-value evaluation strategy.
  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.
  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Definition atom t :=
  match t with
  | tConstruct _ _ _
  | tFix _ _
  | tCoFix _ _
  | tLambda _ _ _
  | tSort _
  | tProd _ _ _ => true
  | _ => false
  end.

Definition isArityHead t :=
  match t with
  | tSort _
  | tProd _ _ _ => true
  | _ => false
  end.

Definition isEvar t :=
  match t with
  | tEvar _ _ => true
  | _ => false
  end.

Definition isFix t :=
  match t with
  | tFix _ _ => true
  | _ => false
  end.

Definition isFixApp t :=
  match fst (decompose_app t) with
  | tFix _ _ => true
  | _ => false
  end.

Definition isCoFix t :=
  match t with
  | tCoFix _ _ => true
  | _ => false
  end.

Definition isConstruct t :=
  match t with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition isAssRel Γ x :=
  match x with
  | tRel i =>
    match option_map decl_body (nth_error Γ i) with
    | Some None => true
    | _ => false
    end
  | _ => false
  end.

Definition isAxiom Σ x :=
  match x with
  | tConst c u =>
    match lookup_env Σ c with
    | Some (ConstantDecl _ {| cst_body := None |}) => true
    | _ => false
    end
  | _ => false
  end.

Definition isStuckFix t args :=
  match t with
  | tFix mfix idx =>
    match unfold_fix mfix idx with
    | Some (narg, fn) =>
      ~~ is_constructor narg args
    | None => false
    end
  | _ => false
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. now rewrite -mkApps_nested in H.
Qed.

Section Wcbv.
  Context (Σ : global_declarations) (Γ : context).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> term -> Prop :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' res :
      eval f (tLambda na t b) ->
      eval a a' ->
      eval (subst10 a' b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (subst10 b0' b1) res ->
      eval (tLetIn na b0 t b1) res

  (** Local variables: defined or undefined *)
  | eval_rel_def i body res :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      eval (lift0 (S i) body) res ->
      eval (tRel i) res

  | eval_rel_undef i :
      option_map decl_body (nth_error Γ i) = Some None ->
      eval (tRel i) (tRel i)

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance_constr u body) res ->
      eval (tConst c u) res

  (** Axiom *)
  | eval_axiom c decl (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = None ->
      eval (tConst c u) (tConst c u)

  (** Case *)
  | eval_iota ind pars discr c u args p brs res :
      eval discr (mkApps (tConstruct ind c u) args) ->
      eval (iota_red pars c args brs) res ->
      eval (tCase (ind, pars) p discr brs) res

  (** Proj *)
  | eval_proj i pars arg discr args k u a res :
      eval discr (mkApps (tConstruct i k u) args) ->
      nth_error args (pars + arg) = Some a ->
      eval a res ->
      eval (tProj (i, pars, arg) discr) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx args args' narg fn res :
      eval f (tFix mfix idx) ->
      unfold_fix mfix idx = Some (narg, fn) ->
      (* There must be at least one argument for this to succeed *)
      is_constructor narg args' ->
      (** We unfold only a fix applied exactly to narg arguments,
          avoiding overlap with [eval_beta] when there are more arguments. *)
      S narg = #|args| ->
      (* NOTE: we modify the ralation to match the traslation from Oak.
         For the translated terms we always know that the fixpoint is defined by
         recursion of the firts argument *)
      narg = 0 ->
      (* We reduce all arguments before unfolding *)
      All2 eval args args' ->
      eval (mkApps fn args') res ->
      eval (mkApps f args) res

  (** Fix stuck, with guard *)
           (** We ignore this case, because it is not relevant for the Oak/Acorn translation *)
  (* | eval_fix_value f mfix idx args args' : *)
  (*     eval f (tFix mfix idx) -> *)
  (*     (* We reduce all arguments to produce a suspended fix application value *)
  (*        Note that the stuck fixpoint can be applied to any number of arguments *)
  (*        here. *) *)
  (*     All2 eval args args' -> *)
  (*     isStuckFix (tFix mfix idx) args' -> *)
  (*     eval (mkApps f args) (mkApps (tFix mfix idx) args') *)

  (** CoFix-case unfolding *)
  | red_cofix_case ip mfix idx p args narg fn brs res :
      unfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip p (mkApps fn args) brs) res ->
      eval (tCase ip p (mkApps (tCoFix mfix idx) args) brs) res

  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn res :
      unfold_cofix mfix idx = Some (narg, fn) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p (mkApps (tCoFix mfix idx) args)) res

  (** Non redex-producing heads applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      ~~ (isLambda f' || isFixApp f' || isArityHead f') ->
      eval a a' ->
      eval (tApp f a) (tApp f' a')

  (** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
  (* | eval_evar n l l' : *)
  (*     Forall2 eval l l' -> *)
  (*     eval (tEvar n l) (tEvar n l') *)


  (** Atoms are values (includes abstractions, cofixpoints and constructors
      along with type constructors) *)
  | eval_atom t : atom t -> eval t t.

  (** Characterization of values for this reduction relation.
      Only constructors and cofixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments:
      - box
      - abstractions
      - constant constructors
      - unapplied fixpoints and cofixpoints
   *)

  Definition value_head x :=
    isConstruct x || isCoFix x || isAssRel Γ x || isAxiom Σ x.

  (* Lemma value_head_atom x : value_head x -> atom x. *)
  (* Proof. destruct x; auto. Qed. *)

  Inductive value : term -> Prop :=
  | value_atom t : atom t -> value t
  (* | value_evar n l l' : Forall value l -> Forall value l' -> value (mkApps (tEvar n l) l') *)
  | value_app t l : value_head t -> All value l -> value (mkApps t l)
  | value_stuck_fix f args :
      All value args ->
      isStuckFix f args ->
      value (mkApps f args)
  .

  (* Lemma value_values_ind : forall P : term -> Prop, *)
  (*     (forall t, atom t -> P t) -> *)
  (*     (* (forall n l l', Forall value l -> Forall P l -> Forall value l' -> Forall P l' -> *) *)
  (*     (*                 P (mkApps (tEvar n l) l')) -> *) *)
  (*     (forall t l, value_head t -> All value l -> All P l -> P (mkApps t l)) -> *)
  (*     (forall f args, *)
  (*         All value args -> *)
  (*         All P args -> *)
  (*         isStuckFix f args -> *)
  (*         P (mkApps f args)) -> *)
  (*     forall t : term, value t -> P t. *)
  (* Proof. *)
  (*   intros P ???. *)
  (*   fix value_values_ind 2. destruct 1. *)
  (*   - easy. *)
  (*   - eapply H0; auto. *)
  (*     revert l a. fix aux 2. destruct 1. constructor; auto. *)
  (*     constructor. now eapply value_values_ind. now apply aux. *)
  (*   - eapply X1; eauto. *)
  (*     clear i. revert args a. fix aux 2. destruct 1. constructor; auto. *)
  (*     constructor. now eapply value_values_ind. now apply aux. *)
  (* Defined. *)

  (* NOTE : proved in the actual development *)
  Lemma value_final e : value e -> eval e e.
  Proof.
    Admitted.

  End Wcbv.
