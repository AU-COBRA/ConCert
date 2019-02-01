(* Various auxillary facts usefull for proving correctness of the translation and the interpreter *)

Require Import CustomTactics.
Require Import Ast.
Require Import EvalE.
Require Import String List.

Require Import Morphisms Setoid.

Require Import Template.monad_utils.

Import FunctionalExtensionality.

Open Scope string_scope.
Import ListNotations.

Import InterpreterEnvList.


Section Values.

  Lemma vars_to_apps_unfold vs : forall acc v,
    vars_to_apps acc (vs ++ [v]) = eApp (vars_to_apps acc vs) v.
  Proof.
    simpl.
    induction vs using rev_ind;intros acc v.
    + reflexivity.
    + simpl.
      unfold vars_to_apps.
      rewrite fold_left_app; easy.
  Qed.

  Lemma subst_env_empty :
    forall e : expr, e = subst_env [] e.
  Proof.
    intros e.
    induction e using expr_ind_case; simpl; try easy; try congruence.
    f_equal;auto.
    rewrite <- map_id at 1.
    eapply @Induction.forall_map_spec.
    eapply H.
    intros x f. destruct x;simpl in *. f_equal. assumption.
  Qed.

  (* For simplicity, we consider only constructors of arity 0 and 1 *)
  Inductive accepted_val : val -> Prop :=
  | avContsr0 : forall i nm v, accepted_val v -> accepted_val (vConstr i nm [])
  | avContsr1 : forall i nm v, accepted_val v -> accepted_val (vConstr i nm [v])
  | avClos : forall ρ nm ty e, accepted_val (vClos ρ nm ty e).

  Lemma expr_eval_econstr {n nm Σ ρ i v} :
    expr_eval n Σ ρ (eConstr i nm) = Ok v ->
    v = vConstr i nm [].
  Proof.
    intros H.
    destruct n;inversion H. reflexivity.
  Qed.

  (** Correctness of the value-back-to-expression transformation *)
  (* A a creterion of correctness we consider the property that
     if we start with a value [v1], the output of [from_val v1] after evaluation,
     should give as some [v2] equivalent to [v1].
     Note that we cannot ask [v1] and [v2] to be equal,
     instead we ask for equivalence. This is due to substitutions of the
     values in the environment while converting closures back to expressions *)
  Lemma from_val_correct n Σ v1 v2 :
    accepted_val v1 ->
    expr_eval n Σ enEmpty (from_val v1) = Ok v2 ->
    v1 ≈ v2.
  Proof.
    intros Hav He.
    revert dependent n.
    revert dependent v2.
    induction v1 using val_ind_full;intros v2 n0 H1.
    + destruct n0;tryfalse.
      inversion Hav;subst.
      * simpl in H1. inversion H1. reflexivity.
      * simpl in H1.
        remember (expr_eval n0 Σ enEmpty (eConstr i n)) as c.
        remember (expr_eval n0 Σ enEmpty (from_val v)) as fv.
        destruct c as [c0 | | ];try destruct c0;destruct fv;tryfalse.
        ** inversion H1 as [H1'].
           symmetry in Heqfv.
           apply Forall_inv in H.
           pose proof (H H2 _ _ Heqfv) as HH. subst.
           symmetry in Heqc.
           pose proof (expr_eval_econstr Heqc) as HH1. inversion HH1;subst.
           simpl. clear H Heqfv H1.
           (* this rewrite actually uses setoid_rewrite along the ≈ relation *)
           rewrite HH.
           reflexivity.
        ** symmetry in Heqc.
           pose proof (expr_eval_econstr Heqc);tryfalse.
    + simpl in H1.
      destruct H.
      * destruct n0;tryfalse. simpl in H1.
        inversion_clear H1.
        rewrite <- subst_env_empty. reflexivity.
      * destruct n0;tryfalse. simpl in H1.
        inversion_clear H1.
        constructor.
        destruct (nm =? n) eqn:Hnm.
        ** unfold inst_env. simpl.
           rewrite <- subst_env_empty.
           apply eqb_eq in Hnm. subst.
           rewrite eqb_refl. reflexivity.
        ** unfold inst_env. simpl.
           rewrite Hnm.
           rewrite <- subst_env_empty.
           reflexivity.
      * (* It takes 2 steps to evaluate a fixpoint to a closure *)
        destruct n0;tryfalse.
        destruct n0;tryfalse. simpl in H1. inversion H1.
        constructor.
        unfold inst_env. simpl.
        rewrite <- subst_env_empty.
        reflexivity.
  Qed.

End Values.