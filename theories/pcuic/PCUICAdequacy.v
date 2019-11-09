From MetaCoq Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICWcbvEval PCUICTyping.

From ConCert Require Import CustomTactics MyEnv
     EnvSubst Ast EvalE PCUICFacts  PCUICTranslate
     PCUICCorrectnessAux PCUICCorrectness Wf Misc.

From Coq Require Import String List.

Import ListNotations ssrbool Basics Lia.
Import NamelessSubst.

Lemma lookup_i_exprs_none :
  forall (ρ : env val) (n : nat),
  lookup_i ρ n = None -> lookup_i (exprs ρ) n = None.
Proof.
Admitted.

Lemma eval_ty_closed_eq ty ρ :
  iclosed_ty 0 (subst_env_i_ty 0 (exprs ρ) ty) = true ->
  eval_type_i 0 ρ ty = Some ty.
Proof.
  (* In order for this to hold, one needs to ensure that applications are always to inductives *)
Admitted.

Lemma valid_env_empty e n :
  valid_env [] n e = true.
Proof.
  Admitted.

Theorem expr_to_term_terminates Σ1 Σ2 (Γ:=[]) ρ
        (e1 e2 : expr) (v : term):
  genv_ok Σ1 ->
  env_ok Σ1 ρ ->
  e1.[exprs ρ] = e2 ->
  iclosed_n 0 e2 = true ->
  Σ2 ;;; Γ |- t⟦e2⟧Σ1 ⇓ v ->
  exists k, eval(k, Σ1, ρ, e1) <> NotEnoughFuel.
Proof.
  revert e2 ρ v.
  induction e1 using expr_elim_case;intros e2 ρ v Hgeok Hρ_ok  Heq Hc He.
  + subst;cbn in *. replace (n-0) with n in * by lia.
    exists 1;simpl.
    destruct (lookup_i ρ n) eqn:Hlook;intros ?;tryfalse.
  + subst;cbn in *. tryfalse.
  + subst;cbn in *.
    unfold is_true in *; repeat rewrite  Bool.andb_true_iff in *.
    destruct Hc.
    exists 1. cbn. destruct (eval_type_i 0 ρ t);
    cbn; destruct (valid_env ρ 1 e1);intros ?;tryfalse.
  + subst;cbn in *.
    unfold is_true in *; repeat rewrite  Bool.andb_true_iff in *.
    destruct Hc.
    exists 1. cbn. destruct (valid_env ρ 1 e1);intros ?;tryfalse.
  + subst;cbn in *.
    unfold is_true in *; repeat rewrite  Bool.andb_true_iff in *.
    destruct Hc as [[? ?] ?].
    inversion He.
    * subst.
      assert (Hev1 : exists k : nat, (eval (k, Σ1, ρ, e1_1)) <> NotEnoughFuel) by
          (eapply IHe1_1;eauto with hints).
      destruct Hev1 as [k1 Hv1].
      exists (1+k1). cbn.
      destruct (eval (k1, Σ1, ρ, e1_1)) eqn:?;destruct (eval_type_i 0 ρ t);
        intros ?;tryfalse. cbn in *.
      assert (Σ2;;; Γ |- t⟦ e1_1.[exprs ρ] ⟧ Σ1 ⇓ t⟦of_val_i v0⟧Σ1).
      { eapply expr_to_term_sound;eauto. }
      assert (b0' = t⟦of_val_i v0⟧Σ1).
      {eapply PcbvCurr.eval_deterministic;eauto. }
      subst.
      assert (Σ2;;; Γ |- t⟦ (e1_2 .[ exprs ρ] 1).[[(n, of_val_i v0)]] ⟧ Σ1 ⇓ v).
      { rewrite <- subst_term_subst_env with (nm:=n) (v:=v0) (Σ:=Σ1) (e:=e1_2 .[ exprs ρ] 1);
          try eapply eval_val_ok;eauto with hints.
        (* eapply ty_expr_env_ok_app_rec. *) admit.  }
      assert (exists k : nat, (eval (k, Σ1, ρ # [n ~> v0], e1_2)) <> NotEnoughFuel).
      { eapply IHe1_2 with (ρ:=ρ # [n ~> v0]);eauto with hints.
        constructor; unfold compose;cbn; try eapply eval_val_ok;eauto with hints. eauto.
        admit. admit. }
      admit.
    * (* Impossible case: mkApps f args <> tLetIn ... *)
      admit.
    * (* Impossible case: mkApps f args <> tLetIn ... *)
      admit.
    * tryfalse.
  + (* application case *)
    subst;cbn in *. unfold is_true in *; repeat rewrite  Bool.andb_true_iff in *.
    destruct Hc.
    inversion He. subst.
    * (* lambda case *) admit.
    * (* fix case *)
      (* How I can invert the equation for mkApps? *)
      admit.
    * (* stuck fix case *) unfold PcbvCurr.isStuckFix in *. admit.
    * (* app congr case *)
      subst.

Theorem expr_to_term_terminates Σ1 Σ2 (Γ:=[]) ρ
        (e1 e2 : expr) (v : term):
  genv_ok Σ1 ->
  env_ok Σ1 ρ ->
  e1.[exprs ρ] = e2 ->
  iclosed_n 0 e2 = true ->
  Σ2 ;;; Γ |- t⟦e2⟧Σ1 ⇓ v ->
  exists k v, eval(k, Σ1, ρ, e1) = Ok v.
Proof.
  revert e2 ρ v.
  induction e1 using expr_elim_case;intros e2 ρ v Hgeok Hρ_ok  Heq Hc He.
  + subst;cbn in *. replace (n-0) with n in * by lia.
    exists 1;simpl.
    destruct (lookup_i ρ n) eqn:Hlook.
    * eexists;simpl;eauto.
    * specialize (lookup_i_exprs_none _ _ Hlook) as Hlook1.
      rewrite Hlook1 in *. cbn in *;tryfalse.
  + subst;cbn in *. tryfalse.
  + subst;cbn in *.
    unfold is_true in *; repeat rewrite  Bool.andb_true_iff in *.
    destruct Hc.
    assert (v = tLambda (nNamed n) T⟦ subst_env_i_ty 0 (exprs ρ) t ⟧ t⟦ e1 .[ exprs ρ] 1 ⟧ Σ1).
    { eapply eval_deterministic;eauto. eapply value_final;eauto with hints. }
    subst.
    (* assert (iclosed_n 0 e1.[exprs ρ] = true). eauto with hints. *)
    (* assert (exists k1 v1, (eval (k1, Σ1, ρ, e1)) = Ok v1). *)
    (* { eapply IHe1;eauto. eapply subst_env_iclosed_n_inv with ();eauto with hints. *)
    (*   eapply eval_ty_expr_env_ok; eauto with hints. } *)
    exists 1. cbn. rewrite eval_ty_closed_eq. cbn.
    inversion He. 3 : { }
    specialize (eval_lam_inv _ _ _ _ _ _ _ _ X0). in X0.
    inversion X0.

  + subst;cbn in *.
    unfold is_true in *; repeat rewrite  Bool.andb_true_iff in *.
    destruct Hc.
    assert (v = tLambda (nNamed n) (tSort Universe.type0) t⟦ e ⟧ Σ1).
    { eapply eval_deterministic;eauto. eapply value_final;eauto with hints. }
    subst.
    exists 1. cbn.
    cbn. rewrite valid_env_empty. eexists;eauto.
  + subst;cbn in *.
    unfold is_true in *; repeat rewrite  Bool.andb_true_iff in *.
    destruct Hc as [[? ?] ?].
    inversion He.
    * subst.
      assert (Hv1 : exists (k : nat) (v1 : val), (eval (k, Σ1, [], e1)) = Ok v1) by eauto.
      destruct Hv1 as [k1 [v1 Hev1]].
      exists (1+k1). cbn. rewrite Hev1.
      rewrite eval_ty_closed_eq by auto. cbn.
    { eapply eval_deterministic;eauto. eapply value_final;eauto with hints. }
    subst.
    exists 1. cbn.
    cbn. rewrite valid_env_empty. eexists;eauto.
