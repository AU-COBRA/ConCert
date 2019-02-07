(* Proof of correctness of the translation from core language expression to the Template Coq terms *)
Require Import Ast EvalE Facts CustomTactics String.
Require Template.WcbvEval.
Require Import Template.All.

Require Import List.

Import ListNotations.

Import Lia.

Notation "Σ ;;; Γ |- t1 ⇓ t2 " := (WcbvEval.eval Σ Γ t1 t2) (at level 50).
Notation "T⟦ e ⟧ Σ " := (expr_to_term Σ e) (at level 40).

Import InterpreterEnvList.

Lemma map_env_list_size {A B} (f : Ast.name -> A -> B) (ρ : env A) :
  length (map_env_list f ρ) = size ρ.
Proof.
Admitted.

Lemma from_option_indep {A} (o : option A) d  d' v :
  o = Some v -> from_option o d = from_option o d'.
Proof.
  intros;subst;easy.
Qed.

Lemma lookup_i_norec_some {A} {ρ : env A} {n : nat} :
  n < size ρ ->
  exists v, lookup_i_norec ρ n = Some v.
Proof.
  revert dependent n.
  induction ρ;intros n1 Hlt.
  + eexists;easy.
  + simpl in *. destruct (Nat.eqb n1 0) eqn:Hn1.
    * eexists;reflexivity.
    * assert (Hn2 : exists n2, n1 = S n2) by
          (destruct n1 as [ | n2]; tryfalse; exists n2; reflexivity).
      destruct Hn2 as [n2 Heq_n2]. replace (n1-1) with n2 by lia.
      subst. apply Lt.lt_S_n in Hlt.
      (* assert (n1=0) by (apply EqNat.beq_nat_eq; easy). subst. *)
Admitted.

Lemma inst_env_i_in ρ n :
  n < size ρ ->
  exists v, lookup_i ρ n = Some v /\ inst_env_i ρ (eRel n) = from_val_i v.
Proof.
  intros Hlt.
  revert dependent n.
  induction ρ;intros n1 Hlt.
  + inversion Hlt.
  + destruct (Nat.eqb n1 0) eqn:Hn1.
    * eexists. split.
      ** simpl. rewrite Hn1.
         reflexivity.
      ** simpl in *. unfold inst_env_i,subst_env_i. simpl.
         assert (n1=0) by (apply EqNat.beq_nat_eq; easy).
         subst. simpl. admit.
    * assert (Hn2 : exists n2, n1 = S n2) by (destruct n1 as [ | n2]; tryfalse; exists n2; reflexivity).
      destruct Hn2 as [n2 Heq_n2]. replace (n1-1) with n2 by lia. subst. simpl in Hlt.
      apply Lt.lt_S_n in Hlt.
      specialize (IHρ _ Hlt). destruct IHρ as [v HH]. destruct HH as [H1 H2].
      exists v. split.
      ** simpl in *. replace (n2 - 0) with n2 by lia. assumption.
      ** specialize (lookup_i_norec_some Hlt) as Hlookup.
         destruct Hlookup.
         simpl in *. unfold inst_env_i,subst_env_i in *. simpl in *.
         rewrite <- H2. replace (n2 - 0) with n2 by lia.
         eapply from_option_indep.

  (*        apply nth_indep. rewrite map_env_list_size. *)
  (*        assumption. *)
  (* + simpl in *. *)
Admitted.

Lemma inst_env_i_notin ρ n :
  size ρ <= n -> lookup_i ρ n = None.
Proof.
  Admitted.

Lemma Wcbv_from_value_value v Σ : WcbvEval.value (T⟦ from_val_i v⟧Σ).
Proof.
Admitted.

(* This should from the fact that ⇓ is deterministic and
   the fact that value evaluates to itself, but the fact that
   ⇓ is deterministic is not yet proved in Template Coq *)
Lemma Wcbv_eval_value_determ Σ (Γ:=[]) t1 t2 :
  WcbvEval.value t1 -> Σ ;;; Γ |- t1 ⇓ t2 -> t1 = t2.
Proof.
  Admitted.


Theorem expr_to_term_sound n ρ Σ1 Σ2 (Γ:=[]) (e1 e2 : expr) (t : term) (v : val) :
  inst_env_i ρ e1 = e2 ->
  Σ2 ;;; Γ |- T⟦e2⟧Σ1 ⇓ t ->
  expr_eval_i n Σ1 ρ e1 = Ok v ->
  t = T⟦from_val_i v⟧Σ1.
Proof.
  revert dependent v.
  revert dependent t.
  revert dependent ρ.
  revert dependent e2.
  revert dependent e1.
  induction n.
  - intros;tryfalse.
  - intros e1 e2 ρ t v Henv HT He.
    destruct e1.
    + (* eRel*)
      autounfold with facts in *. simpl in *.
      destruct (lookup_i ρ n0) eqn:Hlookup;tryfalse. simpl in He;inversion He;subst.

      assert (Hn0 : n0 < size ρ \/ size ρ <= n0) by lia.
      destruct Hn0 as [Hlt | Hge].
      * destruct (inst_env_i_in _ _ Hlt) as [v1 HH].
        destruct HH as [H1 H2].
        assert (v1 = v) by congruence. subst.
        rewrite H2 in HT.
        symmetry.
        eapply Wcbv_eval_value_determ;
        [apply Wcbv_from_value_value | eassumption ].
      * specialize (inst_env_i_notin _ _ Hge) as Hnone;tryfalse.
    + (* eVar *)
      (* This case is trivial because we only consider terms with de Bruijn indices *)
      destruct n0; tryfalse.
    + (* eLambda *)
      autounfold with facts in *. simpl in HT. simpl in He.
      inversion He. rewrite <- Henv in HT. simpl. inversion HT. subst.
      reflexivity.
    + (* eLetIn *)
      autounfold with facts in *. simpl in HT. simpl in He.
      destruct (expr_eval_general n false Σ1 ρ e1_1);tryfalse.
      rewrite <- Henv in HT.
      unfold inst_env_i,subst_env_i in Henv. simpl in Henv.
      simpl in *. inversion HT. subst.
Admitted.