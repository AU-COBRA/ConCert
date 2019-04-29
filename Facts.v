(* Various auxillary facts usefull for proving correctness of the translation and the interpreter *)

Require Import String List.
Require Import Morphisms Setoid.

Require Import Template.monad_utils.

Require Import CustomTactics MyEnv Ast EvalE.

Import Basics.
Open Scope program_scope.

Open Scope string_scope.
Import ListNotations.
Import Lia.
Import Nat.

Import InterpreterEnvList.

Hint Unfold expr_eval_n expr_eval_i : facts.

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

  Lemma vars_to_apps_iclosed_n :
        forall (i : inductive) (n0 : name) (l : list val) (n : nat),
          Forall (fun v : val => iclosed_n n (from_val_i v) = true) l ->
          iclosed_n n (vars_to_apps (eConstr i n0) (map from_val_i l)) = true.
  Proof.
    intros i n0 l n H.
    induction l using rev_ind.
    + reflexivity.
    + rewrite map_app. simpl. rewrite vars_to_apps_unfold.
      simpl. rewrite Forall_app in H. destruct H as [H1 H2].
      apply Forall_inv in H2. rewrite H2. rewrite IHl by assumption.
      reflexivity.
  Qed.

  Lemma Forall_lookup_i {A} ρ n e (P : A -> Prop) :
    ForallEnv P ρ -> lookup_i ρ n = Some e -> P e.
  Proof.
    intros Hfe Hl.
    revert dependent n.
    induction Hfe;intros n Hl.
    + inversion Hl.
    + simpl in *. destruct x; destruct (Nat.eqb n 0);inversion Hl;subst;eauto.
  Qed.


  Lemma lookup_i_length {A} (ρ : env A) n :
    (n <? length ρ) = true -> exists e, lookup_i ρ n = Some e.
  Proof.
  Admitted.

  Lemma iclosed_m_n e : forall n m, iclosed_n n e = true -> iclosed_n (n+m) e = true.
  Proof.
    induction e; intros n1 m1 H;try inversion H;auto.
    simpl in *.
  Admitted.

  Lemma iclosed_n_0 e : forall n, iclosed_n 0 e = true -> iclosed_n n e = true.
  Proof.
    apply iclosed_m_n.
  Qed.

  Lemma iclosed_n_lookup :
    forall (e1 e2 : expr) (ρ : env expr)  (n : nat),
      iclosed_n 0 (subst_env_i_aux 0 ρ e1) = true ->
      lookup_i ρ n = Some e2 ->
      iclosed_n 0 e2 = true.
  Proof.
    intros e1.
    induction e1;intros e2 ρ n1 Hc Hl.
    + simpl in *. replace (n-0) with n in * by lia.
      destruct (lookup_i ρ n);tryfalse. simpl in *.
  Admitted.

  Lemma iclosed_Sn_subst_env:
    forall (ρ : env expr) (e : expr),
      iclosed_n 0 (subst_env_i_aux 0 ρ e) = true ->
      iclosed_n 1 (subst_env_i_aux 1 ρ e) = true.
  Proof.
    intros ρ e0 Hc.
    induction e0 using expr_ind_case;auto.
    + simpl in *. destruct n.
      * reflexivity.
      * replace (S n - 1) with n in * by lia. simpl in *.
        destruct (lookup_i ρ (S n)) eqn:Hl;tryfalse. simpl in *.
  Admitted.

  Lemma subst_env_iclosed_n :
    forall n (ρ : env expr) (e : expr),
      Forall (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n (n + length ρ) e = true <-> iclosed_n n (e.[ρ]n) = true.
  Proof.
    intros n ρ e H.
    split.
    - (* -> *)
      revert dependent ρ.
      induction e using expr_ind_case;intros ρ Hc Hec;simpl;tryfalse;auto.
      + (* eRel *)
        unfold subst_env_i. simpl.
        simpl in *.
        destruct (n <=? n0) eqn:Hnle.
        * rewrite PeanoNat.Nat.ltb_lt in *.
          rewrite PeanoNat.Nat.leb_le in *.
          assert (Hc' : n0-n < length ρ) by lia.
          rewrite <- PeanoNat.Nat.ltb_lt in *.
          destruct (lookup_i_length _ (n0-n) Hc') as [e0 He0].
          rewrite He0. simpl.
          eapply Forall_lookup_i with (ρ0 := ρ) (P:=fun e1 => iclosed_n n e1 = true);eauto.
          apply Forall_impl with (P:=fun e1 => iclosed_n 0 (snd e1) = true);eauto.
          intros a H. unfold compose. change (iclosed_n (0+n) (snd a) = true); now apply iclosed_m_n.
        * simpl in *.
          rewrite PeanoNat.Nat.ltb_lt in *.
          rewrite Compare_dec.leb_iff_conv in *.
          assumption.
      + (* eLambda *)
        simpl in *.
  Admitted.

  Lemma Forall_impl_inner {A} (P Q : A -> Prop) l :
    Forall P l -> Forall (fun x => P x -> Q x) l ->
    Forall Q l.
  Proof.
    intros HP. induction HP;intros HQ.
    + constructor.
    + constructor.
      pose proof (Forall_inv HQ);easy.
      pose proof (Forall_inv_tail HQ);easy.
  Qed.

  Lemma from_value_closed v n :
    val_ok v  (* this ensures that closures contain closed expressions *) ->
    iclosed_n n ( from_val_i v ) = true.
  Proof.
    intros Hv.
    induction v using val_ind_full.
    + simpl. apply vars_to_apps_iclosed_n. inversion Hv;subst.
      eapply Forall_impl_inner;easy.
    + inversion Hv;subst.
  Admitted.


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

  Lemma subst_env_i_empty :
    forall (e : expr) (k : nat), e = subst_env_i_aux k [] e.
  Proof.
    intros e.
    induction e using expr_ind_case;intros k;simpl in *;try easy; try congruence.
    + destruct (n-k);destruct (Nat.leb k n); easy.
    + f_equal;auto.
    rewrite <- map_id at 1.
    eapply @Induction.forall_map_spec.
    eapply H.
    intros x f. destruct x;simpl in *. f_equal. apply f.
  Qed.

  (* Lemma subst_env_i_rec n1 n2 e1 t1 t2 : *)
  (*   forall (e : expr) (k : nat), e = subst_env_i_aux k (enRec n1 n2 e1 t1 t2 enEmpty) e. *)
  (* Proof. *)
  (*   intros e. *)
  (*   induction e using expr_ind_case;intros k;simpl in *;try easy; try congruence. *)
  (*   + destruct (Nat.leb k n); destruct k; try easy. *)
  (*   + f_equal;auto. *)
  (*   rewrite <- map_id at 1. *)
  (*   eapply @Induction.forall_map_spec. *)
  (*   eapply H. *)
  (*   intros x f. destruct x;simpl in *. f_equal. apply f. *)
  (* Qed. *)

  (* For simplicity, we consider only constructors of arity 0 and 1 *)
  Inductive accepted_val : val -> Prop :=
  | avContsr0 : forall i nm v, accepted_val v -> accepted_val (vConstr i nm [])
  | avContsr1 : forall i nm v, accepted_val v -> accepted_val (vConstr i nm [v])
  | avClos : forall ρ nm cm ty1 ty2 e, accepted_val (vClos ρ nm cm ty1 ty2 e).

  Lemma expr_eval_econstr {n nm Σ ρ i v mode} :
    expr_eval_general n mode Σ ρ (eConstr i nm) = Ok v ->
    v = vConstr i nm [].
  Proof.
    destruct mode;  intros H; destruct n;inversion H;reflexivity.
  Qed.

  Import InterpreterEnvList.Equivalence.

  (** Correctness of the value-back-to-expression transformation *)
  (* A creterion of correctness we consider the property that
     if we start with a value [v1], the output of [from_val v1] after evaluation,
     should give as some [v2] equivalent to [v1].
     Note that we cannot ask [v1] and [v2] to be equal,
     instead we ask for equivalence. This is due to substitutions of the
     values in the environment while converting closures back to expressions *)

  Lemma from_val_debruijn_correct n Σ v1 v2 :
    accepted_val v1 ->
    expr_eval_i n Σ [] (from_val_i v1) = Ok v2 ->
    v1 ≈ v2.
  Proof.
    intros Hav He.
    revert dependent n.
    revert dependent v2.
    induction v1 using val_ind_full;intros v2 n0 H1.
    + destruct n0;tryfalse.
      inversion Hav;subst.
      * simpl in H1. inversion H1. reflexivity.
      * autounfold with facts in *. simpl in H1.
        remember (expr_eval_general n0 false Σ [] (eConstr i n)) as cv.
        remember (expr_eval_general n0 false Σ [] (from_val_i v)) as fv.
        destruct cv as [cv0 | | ]; try destruct cv0;try destruct c;destruct fv;tryfalse.
        ** inversion H1 as [H1'].
           symmetry in Heqfv.
           apply Forall_inv in H.
           pose proof (H H2 _ _ Heqfv) as HH. subst.
           symmetry in Heqcv.
           pose proof (expr_eval_econstr Heqcv) as HH1. inversion HH1;subst.
           simpl. clear H Heqfv H1.
           (* this rewrite actually uses setoid_rewrite along the ≈ relation *)
           rewrite HH.
           reflexivity.
        ** symmetry in Heqcv.
           pose proof (expr_eval_econstr Heqcv);tryfalse.
        ** symmetry in Heqcv;pose proof (expr_eval_econstr Heqcv);tryfalse.
    + simpl in H1.
      destruct cm.
      * destruct n0;tryfalse. simpl in H1.
        inversion_clear H1.
        constructor.
        unfold inst_env_i,subst_env_i;simpl.
           rewrite <- subst_env_i_empty.
        reflexivity.
      * destruct n0;tryfalse. simpl in H1.
        inversion_clear H1.
        constructor.
        intros.
        unfold inst_env_i,subst_env_i;simpl.
        rewrite <- subst_env_i_empty;reflexivity.
  Qed.

End Values.

Section Indexify.

  (* Inductive index_env_ok : list (name * nat) -> env val -> Type := *)
  (* | iecEmpty : index_env_ok [] enEmpty *)
  (* | iecCons : forall nm a ρ en, *)
  (*     index_env_ok en ρ -> *)
  (*     index_env_ok (nm :: en) (enCons nm a ρ) *)
  (* | iecRec *)

  Lemma indexify_correct n Σ ρ ne v1 v2 e :
    expr_eval_n n Σ ρ e = Ok v1 ->
    expr_eval_i n Σ ρ (indexify ne e) = Ok v2 ->
    v1 = v2.
  Proof.
    intros Hn Hi.
    induction e using expr_ind_case;autounfold with facts in *.
    + (* This will be proved trivially if we add an assuption that
         there are no indices in [e] *)
      admit.
    + destruct n;tryfalse. simpl in *.
      destruct (Ast.lookup ne n0) eqn:Heq;tryfalse.
      Admitted.

End Indexify.
