(** * Lemmas about the environment substitutions, closedness, etc. on expressions *)

From MetaCoq.Template Require Import All.
Require Import String List.
Require Import Morphisms Setoid Bool.

From ConCert Require Import CustomTactics Misc MyEnv Ast
     EvalE PCUICTranslate EnvSubst Wf.

Import Basics.
Open Scope program_scope.

Open Scope string_scope.
Import ListNotations.
Import Lia.
Import Nat.

Import NamelessSubst.

Hint Unfold expr_eval_n expr_eval_i : facts.

(** An elimination principle that takes into account nested occurrences of expressions
   in the list of branches for [eCase] *)
Definition expr_elim_case (P : expr -> Type)
           (Hrel    : forall n : nat, P (eRel n))
           (Hvar    : forall n : ename, P (eVar n))
           (Hlam    :forall (n : ename) (t : type) (e : expr), P e -> P (eLambda n t e))
           (HtyLam : forall (n : ename) (e : expr), P e -> P (eTyLam n e))
           (Hletin  : forall (n : ename) (e : expr),
               P e -> forall (t : type) (e0 : expr), P e0 -> P (eLetIn n e t e0))
           (Happ    :forall e : expr, P e -> forall e0 : expr, P e0 -> P (eApp e e0))
           (Hconstr :forall (i : inductive) (n : ename), P (eConstr i n))
           (Hconst  :forall n : ename, P (eConst n))
           (Hcase   : forall p (t : type) (e : expr),
               P e -> forall l : list (pat * expr), All (fun x => P (snd x)) l ->P (eCase p t e l))
           (Hfix    :forall (n n0 : ename) (t t0 : type) (e : expr), P e -> P (eFix n n0 t t0 e))
           (Hty : forall t : type, P (eTy t)) :
  forall e : expr, P e.
Proof.
  refine (fix ind (e : expr) := _ ).
  destruct e.
  + apply Hrel.
  + apply Hvar.
  + apply Hlam. apply ind.
  + apply HtyLam. apply ind.
  + apply Hletin; apply ind.
  + apply Happ;apply ind.
  + apply Hconstr.
  + apply Hconst.
  + apply Hcase. apply ind.
    induction l.
    * constructor.
    * constructor. apply ind. apply IHl.
  + apply Hfix. apply ind.
  + apply Hty.
Defined.


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
        forall (i : inductive) (n0 : ename) (l : list val) (n : nat),
          All (fun v : val => iclosed_n n (of_val_i v) = true) l ->
          iclosed_n n (vars_to_apps (eConstr i n0) (map of_val_i l)) = true.
  Proof.
    intros i n0 l n H.
    induction l using rev_ind.
    + reflexivity.
    + rewrite map_app. simpl. rewrite vars_to_apps_unfold.
      simpl. apply All_app in H. destruct H as [H1 H2].
      split_andb.
      * now apply IHl.
      * now inversion H2.
  Qed.

  (* Lemma Forall_lookup_i {A} ρ n e (P : A -> Prop) : *)
  (*   ForallEnv P ρ -> lookup_i ρ n = Some e -> P e. *)
  (* Proof. *)
  (*   intros Hfe Hl. *)
  (*   revert dependent n. *)
  (*   induction Hfe;intros n Hl. *)
  (*   + inversion Hl. *)
  (*   + simpl in *. destruct x; destruct (Nat.eqb n 0);inversion Hl;subst;eauto. *)
  (* Qed. *)

  Lemma All_lookup_i {A} ρ n e (P : A -> Type) :
    AllEnv P ρ -> lookup_i ρ n = Some e -> P e.
  Proof.
    intros Hfe Hl.
    revert dependent n.
    induction Hfe;intros n Hl.
    + inversion Hl.
    + simpl in *. destruct x; destruct (Nat.eqb n 0);inversion Hl;subst;eauto.
  Qed.


  Lemma iclosed_ty_geq ty : forall n m, m >= n -> iclosed_ty n ty = true -> iclosed_ty m ty = true.
  Proof.
    induction ty;intros n1 m1 H Hc;eauto.
    + simpl in *. assert (S m1 >= S n1) by lia. eapply IHty;eauto.
    + simpl in *. inv_andb Hc. split_andb; eauto.
    + simpl in *. leb_ltb_to_prop;lia.
    + simpl in *. inv_andb Hc. split_andb; eauto.
  Qed.

  Lemma iclosed_ty_m_n ty : forall n m, iclosed_ty n ty = true -> iclosed_ty (n+m) ty = true.
  Proof.
    intros n m H.
    eapply iclosed_ty_geq with (n := n);eauto. lia.
  Qed.

  Lemma iclosed_ty_0 ty : forall n, iclosed_ty 0 ty = true -> iclosed_ty n ty = true.
  Proof. apply iclosed_ty_m_n. Qed.

  Lemma iclosed_n_geq e : forall n m, m >= n -> iclosed_n n e = true -> iclosed_n m e = true.
  Proof.
    induction e using expr_elim_case; intros n1 m1 Hgeq H1;try inversion H1;auto.
    + simpl in *. rewrite H1.
      leb_ltb_to_prop;lia.
    + simpl in *. rewrite H1. inv_andb H1.
      split_andb;auto. apply iclosed_ty_geq with (n:=n1);auto;lia. eapply IHe with (n:=S n1);auto; lia.
    + simpl in *. rewrite H1. eapply IHe with (n:=S n1);auto; lia.
    + simpl in *. repeat rewrite Bool.andb_true_iff in *.
      clear H0. destruct H1 as [[Ht He1] He2].
      rewrite He1, He2, Ht. simpl.
      repeat split_andb.
      apply iclosed_ty_geq with (n:=n1);auto;lia.
      eapply IHe1;eauto. eapply IHe2 with (n:= S n1);eauto;lia.
    + simpl in *. rewrite Bool.andb_true_iff in *. destruct H1 as [He1 He2].
      rewrite He1, He2. simpl.
      split_andb;eauto.
    + simpl in *. repeat rewrite Bool.andb_true_iff in *.
      destruct H1 as [[[Hp Ht] He1] Hforall]. rewrite Hp,Ht,He1,Hforall.
      repeat split_andb.
      eapply forallb_impl_inner;try eapply Hp;intros;
        apply iclosed_ty_geq with (n:=n1);auto;lia.
      apply iclosed_ty_geq with (n:=n1);auto;lia.
      erewrite IHe;eauto.
      apply All_forallb.
      apply forallb_All in Hforall.
      apply All_impl_inner with (P:= fun x => iclosed_n (#|pVars (fst x)|+n1) (snd x) = true).
      assumption.
      eapply All_impl. apply H.
      intros. simpl in *.
      eapply H0 with (n:=#|pVars x.1| + n1). lia. easy.
    + simpl in *. rewrite H1. repeat rewrite Bool.andb_true_iff in *. intuition.
      repeat split_andb;eauto with facts.
      eapply iclosed_ty_geq with (n:=n1);eauto.
      eapply iclosed_ty_geq with (n:=n1);eauto.
      eapply IHe with (n:=S (S n1));eauto;lia.
    + simpl. rewrite H0. apply iclosed_ty_geq with (n:=n1);auto;lia.
  Qed.

  Lemma iclosed_m_n e : forall n m, iclosed_n n e = true -> iclosed_n (n+m) e = true.
  Proof.
    intros n m H.
    eapply iclosed_n_geq with (n := n);eauto. lia.
  Qed.

  Lemma iclosed_n_0 e : forall n, iclosed_n 0 e = true -> iclosed_n n e = true.
  Proof. apply iclosed_m_n. Qed.

  Hint Resolve iclosed_ty_m_n iclosed_ty_0 iclosed_m_n iclosed_n_0 : facts.

  Hint Unfold is_true.

  Lemma iclosed_ty_env_ok n ρ ty : iclosed_ty n ty -> ty_env_ok n ρ ty.
  Proof.
    revert n ρ.
    induction ty;intros n0 ρ Hc;eauto.
    + simpl in *. inv_andb Hc. split_andb;intuition.
    + simpl in *.  assert (n0 <=? n = false) by (unfold is_true in *; leb_ltb_to_prop;lia).
      now rewrite H.
    + simpl in *. inv_andb Hc. split_andb;intuition.
  Qed.

  Lemma subst_env_i_ty_closed :
    forall (ty : type) (n : nat) (ρ : env expr),
      ty_env_ok n ρ ty ->
      AllEnv (iclosed_n 0) ρ ->
      iclosed_ty (n + #|ρ|) ty = true -> iclosed_ty n (subst_env_i_ty n ρ ty) = true.
  Proof.
    intros ty.
    induction ty;intros n1 ρ Hok Henv Hc;auto.
    + simpl in *. eapply IHty;eauto.
    + simpl in *. inv_andb Hok;inv_andb Hc;split_andb;auto.
    + simpl in *. destruct (n1 <=? n) eqn:Hnle.
      * leb_ltb_to_prop.
        assert (Hc' : n-n1 < length ρ) by lia.
        rewrite <- PeanoNat.Nat.ltb_lt in *. unfold lookup_ty.
        destruct (lookup_i_length _ (n-n1) Hc') as [e0 He0].
        rewrite He0 in *. simpl. destruct e0;tryfalse.
        simpl in *. assert (H : iclosed_n 0 (eTy t)) by (eapply (All_lookup_i _ _ _ _ Henv);eauto).
        simpl in *. eauto with facts.
      * simpl in *. leb_ltb_to_prop. assumption.
    + simpl in *. inv_andb Hok;inv_andb Hc;split_andb;auto.
  Qed.

  Lemma subst_env_i_ty_closed_inv :
    forall (ty : type) (n : nat) (ρ : env expr),
      AllEnv (iclosed_n 0) ρ ->
      iclosed_ty n (subst_env_i_ty n ρ ty) = true ->
      iclosed_ty (n + #|ρ|) ty = true.
  Proof.
    intros ty.
    induction ty;intros n1 ρ Henv Hc;auto.
    + simpl in *. replace (S (n1 + #|ρ|)) with (S n1 + #|ρ|) by lia. eapply IHty;eauto.
    + simpl in *. inv_andb Hc;split_andb;auto.
    + simpl in *.
      destruct (n1 <=? n) eqn:Hnle.
      * destruct (n <? n1 + #|ρ|) eqn:Hn;auto.
        leb_ltb_to_prop.
        assert (Hnk : #|ρ| <= n - n1) by lia.
        rewrite <- PeanoNat.Nat.ltb_ge in *.
        specialize (lookup_i_length_false _ _  Hnk) as HH.
        unfold lookup_ty in *.
        rewrite HH in *;simpl in *;tryfalse.
      * simpl in *. leb_ltb_to_prop. lia.
    + simpl in *. inv_andb Hc;split_andb;auto.
  Qed.

  Hint Resolve subst_env_i_ty_closed subst_env_i_ty_closed_inv iclosed_ty_env_ok : facts.

  Lemma subst_env_iclosed_n (e : expr) :
    forall n (ρ : env expr),
      ty_expr_env_ok ρ n e ->
      All (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n (n + #|ρ|) e = true -> iclosed_n n (e.[ρ]n) = true.
  Proof.
    induction e using expr_elim_case;intros n1 ρ Hok Hc Hec;
        simpl in *;try inv_andb Hok;try inv_andb Hec;try split_andb;tryfalse;auto with facts.
      + (* eRel *)
        unfold subst_env_i. simpl.
        simpl in *.
        destruct (n1 <=? n) eqn:Hnle.
        * leb_ltb_to_prop.
          assert (Hc' : n-n1 < length ρ) by lia.
          rewrite <- PeanoNat.Nat.ltb_lt in *.
          destruct (lookup_i_length _ (n-n1) Hc') as [e0 He0].
          rewrite He0. simpl.
          eapply All_lookup_i with (ρ0 := ρ) (P:=fun e1 => iclosed_n n1 e1 = true);eauto.
          apply (All_impl (P:=fun e1 => iclosed_n 0 (snd e1) = true));eauto.
          intros a H. unfold compose. change (iclosed_n (0+n1) (snd a) = true); now apply iclosed_m_n.
        * simpl in *. leb_ltb_to_prop. assumption.
      + inv_andb H1. inv_andb H. split_andb;auto with facts.
      + repeat inv_andb H0. repeat inv_andb H2.
        destruct p as [ind tys]. simpl in *.
        apply forallb_All in H3 as Hall3.
        apply forallb_All in H1 as Hall1.
        apply forallb_All in H0 as Hall0.
        apply forallb_All in H2 as Hall2.
        specialize (All_mix Hall0 Hall2) as Hall'. simpl in *.
        specialize (All_mix Hall3 Hall1) as Hall. simpl in *.
        repeat split_andb;eauto with facts.
        apply All_forallb. apply All_map. unfold compose. simpl.
        eapply All_impl_inner. apply Hall'. simpl in *.
        apply Forall_All.
        eapply Forall_forall;
          intros;eapply subst_env_i_ty_closed;intuition.
        apply All_forallb. apply All_map. unfold compose. simpl.
        eapply All_impl_inner. apply Hall. simpl in *.
        eapply All_impl. apply H. intros. simpl in *.
        rewrite PeanoNat.Nat.add_assoc in *.
        eapply H8;intuition;auto with facts.
      + inv_andb H. inv_andb H1. split_andb.
        eapply subst_env_i_ty_closed;eauto with facts. intuition.
  Qed.

  Lemma subst_env_iclosed_n_inv (e : expr) :
    forall n (ρ : env expr),
      All (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n n (e.[ρ]n) = true -> iclosed_n (n + #|ρ|) e = true.
  Proof.
    induction e using expr_ind_case;intros k ρ Hc Hec;
      simpl in *;try inv_andb Hec; try split_andb;auto;
        try repeat rewrite <- PeanoNat.Nat.add_succ_l;tryfalse;auto with facts.
    + (* eRel *)
      unfold subst_env_i. simpl.
      simpl in *.
      destruct (k <=? n) eqn:Hnle.
      * destruct (n <? k + #|ρ|) eqn:Hn;auto.
        leb_ltb_to_prop.
        assert (Hnk : #|ρ| <= n - k) by lia.
        rewrite <- PeanoNat.Nat.ltb_ge in *.
        specialize (lookup_i_length_false _ _  Hnk) as HH.
        rewrite HH in Hec;simpl in *;tryfalse.
      * simpl in *. leb_ltb_to_prop. lia.
    + inv_andb H. split_andb;auto with facts.
    + destruct p;simpl in *. inv_andb Hec. repeat inv_andb H0.
      repeat split_andb;auto with facts.
      rewrite forallb_map in H0.
      eapply forallb_impl_inner. eapply H0. intros;simpl.
      eapply subst_env_i_ty_closed_inv;eauto.
    + destruct p;simpl in *. inv_andb Hec. repeat inv_andb H0.
      apply forallb_Forall.
      eapply Forall_forall. intros a Hin.
      rewrite forallb_map in H1. unfold compose in H1;simpl in H1.
      rewrite Forall_forall in H.
      rewrite PeanoNat.Nat.add_assoc.
      assert ( HH : Forall (fun x : pat * expr =>
                              is_true (iclosed_n (#|pVars (fst x)| + k)
                                      ((snd x).[ ρ] (#|pVars (fst x)| + k)))) l) by
           now apply forallb_Forall.
      rewrite Forall_forall in HH. intuition.
    + inv_andb H. split_andb;auto with facts.
  Qed.

  Lemma subst_env_iclosed_0 (e : expr) :
    forall (ρ : env expr),
      ty_expr_env_ok ρ 0 e ->
      All (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n #|ρ| e = true -> iclosed_n 0 (e.[ρ]) = true.
  Proof.
    intros;apply subst_env_iclosed_n with (n:=0);eauto with facts.
  Qed.

  Lemma subst_env_iclosed_0_inv (e : expr) :
    forall (ρ : env expr),
      All (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n 0 (e.[ρ]) = true -> iclosed_n #|ρ| e = true.
  Proof.
    intros;apply subst_env_iclosed_n_inv with (n:=0);eauto.
  Qed.

  Lemma of_value_closed Σ v n :
    val_ok Σ v  (* this ensures that closures contain closed expressions *) ->
    iclosed_n n (of_val_i v ) = true.
  Proof.
    revert n.
    induction v using val_elim_full;intros n1 Hv.
    + simpl. apply vars_to_apps_iclosed_n.
      inversion Hv;subst;clear Hv.
      eapply All_impl_inner. apply X0.
      now eapply (All_impl X).
    + simpl in *. destruct cm.
      * simpl in *. inversion Hv. subst. clear Hv.
        split_andb. eapply iclosed_ty_0.
        eapply subst_env_i_ty_closed;
          auto with facts.
        eapply All_map. eapply (All_impl_inner _ _ _ X0).
        eapply (All_impl X);eauto.
        eapply iclosed_m_n with (n:=1).
        apply subst_env_iclosed_n.
        ** easy.
        ** apply All_map.
           unfold AllEnv,compose,fun_prod in *.
           eapply All_impl_inner. apply X0.
           now eapply (All_impl X).
        ** now rewrite map_length.
      * unfold subst_env_i. simpl in *.
        inversion Hv. subst. repeat split_andb.
        ** eapply iclosed_ty_0.
           eapply subst_env_i_ty_closed;
             auto with facts.
           eapply All_map. eapply (All_impl_inner _ _ _ X0).
           eapply (All_impl X);eauto.
        ** eapply iclosed_ty_0.
           eapply subst_env_i_ty_closed;
             auto with facts.
           eapply All_map. eapply (All_impl_inner _ _ _ X0).
           eapply (All_impl X);eauto.
        ** eapply iclosed_m_n with (n:=2).
           eapply subst_env_iclosed_n.
           *** easy.
           *** apply All_map.
               unfold AllEnv,compose,fun_prod in *.
               eapply All_impl_inner. apply X0.
               now eapply (All_impl X).
           *** now rewrite map_length.
    + simpl. simpl in *.
      inversion Hv. subst. clear Hv.
        eapply iclosed_m_n with (n:=1).
        apply subst_env_iclosed_n.
        ** easy.
        ** apply All_map.
           unfold AllEnv,compose,fun_prod in *.
           eapply All_impl_inner. apply X0. simpl.
           now eapply (All_impl X).
        ** now rewrite map_length.
    + simpl. inversion Hv. subst. eauto with facts.
Qed.


  Lemma subst_env_i_ty_empty k t : t = subst_env_i_ty k [] t.
  Proof.
    revert k.
    induction t;intros;simpl;try f_equal;eauto.
    destruct (k <=? n);auto.
  Qed.


  Hint Resolve subst_env_i_ty_empty.

  Lemma subst_env_i_empty :
    forall (e : expr) (k : nat), e = subst_env_i_aux k [] e.
  Proof.
    intros e.
    induction e using expr_ind_case;simpl in *;intuition.
    + simpl. destruct (Nat.leb k n);eauto.
    + simpl.
      apply f_equal4;eauto with facts.
      rewrite map_id_f;eauto.
      rewrite <- map_id at 1.
      eapply forall_map_spec.
      eapply Forall_impl;eauto. intros p Hp;cbn in *. destruct p; rewrite <-Hp;eauto.
  Qed.

  (* For simplicity, we consider only constructors of arity 0 and 1 *)
  Inductive accepted_val : val -> Prop :=
  | avContsr0 : forall i nm v, accepted_val v -> accepted_val (vConstr i nm [])
  | avContsr1 : forall i nm v, accepted_val v -> accepted_val (vConstr i nm [v])
  | avClos : forall ρ nm cm ty1 ty2 e, accepted_val (vClos ρ nm cm ty1 ty2 e).

  Lemma expr_eval_econstr {n nm Σ ρ i v mode} :
    expr_eval_general mode Σ n ρ (eConstr i nm) = Ok v ->
    v = vConstr i nm [].
  Proof.
    destruct mode; intros H; destruct n;simpl in *;
      destruct (resolve_constr Σ i nm);tryfalse;inversion H;reflexivity.
  Qed.

  Import Equivalence.

  (** Correctness of the value-back-to-expression transformation *)
  (* A creterion of correctness we consider the property that
     if we start with a value [v1], the output of [of_val v1] after evaluation,
     should give as some [v2] equivalent to [v1].
     Note that we cannot ask [v1] and [v2] to be equal,
     instead we ask for equivalence. This is due to substitutions of the
     values in the environment while converting closures back to expressions *)

  Lemma of_val_i_correct n Σ v1 v2 :
    accepted_val v1 ->
    expr_eval_i Σ n [] (of_val_i v1) = Ok v2 ->
    v1 ≈ v2.
  Proof.
    intros Hav He.
    revert dependent n.
    revert dependent v2.
    induction v1 using val_ind_full;intros v2 n0 H1.
    + destruct n0;tryfalse.
      inversion Hav;subst.
      * cbn in H1. destruct (resolve_constr Σ i n);tryfalse. inversion H1. reflexivity.
      * autounfold with facts in *. simpl in H1.
        remember (expr_eval_general false Σ n0 [] (eConstr i n)) as cv.
        remember (expr_eval_general false Σ n0 [] (of_val_i v)) as fv.
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
        **  symmetry in Heqcv;pose proof (expr_eval_econstr Heqcv);tryfalse.
    + simpl in H1.
      destruct cm.
      * destruct n0;tryfalse. simpl in H1.
        destruct (eval_type_i 0 [] ty1);tryfalse.
        inversion_clear H1.
  (*       constructor. *)
  (*       unfold inst_env_i,subst_env_i;simpl. *)
  (*       rewrite <- subst_env_i_empty. *)
  (*       reflexivity. *)
  (*     * destruct n0;tryfalse. simpl in H1. *)
  (*       inversion_clear H1. *)
  (*       constructor. *)
  (*       intros. *)
  (*       unfold inst_env_i,subst_env_i;simpl. *)
  (*       rewrite <- subst_env_i_empty;reflexivity. *)
  (*   + destruct n0;tryfalse. simpl in H1. *)
  (*     inversion_clear H1. *)
  (*     constructor. *)
  (*     unfold inst_env_i,subst_env_i;simpl. *)
  (*     rewrite <- subst_env_i_empty. *)
  (*     reflexivity. *)
  (*   + simpl in *. *)
  (*     destruct n0;simpl in *;tryfalse. *)
  (*     destruct (eval_type_i _ _ _);tryfalse;simpl in *. *)
  (*     now inversion H1. *)
  (* Qed. *)
Admitted.
  End Values.

  Section FindLookupProperties.

  Context {A : Type}
          {B : Type}
          {C : Type}.

  Lemma lookup_ind_nth_error_False (ρ : env A) n m a key :
    lookup_with_ind_rec (1+n+m) ρ key  = Some (n, a) -> False.
  Proof.
    revert dependent m.
    revert dependent n.
    induction ρ as [ |a0 ρ0];intros n m H;tryfalse.
    simpl in *.
    destruct a0;destruct (s =? key).
    + inversion H;lia.
    + replace (S (n + m)) with (n + S m)  in * by lia.
      eauto.
  Qed.

  Lemma lookup_ind_nth_error_shift (ρ : env A) n i a key :
    lookup_with_ind_rec (1+n) ρ key = Some (1+i, a) <->
    lookup_with_ind_rec n ρ key = Some (i, a).
  Proof.
    split;revert dependent i;revert dependent n;
    induction ρ;intros i1 n1 H;tryfalse;simpl in *;
      destruct a0; destruct ( s =? key); inversion H;eauto.
  Qed.

  Lemma lookup_ind_nth_error (ρ : env A) i a key :
    lookup_with_ind ρ key = Some (i,a) -> nth_error ρ i = Some (key,a).
  Proof.
    revert dependent ρ.
    induction i;simpl;intros ρ0 H.
    + destruct ρ0;tryfalse. unfold lookup_with_ind in H. simpl in *.
      destruct p as (nm,a0); destruct (nm =? key) eqn:Heq; try rewrite String.eqb_eq in *;subst.
      inversion H;subst;eauto.
      now apply (lookup_ind_nth_error_False _ 0 0) in H.
    + destruct ρ0;tryfalse. unfold lookup_with_ind in H. simpl in *.
      destruct p as (nm,a0); destruct (nm =? key) eqn:Heq;
        try rewrite String.eqb_eq in *;subst;tryfalse.
      apply IHi. now apply lookup_ind_nth_error_shift.
  Qed.

  Lemma lookup_i_nth_error (ρ : env A) i :
    lookup_i ρ i = option_map snd (nth_error ρ i).
  Proof.
    revert i.
    induction ρ;intros.
    + simpl. now rewrite nth_error_nil.
    + simpl. destruct a. simpl in *.
      destruct i;simpl;auto. now replace (i-0) with i by lia.
  Qed.

  Lemma find_map_eq p1 p2 a (f g : A -> B) (l : list A) :
    find p1 l = Some a -> (forall a, f a = g a) ->
    (forall a, p1 a = p2 (f a)) -> find p2 (map f l) = Some (g a).
  Proof.
    intros Hfind Hfeq Heq.
    induction l as [ | a' l'];tryfalse.
    simpl in *. rewrite <- Heq.
    destruct (p1 a');inversion Hfind;subst;auto.
    now rewrite Hfeq.
  Qed.

  Lemma find_map p1 p2 a (f : A -> B) (l : list A) :
    find p1 l = Some a -> (forall a, p1 a = p2 (f a)) -> find p2 (map f l) = Some (f a).
  Proof.
    intros Hfind Heq. now eapply find_map_eq.
  Qed.

  Lemma find_forallb_map {X Y} {xs : list X} {p0 : X -> bool} {p1 : Y -> bool} {f : X -> Y}:
    forall x : X, find p0 xs = Some x -> forallb p1 (map f xs) = true -> p1 (f x) = true.
  Proof.
    induction xs;intros x Hfnd Hall.
    + easy.
    + simpl in *. destruct (p0 a).
      * inversion Hfnd;subst. now destruct (p1 (f x));tryfalse.
      * destruct (p1 (f a));tryfalse;auto.
  Qed.

  Lemma find_forallb {xs : list A} {p1 : A -> bool} {p}:
    forall x, find p xs = Some x -> forallb p1 xs = true -> p1 x = true.
  Proof.
    intros x Hfnd Hall.
    replace xs with (map id xs) in Hall by apply map_id.
    eapply @find_forallb_map with (f:=id);eauto.
  Qed.

  Lemma find_none_fst {p} (l1 l2 : list (A * B)) :
    map fst l1 = map fst l2 ->
    find (p ∘ fst) l1 = None -> find (p ∘ fst) l2 = None.
  Proof.
    revert dependent l2.
    induction l1 as [ | ab l1'];intros l2 Hmap Hfnd.
    + destruct l2;simpl in *;easy.
    + destruct l2;simpl in *;tryfalse.
      unfold compose,id in *;simpl in *.
      destruct ab as [a b];simpl in *.
      inversion Hmap;subst.
    destruct (p (fst p0));simpl in *;eauto;tryfalse.
  Qed.

End FindLookupProperties.


Section Validate.

  Lemma valid_ty_env_ty_env_ok ρ n ty:
    valid_ty_env n ρ ty -> ty_env_ok n (exprs ρ) ty.
  Proof.
    revert n ρ.
    induction ty;intros;simpl in *;unfold is_true in *;
      repeat rewrite Bool.andb_true_iff in *;intuition;eauto.
    rewrite lookup_i_nth_error. rewrite lookup_i_nth_error in H.
    destruct (n0 <=? n);auto.
    rewrite nth_error_map. destruct (nth_error ρ (n - n0));simpl in *;auto.
    destruct p.2;simpl;auto.
  Qed.

  Hint Resolve valid_ty_env_ty_env_ok : facts.

  Lemma valid_env_ty_expr_env_ok ρ n e:
    valid_env ρ n e -> ty_expr_env_ok (exprs ρ) n e.
  Proof.
    revert n ρ.
    induction e using expr_elim_case;intros;
      simpl in *;unfold is_true in *;repeat rewrite Bool.andb_true_iff in *;intuition;
        try eapply valid_ty_env_ty_env_ok;eauto.
    + destruct p as [ind tys]. simpl in *.
      eapply forallb_impl_inner. eapply H1. intros.
      now eapply valid_ty_env_ty_env_ok.
    + apply All_forallb. apply forallb_All in H2.
      eapply All_impl_inner. apply H2. simpl.
      eapply (All_impl H);eauto.
  Qed.
End Validate.
