(* Various auxillary facts usefull for proving correctness of the translation and the interpreter *)
Require Import MetaCoq.Template.monad_utils MetaCoq.Template.All.
Require Import String List.
Require Import Morphisms Setoid.

Require Import CustomTactics MyEnv Ast EvalE PCUICTranslate.

Import Basics.
Open Scope program_scope.

Open Scope string_scope.
Import ListNotations.
Import Lia.
Import Nat.

Import InterpreterEnvList.

Hint Unfold expr_eval_n expr_eval_i : facts.

Ltac inv_andb H := apply Bool.andb_true_iff in H;destruct H.
Ltac split_andb := apply Bool.andb_true_iff;split.
Ltac leb_ltb_to_prop :=
  try rewrite PeanoNat.Nat.ltb_lt in *;
  try rewrite PeanoNat.Nat.leb_le in *;
  try rewrite PeanoNat.Nat.leb_gt in *;
  try rewrite PeanoNat.Nat.ltb_ge in *.

Ltac prop_to_leb_ltb :=
  try rewrite <- PeanoNat.Nat.ltb_lt in *;
  try rewrite <-PeanoNat.Nat.leb_le in *;
  try rewrite <- PeanoNat.Nat.leb_gt in *;
  try rewrite <- PeanoNat.Nat.ltb_ge in *.


(* An elimination principle that takes into account nested occurrences of expressions
   in the list of branches for [eCase] *)
Definition expr_elim_case (P : expr -> Type)
           (Hrel    : forall n : nat, P (eRel n))
           (Hvar    : forall n : name, P (eVar n))
           (Hlam    :forall (n : name) (t : type) (e : expr), P e -> P (eLambda n t e))
           (Hletin  : forall (n : name) (e : expr),
               P e -> forall (t : type) (e0 : expr), P e0 -> P (eLetIn n e t e0))
           (Happ    :forall e : expr, P e -> forall e0 : expr, P e0 -> P (eApp e e0))
           (Hconstr :forall (i : inductive) (n : name), P (eConstr i n))
           (Hconst  :forall n : name, P (eConst n))
           (Hcase   : forall (p : inductive * nat) (t : type) (e : expr),
               P e -> forall l : list (pat * expr), All (fun x => P (snd x)) l ->P (eCase p t e l))
           (Hfix    :forall (n n0 : name) (t t0 : type) (e : expr), P e -> P (eFix n n0 t t0 e)) :
  forall e : expr, P e.
Proof.
  refine (fix ind (e : expr) := _ ).
  destruct e.
  + apply Hrel.
  + apply Hvar.
  + apply Hlam. apply ind.
  + apply Hletin; apply ind.
  + apply Happ;apply ind.
  + apply Hconstr.
  + apply Hconst.
  + apply Hcase. apply ind.
    induction l.
    * constructor.
    * constructor. apply ind. apply IHl.
  + apply Hfix. apply ind.
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
        forall (i : inductive) (n0 : name) (l : list val) (n : nat),
          All (fun v : val => iclosed_n n (from_val_i v) = true) l ->
          iclosed_n n (vars_to_apps (eConstr i n0) (map from_val_i l)) = true.
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

  Lemma Forall_lookup_i {A} ρ n e (P : A -> Prop) :
    ForallEnv P ρ -> lookup_i ρ n = Some e -> P e.
  Proof.
    intros Hfe Hl.
    revert dependent n.
    induction Hfe;intros n Hl.
    + inversion Hl.
    + simpl in *. destruct x; destruct (Nat.eqb n 0);inversion Hl;subst;eauto.
  Qed.

  Lemma All_lookup_i {A} ρ n e (P : A -> Type) :
    AllEnv P ρ -> lookup_i ρ n = Some e -> P e.
  Proof.
    intros Hfe Hl.
    revert dependent n.
    induction Hfe;intros n Hl.
    + inversion Hl.
    + simpl in *. destruct x; destruct (Nat.eqb n 0);inversion Hl;subst;eauto.
  Qed.


  Lemma lookup_i_length {A} (ρ : env A) n :
    (n <? length ρ) = true -> {e | lookup_i ρ n = Some e}.
  Proof.
    intros H. revert dependent n.
    induction ρ;intros;leb_ltb_to_prop;simpl in *.
    elimtype False. lia.
    destruct a. destruct n.
    + simpl;eauto.
    + simpl. assert (n < #|ρ|) by lia. replace (n-0) with n by lia.
      prop_to_leb_ltb. now apply IHρ.
  Qed.

  Lemma lookup_i_length_false {A} (ρ : env A) n :
    (n <? length ρ) = false -> lookup_i ρ n = None.
  Proof.
    intros H. revert dependent n.
    induction ρ;intros;leb_ltb_to_prop;simpl in *;auto.
    destruct a. destruct n.
    + simpl;eauto. inversion H.
    + simpl. assert (#|ρ| <= n) by lia. replace (n-0) with n by lia.
      rewrite <- PeanoNat.Nat.ltb_ge in *.
      now apply IHρ.
  Qed.

  (* TODO : move to misc *)
  Lemma forallb_Forall_iff {A} (p : A -> bool) (l : list A):
    Forall (fun x => p x = true) l <-> forallb p l = true.
  Proof.
    split.
    + induction l;intros H.
      * reflexivity.
      * simpl. inversion H as [H1 | a1 l1 Heq]. subst. rewrite Heq. easy.
    + induction l;intros H.
      * constructor.
      * simpl in *. rewrite Bool.andb_true_iff in *. destruct H. easy.
  Qed.

  (* TODO : move to misc *)
  Lemma Forall_impl_inner {A} (P Q : A -> Prop) l :
    Forall P l -> Forall (fun x => P x -> Q x) l ->
    Forall Q l.
  Proof.
    intros HP. induction HP;intros HQ.
    + constructor.
    + constructor;inversion HQ;easy.
  Qed.

  (* TODO : move to misc *)
  Lemma All_impl_inner {A} (P Q : A -> Type) l :
    All P l -> All (fun x => P x -> Q x) l ->
    All Q l.
  Proof.
    intros HP. induction HP;intros HQ.
    + constructor.
    + constructor;inversion HQ;easy.
  Qed.

  Lemma iclosed_n_geq e : forall n m, m >= n -> iclosed_n n e = true -> iclosed_n m e = true.
  Proof.
    intros n m.
    revert n m.
    induction e using expr_elim_case; intros n1 m1 Hgeq H1;try inversion H1;auto.
    + simpl in *. rewrite H1.
      leb_ltb_to_prop;lia.
    + simpl in *. rewrite H1. eapply IHe with (n:=S n1);auto; lia.
    + simpl in *. rewrite Bool.andb_true_iff in *. destruct H1 as [He1 He2].
      rewrite He1, He2. simpl.
      split_andb.
      eapply IHe1;eauto. eapply IHe2 with (n:= S n1);eauto;lia.
    + simpl in *. rewrite Bool.andb_true_iff in *. destruct H1 as [He1 He2].
      rewrite He1, He2. simpl.
      split_andb;eauto.
    + simpl in *. rewrite Bool.andb_true_iff in *. destruct H1 as [He1 Hforall].
      f_equal;auto.
      erewrite IHe;eauto.
      rewrite Hforall.
      apply All_forallb.
      apply forallb_All in Hforall.
      apply All_impl_inner with (P:= fun x => iclosed_n (#|pVars (fst x)|+n1) (snd x) = true).
      assumption.
      eapply All_impl. apply H.
      intros. simpl in *.
      eapply H0 with (n:=#|pVars x.1| + n1). lia. easy.
    + simpl in *. rewrite H1. eapply IHe with (n:=S (S n1));eauto;lia.
  Qed.

  Lemma iclosed_m_n e : forall n m, iclosed_n n e = true -> iclosed_n (n+m) e = true.
  Proof.
    intros n m H.
    eapply iclosed_n_geq with (n := n);eauto. lia.
  Qed.

  Lemma iclosed_n_0 e : forall n, iclosed_n 0 e = true -> iclosed_n n e = true.
  Proof. apply iclosed_m_n. Qed.

  Lemma subst_env_iclosed_n (e : expr) :
    forall n (ρ : env expr),
      All (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n (n + #|ρ|) e = true -> iclosed_n n (e.[ρ]n) = true.
  Proof.
    intros n ρ Hc.
    revert dependent ρ;revert dependent n.
    induction e using expr_elim_case;intros n1 ρ Hc Hec;
        simpl in *;try (inv_andb Hec;split_andb;auto);tryfalse;auto.
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
      + apply utils.All_forallb. apply utils.All_map. unfold compose. simpl.
        assert ( H2 : All (fun x : pat * expr =>
                                is_true (iclosed_n ((#|pVars (fst x)|) + (n1 + #|ρ|)) (snd x))) l)
          by now apply utils.forallb_All.
        eapply All_impl_inner. apply H2. simpl in *.
        eapply All_impl. apply H. intros. simpl in *.
        rewrite PeanoNat.Nat.add_assoc in H4.
        eapply H3;eauto.
  Qed.

  Lemma subst_env_iclosed_n_inv (e : expr) :
    forall n (ρ : env expr),
      All (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n n (e.[ρ]n) = true -> iclosed_n (n + #|ρ|) e = true.
  Proof.
    induction e using expr_ind_case;intros k ρ Hc Hec;
      simpl in *;try (inv_andb Hec;split_andb;auto);
        try repeat rewrite <- PeanoNat.Nat.add_succ_l;tryfalse;auto.
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
    + apply utils.forallb_Forall.
      eapply Forall_forall. intros a Hin.
      rewrite forallb_map in H1. unfold compose in H1;simpl in H1.
      rewrite Forall_forall in H.
      rewrite PeanoNat.Nat.add_assoc.
      assert ( H2 : Forall (fun x : pat * expr =>
                              is_true (iclosed_n (#|pVars (fst x)| + k)
                                      ((snd x).[ ρ] (#|pVars (fst x)| + k)))) l) by
           now apply utils.forallb_Forall.
        rewrite Forall_forall in H2.
        apply H;auto. now apply H2.
  Qed.

  Lemma subst_env_iclosed_0 (e : expr) :
    forall (ρ : env expr),
      All (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n #|ρ| e = true -> iclosed_n 0 (e.[ρ]) = true.
  Proof.
    intros;apply subst_env_iclosed_n with (n:=0);eauto.
  Qed.

  Lemma subst_env_iclosed_0_inv (e : expr) :
    forall (ρ : env expr),
      All (fun e => iclosed_n 0 (snd e) = true) ρ ->
      iclosed_n 0 (e.[ρ]) = true -> iclosed_n #|ρ| e = true.
  Proof.
    intros;apply subst_env_iclosed_n_inv with (n:=0);eauto.
  Qed.

  Lemma from_value_closed Σ v n :
    val_ok Σ v  (* this ensures that closures contain closed expressions *) ->
    iclosed_n n ( from_val_i v ) = true.
  Proof.
    revert n.
    induction v using val_elim_full;intros n1 Hv.
    + simpl. apply vars_to_apps_iclosed_n.
      inversion Hv;subst;clear Hv.
      eapply All_impl_inner. apply X0.
      now eapply (All_impl X).
    + simpl in *. destruct cm.
      * simpl in *. inversion Hv. subst. clear Hv.
        eapply iclosed_m_n with (n:=1).
        apply subst_env_iclosed_n.
        ** apply All_map.
           unfold AllEnv,compose,fun_prod in *.
           eapply All_impl_inner. apply X0.
           now eapply (All_impl X).
        ** now rewrite map_length.
      * unfold subst_env_i. simpl in *.
        inversion Hv. subst.
        eapply iclosed_m_n with (n:=2).
        apply subst_env_iclosed_n.
        ** apply All_map. unfold compose in *.
           eapply All_impl_inner. apply X0.
           now eapply (All_impl X).
        ** now rewrite map_length.
Qed.


  Lemma subst_env_empty :
    forall e : expr, e = subst_env [] e.
  Proof.
    intros e.
    induction e using expr_ind_case; simpl; try easy; try congruence.
    f_equal;auto.
    rewrite <- map_id at 1.
    eapply forall_map_spec.
    eapply Forall_impl;eauto. intros a f; destruct a;simpl in *;easy.
  Qed.

  Lemma subst_env_i_empty :
    forall (e : expr) (k : nat), e = subst_env_i_aux k [] e.
  Proof.
    intros e.
    induction e using expr_ind_case;intros k;simpl in *;try easy; try congruence.
    + destruct (n-k);destruct (Nat.leb k n); easy.
    + f_equal;auto.
    rewrite <- map_id at 1.
    eapply forall_map_spec.
    eapply Forall_impl;eauto. intros a f; destruct a;simpl in *;easy.
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
    destruct mode; intros H; destruct n;simpl in *;
      destruct (resolve_constr Σ i nm);tryfalse;inversion H;reflexivity.
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
      * cbn in H1. destruct (resolve_constr Σ i n);tryfalse. inversion H1. reflexivity.
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
