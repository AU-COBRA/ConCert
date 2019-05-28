(* Proof of correctness of the translation from core language expression to the Template Coq terms *)
From Template Require Import utils.

Require Import PeanoNat.

Require PCUIC.PCUICWcbvEval.
From PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping PCUICClosed
     PCUICLiftSubst.

Require Import String List Basics.

Require Import CustomTactics MyEnv Ast EvalE PCUICFacts PCUICTranslate.

Import InterpreterEnvList.
Notation "'eval' ( n , Σ , ρ , e )"  := (expr_eval_i n Σ ρ e) (at level 100).

Notation "M { j := N }" := (subst (N :: nil) j M) (at level 10, right associativity).

Import ListNotations.
Open Scope list_scope.

Import Lia.

Module P := PCUICAst.
Module Pcbv := PCUICWcbvEval.

Notation "Σ ;;; Γ |- t1 ⇓ t2 " := (Pcbv.eval Σ Γ t1 t2) (at level 50).
Notation "T⟦ e ⟧ Σ " := (expr_to_pcuic Σ e) (at level 49).

Tactic Notation "simpl_vars_to_apps" "in" ident(H) :=
  simpl in H;try rewrite map_app in H; simpl in H;
  rewrite vars_to_apps_unfold in H;simpl in H.

Tactic Notation "simpl_vars_to_apps" :=
  simpl;try rewrite map_app; simpl; rewrite vars_to_apps_unfold;simpl.


Notation exprs := (map (fun x => (fst x, from_val_i (snd x)))).

Lemma from_option_indep {A} (o : option A) d  d' v :
  o = Some v -> from_option o d = from_option o d'.
Proof.
  intros;subst;easy.
Qed.

Lemma lookup_i_from_val_env ρ n v :
  lookup_i ρ n = Some v -> lookup_i (exprs ρ) n = Some (from_val_i v).
Proof.
  revert dependent n.
  induction ρ;intros n0 Hρ.
  + easy.
  + destruct a;simpl in *.
    destruct n0.
    * simpl in *. inversion Hρ. subst. reflexivity.
    * simpl in *. replace (n0 - 0) with n0 in * by lia. easy.
Qed.

Lemma inst_env_i_in (ρ : env val) n :
  n < length ρ ->
  exists v, lookup_i ρ n = Some v /\ (eRel n).[exprs ρ] = from_val_i v.
Proof.
  intros Hlt.
  revert dependent n.
  induction ρ;intros n1 Hlt.
  + inversion Hlt.
  + destruct (Nat.eqb n1 0) eqn:Hn1.
    * destruct a. eexists. split.
      ** simpl. rewrite Hn1.
         reflexivity.
      ** simpl in *. unfold inst_env_i,subst_env_i. simpl.
         assert (n1=0) by (apply EqNat.beq_nat_eq; easy).
         subst. simpl. reflexivity.
    * destruct a.
      assert (Hn2 : exists n2, n1 = S n2) by (destruct n1 as [ | n2]; tryfalse; exists n2; reflexivity).
      destruct Hn2 as [n2 Heq_n2]. replace (n1-1) with n2 by lia. subst. simpl in Hlt.
      apply Lt.lt_S_n in Hlt.
      specialize (IHρ _ Hlt). destruct IHρ as [v1 HH]. destruct HH as [H1 H2].
      exists v1. split.
      ** simpl in *. replace (n2 - 0) with n2 by lia. assumption.
      ** assert (Hltb : n2 <? #|ρ| = true) by now apply PeanoNat.Nat.ltb_lt.
        specialize (lookup_i_length _ _ Hltb) as Hlookup.
         destruct Hlookup.
         simpl in *. unfold inst_env_i,subst_env_i in *. simpl in *.
         rewrite <- H2. replace (n2 - 0) with n2 by lia.
         apply lookup_i_from_val_env in H.
         now eapply from_option_indep.
Qed.

Definition is_app (e : expr) : bool :=
  match e with
  | eApp _ _ => true
  | _ => false
  end.


Lemma mkApps_vars_to_apps l: forall (Σ : global_env) e,
    P.mkApps (T⟦e⟧Σ) (map (expr_to_pcuic Σ) l) =
    T⟦ vars_to_apps e l ⟧ Σ.
Proof.
  induction l;intros.
  + reflexivity.
  + simpl. now rewrite <- IHl.
Qed.


Lemma mkApps_vars_to_apps_constr :
  forall (Σ1 : global_env) (i0 : Ast.inductive) (n1 : Ast.name) (l0 : list val) ci,
    resolve_constr Σ1 i0 n1 = Some ci ->
    mkApps (tConstruct (BasicAst.mkInd i0 0) (fst ci) []) (map (fun x => T⟦from_val_i x⟧ Σ1) l0) =
    T⟦ vars_to_apps (eConstr i0 n1) (map from_val_i l0) ⟧ Σ1.
Proof.
  intros Σ1 i0 n1 l0 ci Hci.
  rewrite <- mkApps_vars_to_apps.
  simpl. rewrite Hci. f_equal. rewrite map_map. reflexivity.
Qed.

Lemma Wcbv_value_vars_to_apps Σ :
  forall (i : inductive) (n : name) (l : list val) ci,
    resolve_constr Σ i n = Some ci ->
    Forall (fun v : val => Pcbv.value (T⟦ from_val_i v ⟧ Σ)) l ->
    Pcbv.value (T⟦ vars_to_apps (eConstr i n) (map from_val_i l) ⟧ Σ).
Proof.
  intros i n l ci Hres Hfa.
  erewrite <- mkApps_vars_to_apps_constr;eauto.
  constructor. now apply Forall_map.
Qed.

Open Scope bool.

(* Fixpoint glob_env_ok (Σ : global_env) (e : expr) : bool := *)
(*   match e with *)
(*   | eRel i => true *)
(*   | eVar nm => true *)
(*   | eLambda nm ty b => glob_env_ok Σ b *)
(*   | eLetIn nm e1 ty e2 => (glob_env_ok Σ e1) && (glob_env_ok Σ e2) *)
(*   | eApp e1 e2 => (glob_env_ok Σ e1) && (glob_env_ok Σ e2) *)
(*   | eConstr t i => match (resolve_inductive Σ i) with *)
(*                   | Some _ => true *)
(*                   | _ => false *)
(*                   end *)
(*   | eCase nm_i ty e bs => *)
(*     let res1 := match (resolve_inductive Σ (fst nm_i)) with *)
(*                 | Some _ => true *)
(*                 | _ => false *)
(*                 end *)
(*     in res1 && (forallb ((glob_env_ok  Σ) ∘ snd) bs) *)
(*   | eFix nm vn ty1 ty2 b => *)
(*     glob_env_ok Σ b *)
(*   | eConst _ => true *)
(*   end. *)

Fixpoint ge_val_ok Σ v : bool:=
  match v with
  | vConstr ind ctor args =>
    let res :=
        match (resolve_constr Σ ind ctor) with
                  | Some _ => true
                  | _ => false
        end
    in res && forallb (ge_val_ok Σ) args
  | vClos ρ x0 x1 x2 x3 e => forallb (ge_val_ok Σ ∘ snd) ρ
  end.



Lemma Wcbv_from_value_value v Σ :
  ge_val_ok Σ v ->
  Pcbv.value (T⟦ from_val_i v⟧Σ).
Proof.
  intros Hok.
  induction v using val_ind_full.
  + simpl in *.
    destruct (resolve_constr Σ i n) eqn:Hres;tryfalse.
    unfold is_true in *.
    inv_andb Hok.
    assert (Forall (fun v => ge_val_ok Σ v = true) l) by
        now apply  forallb_Forall.
    eapply Wcbv_value_vars_to_apps;eauto.
    now eapply Forall_impl_inner.
  + destruct cm. constructor. simpl.
    (* fix of Pcbv.eval needed: tFix is a value *)
    admit.
    (* constructor;simpl;auto. *)
Admitted.

Section WcbvEvalProp.

  Lemma All_eq {A} (l1 l2 : list A) : All2 (fun t1 t2 => t1 = t2) l1 l2 -> l1 = l2.
  Proof.
    intros H.
    induction H;f_equal;auto.
  Qed.

  Lemma All_All2_impl {A} (l1 l2 : list A) P :
    All (fun t1 => forall t2, P t1 t2 -> t1 = t2) l1 ->
    All2 P l1 l2 ->
    All2 (fun t1 t2 => t1 = t2) l1 l2.
  Proof.
    intros Hall Hall2.
    induction Hall2;auto.
    inversion Hall as [a | ty ll HH3 HH4];subst;clear Hall.
    constructor;auto.
  Qed.

  Lemma mkApps_unfold t1 ts t2 :
    mkApps t1 (ts ++ [t2]) = tApp (mkApps t1 ts) t2.
  Proof.
    now rewrite <- PCUICAstUtils.mkApps_nested.
  Qed.

  Lemma mkApps_eq_false t1 t2 args :
    t1 <> t2 -> (forall t1' t2' , t2 <> tApp t1' t2') ->
    mkApps t1 args = t2 -> False.
  Proof.
    intros Hneq Hnapp H.
    destruct args using rev_ind;simpl in *;tryfalse.
    rewrite  mkApps_unfold  in H.
    destruct t2;tryfalse.
  Qed.

  Lemma mkApps_tRel_false t args i :
    t <> tRel i ->
    mkApps t args = tRel i -> False.
  Proof.
    intros.
    eapply mkApps_eq_false;eauto. intros ? ? Hi. tryfalse.
  Qed.

  Lemma mkApps_empty t args : mkApps t args = t -> args = [].
  Proof.
    revert t.
    induction args using rev_ind;intros t H;auto.
    rewrite mkApps_unfold in *.
    simpl in *. destruct t;tryfalse. inversion H. simpl in *.
  Admitted.

  Hint Resolve mkApps_tRel_false : facts.

    (* This should from the fact that ⇓ is deterministic and
     the fact that value evaluates to itself, but the fact that
     ⇓ is deterministic is not yet proved in Template Coq *)
  Lemma Wcbv_eval_value_determ Σ t1 t2 :
    Pcbv.value t1 -> Σ ;;; [] |- t1 ⇓ t2 -> t1 = t2.
  Proof.
    intros Hv.
    revert t2.
    induction Hv using Pcbv.value_values_ind;intros t2 He.
    + inversion He;auto;subst; try inversion isdecl.
      exfalso;eapply mkApps_tRel_false;eauto;easy.
      destruct t;inversion H;try (exfalso;eapply mkApps_tRel_false;eauto;easy).
      destruct a;simpl in *;auto. inversion H0.
      inversion isdecl.
      exfalso;eapply mkApps_tRel_false;eauto;easy.
Admitted.
  (*   + simpl in *. inversion He;auto. *)
  (*   + simpl in *. inversion He;auto. *)
  (*   + simpl in *. inversion He;auto. *)
  (*   + simpl in *. *)
  (*     destruct l. *)
  (*     * simpl in *. inversion He;auto. *)
  (*     * simpl in He. *)
  (*       inversion He;subst;simpl in *;try inversion H4;subst;auto. *)
  (*       inversion H0. subst. clear H0. *)
  (*       f_equal. *)
  (*       apply All_eq. destruct l';inversion H6;subst;clear H6. *)
  (*       constructor;auto. *)
  (*       eapply All_All2_impl;eauto. *)
  (*   + destruct l. *)
  (*     * inversion He;subst;reflexivity. *)
  (*     * simpl in *. *)
  (*       inversion H0;subst;clear H0. *)
  (*       inversion He;subst;clear He;try inversion H5;subst;auto. *)
  (*       destruct l';inversion H7;subst. *)
  (*       repeat f_equal. easy. *)
  (*       apply All_eq. *)
  (*       eapply All_All2_impl;eauto. *)
  (*   + destruct t;tryfalse;inversion He;subst;auto. *)
  (* Qed. *)

  (* Lemma closedn_n_m n m t: closedn n t = true -> closedn (m+n) t = true. *)
  (* Proof. *)
  (*   revert n. revert m. *)
  (*   induction t using Induction.term_forall_list_ind;intros n0 m0 H0;auto. *)
  (*   + simpl in *. rewrite PeanoNat.Nat.ltb_lt in *;lia. *)
  (*   + simpl in *. induction l;simpl in *;auto. *)
  (*     rewrite Bool.andb_true_iff in *. destruct H0. *)
  (*     inversion H. subst. auto. *)
  (*   + simpl in *. rewrite Bool.andb_true_iff in *. destruct H0. *)
  (*     split;easy. *)
  (*   + simpl in *. *)
  (*     rewrite Bool.andb_true_iff in *. destruct H0. *)
  (*     rewrite IHt1 by assumption. replace (S (n0 + m0)) with (n0 + S m0) by lia. *)
  (*     rewrite IHt2 by assumption. auto. *)
  (*   + simpl in *. *)
  (*     rewrite Bool.andb_true_iff in *. destruct H0. *)
  (*     rewrite IHt1 by assumption. replace (S (n0 + m0)) with (n0 + S m0) by lia. *)
  (*     rewrite IHt2 by assumption. auto. *)
  (*   + simpl in *. *)
  (*     repeat rewrite Bool.andb_true_iff in *. destruct H0 as [Htmp H]. destruct Htmp. *)
  (*     rewrite IHt1 by assumption. replace (S (n0 + m0)) with (n0 + S m0) by lia. *)
  (*     rewrite IHt2 by assumption. rewrite IHt3 by assumption. *)
  (*     auto. *)
  (*   + simpl in *. rewrite Bool.andb_true_iff in *. *)
  (*     destruct H0. *)
  (*     rewrite forallb_forall in *. *)
  (*     rewrite Forall_forall in *. *)
  (*     auto. *)
  (*   + simpl in *. *)
  (*     repeat rewrite Bool.andb_true_iff in *. destruct H0 as [Htmp H0]. destruct Htmp. *)
  (*     rewrite IHt1 by assumption. replace (S (n0 + m0)) with (n0 + S m0) by lia. *)
  (*     rewrite IHt2 by assumption. unfold tCaseBrsProp in H. *)
  (*     split;auto. apply forallb_Forall_iff. *)
  (*     rewrite <- forallb_Forall_iff in H0. *)
  (*     unfold test_snd in *. *)
  (*     rewrite Forall_forall in *. *)
  (*     intros. easy. *)
  (*   + simpl in *. easy. *)
  (*   + simpl in *. *)
  (*     unfold tFixProp in *. *)
  (*     rewrite <- forallb_Forall_iff in *. *)
  (*     unfold test_def in *. *)
  (*     rewrite Forall_forall in *. *)
  (*     intros x Hx. *)
  (*     specialize (H _ Hx). destruct H as [H1 H2]. *)
  (*     specialize (H0 _ Hx). inv_andb H0. *)
  (*     split_andb; replace (#|m| + (n0 + m0)) with (n0+ (#|m| + m0)) by lia; easy. *)
  (*   + simpl in *. unfold test_def,tFixProp in *. *)
  (*     rewrite forallb_forall in *. *)
  (*     rewrite Forall_forall in *. *)
  (*     intros x Hx. *)
  (*     specialize (H _ Hx). destruct H as [H1 H2]. *)
  (*     specialize (H0 _ Hx). inv_andb H0. *)
  (*     split_andb; replace (#|m| + (n0 + m0)) with (n0+ (#|m| + m0)) by lia; easy. *)
  (* Qed. *)

End WcbvEvalProp.


Lemma type_to_term_closed ty n : closedn n (type_to_term ty) = true.
Proof.
  induction ty;simpl;auto.
  rewrite IHty1. simpl.
  eapply closed_upwards. easy. lia.
Qed.

(* This should follow from the closedness of  [type_to_term ty] but there is no
   theorem about substituting to closed terms (yet) in MetaCoq *)
Lemma type_to_term_subst ty n t : (type_to_term ty) {n:=t} = type_to_term ty.
Proof.
Admitted.

Hint Resolve -> length_zero_iff_nil : hints.
Hint Resolve <- length_zero_iff_nil : hints.
Hint Resolve type_to_term_subst : hints.
Hint Resolve type_to_term_closed : hints.

Lemma closedn_pat_to_lam vs e0 n:
  closedn (#|vs| + n) e0 ->
  closedn n (pat_to_lam vs e0).
Proof.
  revert n.
  induction vs;intros n H.
  + easy.
  + simpl. destruct a. simpl in *.
    apply Bool.andb_true_iff.  split; auto with hints.
    replace (S (#|vs| + n)) with (#|vs| + S n) in * by lia.
    now apply IHvs.
Qed.

Lemma subst_pat_to_lam l t u n:
  (pat_to_lam l t) {n:=u} = pat_to_lam l (t {#|l|+n := u}).
Proof.
  revert dependent n.
  induction l;intros n.
  + simpl. reflexivity.
  + destruct a; simpl. cbn. f_equal. eauto with hints.
    replace (S (#|l| + n)) with (#|l|+S n) by lia.
    apply IHl.
Qed.

Fixpoint nsubst (ts : list term) (n : nat) (t :term) :=
  match ts with
  | [] => t
  | t0 :: ts0 => nsubst ts0 (n-1) (subst [t0] n t)
  end.

Parameter a0 : term.
Parameter a1 : term.
Parameter a2 : term.
Parameter t : term.

Eval simpl in nsubst [a0;a1;a2] 2 t.


Lemma pat_to_lam_app l args t v Σ (Γ:=[]) :
  Forall Pcbv.value args ->
  #|l| = #|args| ->
  Σ ;;; Γ |- mkApps (pat_to_lam l t) args ⇓ v ->
  Σ ;;; Γ |- nsubst args (#|l| - 1) t ⇓ v.
Proof.
  revert args. revert t.
  induction l using rev_ind; intros t0 args Hval Heq He.
  + simpl in *. destruct args;tryfalse. simpl in *. easy.
  + simpl in *.
    destruct args as [ | a0 args0];tryfalse. inversion Heq. clear Heq.
    simpl in *. replace (#|l| - 0) with (#|l|) by lia.
    simpl in *.
    (* inversion He try inversion H3;subst;tryfalse. *)
    (* rewrite subst_pat_to_lam in *. *)
    (* replace (#|l| + 0) with (#|l|) in * by lia. *)
    (* inversion Hval. subst. clear Hval. *)
    (* assert (a0=a') by now eapply Wcbv_eval_value_determ. *)
    (* subst. now apply IHl. *)
Admitted.


Lemma closed_mkApps n t1 t2 :
  closedn n (mkApps t1 [t2]) = true <->
  closedn n t1 = true /\ closedn n t2 = true.
Proof.
  split.
  + intros Hc.
    apply Bool.andb_true_iff.
    specialize (closedn_mkApps_inv n t1 [t2]) as H. simpl in H.
    rewrite Bool.andb_true_r in *. easy.
  + intros Hc.
    destruct Hc.
    apply closedn_mkApps;auto. simpl. rewrite Bool.andb_true_r in *. easy.
Qed.

Hint Resolve <- closed_mkApps : hints.
Hint Resolve -> closed_mkApps : hints.

Lemma expr_closed_term_closed e n Σ:
  iclosed_n n e = true -> closedn n (T⟦e⟧Σ) = true.
Proof.
  revert n.
  induction e using expr_ind_case;intros n1 Hc;auto.
  + (* eLambda*)
    simpl in *. rewrite Bool.andb_true_iff.
    auto with hints.
  + (* eLetIn *)
    simpl in *. repeat rewrite Bool.andb_true_iff in *.
    destruct Hc. auto with hints.
  + (* eApp *)
    simpl in Hc. repeat rewrite Bool.andb_true_iff in *.
    cbn -[mkApps]. eauto with hints. apply <- closed_mkApps. destruct Hc. easy.
  + (* eConstr *)
    simpl in *. destruct (resolve_constr Σ i n); auto.
  + (* eCase *)
    destruct p. simpl in *. repeat rewrite Bool.andb_true_iff in *.
    destruct Hc.
    repeat split;auto with hints.
    destruct (resolve_inductive Σ i) eqn:Hres;auto.
    simpl. rewrite forallb_map. unfold Basics.compose,test_snd,trans_branch.
    apply forallb_Forall. apply Forall_forall. intros x Hin.
    destruct x as [nm tys]. unfold fun_prod,id in *. simpl.
    destruct (find (fun x => _)) as [ p | ] eqn:Hnm;simpl;auto.
    destruct p as [pt e0]. simpl.
    destruct (Nat.eqb #|pVars pt| #|tys|) eqn:Hlen;auto.
    apply find_some in Hnm. destruct Hnm as [Hin' Heqs].
    rewrite Forall_forall in H.
    change
      (forallb (fun x : pat * expr => iclosed_n (#|pVars (fst x)| + n1) (snd x)) l = true)
      with (is_true (forallb (fun x : pat * expr => iclosed_n (#|pVars (fst x)| + n1) (snd x)) l)) in H1.
    rewrite <- forallb_Forall in H1.
    rewrite Forall_forall in H1.
    rewrite in_map_iff in Hin'.
    destruct Hin' as [x Htmp]. destruct x as [pt1 e1].
    destruct Htmp as [He1 Hin'']. inversion He1;subst;clear He1.

    apply closedn_pat_to_lam. change e1 with (snd (pt, e1)).
    apply H;auto.
    specialize (H1 (pt,e1) Hin''). simpl in *.
    rewrite combine_length.
    rewrite PeanoNat.Nat.eqb_eq in *.
    replace (#|tys|) with (#|pVars pt|) by assumption.
    rewrite PeanoNat.Nat.min_id. easy.
  + simpl. rewrite Bool.andb_true_r in *. unfold PCUICAstUtils.test_def. simpl.
    repeat rewrite Bool.andb_true_iff. repeat split;auto with hints.
Qed.

Lemma closed_exprs_len_iff e n (ρ : env val) :
  iclosed_n (n + #|exprs ρ|) e = true <->
  iclosed_n (n + #|ρ|) e = true.
Proof.
  split.
  intros H. rewrite map_length in H. assumption.
  intros H. rewrite map_length. assumption.
Qed.


Hint Resolve
     PeanoNat.Nat.compare_eq
     Compare_dec.nat_compare_Lt_lt
     Compare_dec.nat_compare_Gt_gt
     Compare_dec.leb_correct_conv
     PeanoNat.Nat.leb_refl : facts.
Hint Resolve
     -> PeanoNat.Nat.ltb_lt : facts.
Hint Resolve
     -> PeanoNat.Nat.leb_le : facts.

Hint Constructors val_ok Forall : hints.
Hint Unfold snd env_ok ForallEnv compose : hints.


Hint Resolve <- subst_env_iclosed_0 subst_env_iclosed_n
                closed_exprs_len_iff : hints.
Hint Resolve -> subst_env_iclosed_0 subst_env_iclosed_n
                                   closed_exprs_len_iff : hints.
Hint Resolve iclosed_n_0 : hints.


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
      destruct a3; destruct ( s =? key); inversion H;eauto.
  Qed.

  Lemma lookup_ind_nth_error (ρ : env A) i a key :
    lookup_with_ind ρ key = Some (i,a) -> nth_error ρ i = Some (key,a).
  Proof.
    revert dependent ρ.
    induction i;simpl;intros ρ0 H.
    + destruct ρ0;tryfalse. unfold lookup_with_ind in H. simpl in *.
      destruct p; destruct (s =? key) eqn:Heq; try rewrite eqb_eq in *;subst.
      inversion H;eauto.
      now apply (lookup_ind_nth_error_False _ 0 0) in H.
    + destruct ρ0;tryfalse. unfold lookup_with_ind in H. simpl in *.
      destruct p; destruct (s =? key) eqn:Heq;
        try rewrite eqb_eq in *;subst;tryfalse.
      apply IHi. now apply lookup_ind_nth_error_shift.
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


Lemma option_to_res_ok {A} (o : option A) s v:
  option_to_res o s = Ok v ->
  o = Some v.
Proof.
  intros H. destruct o. inversion H;auto. tryfalse.
Qed.

Lemma forall_map_spec' :
forall (A B : Type) (P : A -> Prop) (l : list A) (f g : A -> B),
  Forall P l -> (forall x : A, In x l -> P x -> f x = g x) -> map f l = map g l.
Proof.
  induction l;intros f g Hfa Heq;simpl;auto.
  inversion Hfa;subst;clear Hfa.
  f_equal.
  + apply Heq;simpl;auto.
  + eapply IHl;intros;try apply Heq;simpl;auto.
Qed.


Lemma forallb_In_snd {A B} (l : list (A * B)) (p : B -> bool) (a : A * B) :
  forallb (fun x => p (snd x)) l = true -> In a l -> p (snd a) = true.
Proof.
  intros H Hin.
  induction l;tryfalse;simpl in *.
  inv_andb H. destruct Hin;subst;auto.
Qed.

Lemma subst_term_subst_env_rec e e0:
  forall Σ n nm,
  iclosed_n (1+n) e = true ->
  iclosed_n 0 e0 = true ->
  (T⟦e⟧ Σ) {n:=T⟦e0⟧ Σ} =
  (T⟦e.[nil # [nm ~> e0]]n⟧ Σ).
Proof.
  induction e using expr_ind_case;intros Σ n1 nm Hc Hce0.
  + (* eRel *)
    cbn.
    destruct (Nat.compare n1 n) eqn:Hn.
    * assert (n1 = n) by auto with facts.
      subst. simpl in *.
      assert (Hn0: Nat.leb n n = true) by auto with facts.
      rewrite Hn0. replace (n - n) with 0 by lia. simpl.
      assert (closed (T⟦ e0 ⟧ Σ) = true) by now apply expr_closed_term_closed.
      rewrite lift_closed by assumption.
      reflexivity.
    * simpl in *.
      assert (n1 < n) by auto with facts.
      assert (n < S n1) by auto with facts.
      exfalso. lia.
    * simpl in *.
      assert  (n < S n1) by auto with facts.
      assert (n1 > n) by auto with facts.
      assert (Hleb : Nat.leb n1 n = false) by auto with facts.
      rewrite Hleb. reflexivity.
  + (* eVar *)
    reflexivity.
  + (* eLambda *)
    cbn in *.
    rewrite type_to_term_subst.
    destruct Hc.
    now f_equal.
  + (* eLetIn *)
    cbn in *.
    rewrite type_to_term_subst.
    apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
    f_equal;eauto.
  + (* eApp *)
    change ((T⟦ eApp e1 e2 ⟧ Σ)) with ((mkApps (T⟦e1⟧Σ) [T⟦e2⟧Σ])) in *.
    simpl in Hc.
    apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
    cbn -[mkApps].
    rewrite subst_mkApps.
    erewrite IHe1 by eauto. simpl.
    erewrite IHe2 by eauto. reflexivity.
  + (* eConstr *)
    simpl. destruct (resolve_constr Σ i n);auto.
  + (* eConst *)
    reflexivity.
  + (* eCase *)
    cbn in *. destruct p. simpl in *.
    apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
    repeat f_equal.
    * rewrite type_to_term_subst. reflexivity.
    * eapply IHe; eauto.
    * rewrite_all map_map. simpl.
      destruct (resolve_inductive Σ i) eqn:Hres;auto.
      simpl. unfold on_snd.
      apply map_ext.
      intros a. destruct a. unfold on_snd.
      cbn. destruct (find _ _) eqn:Hfnd;simpl.
      ** eapply find_map with
             (p2 := (fun x => pName (fst x) =? n0))
             (f:= fun x => ((fst x), (snd x){#|pVars (fst x)|+n1 := T⟦ e0 ⟧ Σ})) in Hfnd.
         rewrite map_map in Hfnd. simpl in Hfnd. unfold fun_prod,id. simpl.
         assert ( Hmap :
                    (map (fun x => (id (fst x), (T⟦snd x⟧ Σ) {#|pVars (fst x)|+n1 := T⟦e0⟧ Σ})) l) =
                    (map (fun x => (fst x, T⟦snd x .[[(nm,e0)]](#|pVars (fst x)| + n1) ⟧ Σ)) l)).
         { eapply forall_map_spec'. apply H. intros a Hin Ha. f_equal.
           assert (iclosed_n (#|pVars (fst a)| + S n1) (snd a) = true) by
               now eapply forallb_forall with (x:=a) in Hce2.
           apply Ha.
           replace (S (#|pVars (fst a)| + n1)) with
               (#|pVars (fst a)| + S n1) by lia.
           assumption. assumption. }
         rewrite <- Hmap. unfold id in *. rewrite Hfnd. simpl.
         destruct (Nat.eqb #|pVars (fst p)| #|l1|) eqn:Hlen;simpl;auto.
         f_equal. unfold id.  rewrite subst_pat_to_lam.
         repeat f_equal. rewrite PeanoNat.Nat.eqb_eq in Hlen.
         rewrite combine_length. rewrite Hlen. apply PeanoNat.Nat.min_id.
         intros. destruct a;easy.
      ** change (fun x : pat * term => pName (fst x) =? n0) with
                                ((fun x : pat => pName x =? n0) ∘ fst (B:=term)) in *.
         erewrite find_none_fst with (l2:=(map (fun_prod id (expr_to_pcuic Σ)) l));eauto.
         now repeat rewrite map_map.
  + (* eFix *)
    simpl. unfold PCUICAstUtils.map_def. simpl. repeat f_equal;try apply type_to_term_subst.
    easy.
Qed.

Lemma subst_term_subst_env e :
  forall v Σ nm,
  val_ok Σ v ->
  iclosed_n 1 e = true ->
  (T⟦e⟧ Σ) {0:=T⟦ from_val_i v ⟧ Σ} =
  (T⟦e.[nil # [nm ~> from_val_i v]]⟧ Σ).
Proof.
  intros.
  assert (iclosed_n 0 (from_val_i v) = true) by now eapply from_value_closed.
  now apply subst_term_subst_env_rec.
Qed.

Lemma subst_env_i_closed_n_eq :
  forall (e : expr) (n m : nat) (ρ : env expr),
    iclosed_n n e = true ->
    e.[ρ](m+n) = e.
Proof.
  intros e.
  induction e using expr_ind_case;intros n1 m1 ρ Hc;simpl;auto.
  + simpl in *. destruct (Nat.leb (m1 + n1)) eqn:Hmn1; leb_ltb_to_prop;try lia;easy.
  + simpl in *. f_equal. replace (S (m1 + n1)) with (m1 + S n1) by lia. easy.
  + simpl in *. inv_andb Hc. f_equal;replace (S (m1 + n1)) with (m1 + S n1) by lia;easy.
  + simpl in *. inv_andb Hc. f_equal;replace (S (m1 + n1)) with (m1 + S n1) by lia;easy.
  + simpl in *. inv_andb Hc. f_equal. easy.
    transitivity (map id l).
    eapply forall_map_spec';eauto.
    simpl. intros x Hin Hx. destruct x. unfold id. f_equal. simpl in *.
    replace (#|pVars p0| + (m1 + n1)) with (m1 + (#|pVars p0| + n1)) by lia.
    apply Hx. rewrite forallb_forall in *.
    rewrite Forall_forall in *.
    change e0 with (snd (p0,e0)).
    change p0 with (fst (p0,e0)). easy.
    apply map_id.
  + simpl in *. f_equal. replace (S (S (m1 + n1))) with (m1 + S (S n1)) by lia. easy.
Qed.

Lemma subst_env_i_closed_eq :
  forall (e : expr) (n : nat) (ρ : env expr),
    iclosed_n 0 e = true ->
    e.[ρ]n = e.
Proof.
  intros;eapply subst_env_i_closed_n_eq with (m:=0);eauto with hints.
Qed.

Lemma subst_env_compose_1 :
  forall (nm : Ast.name) (e e1: expr) k (ρ : env expr),
    Forall (fun x => iclosed_n 0 (snd x) = true) ρ ->
    iclosed_n 0 e1 = true ->
    e.[ρ # [nm ~> e1]]k =
    (e.[ρ](1+k)).[nil # [nm ~> e1]]k.
Proof.
  intros nm.
  unfold inst_env_i,subst_env_i in *. simpl in *.
  induction e using expr_ind_case;intros e' k ρ Hfc Hc;simpl;auto.
  + simpl. destruct n.
    * reflexivity.
    * destruct (Nat.leb k n) eqn:Hkn.
      ** leb_ltb_to_prop.
         assert (k <= S n) by lia.
         prop_to_leb_ltb. rewrite H.
         leb_ltb_to_prop.
         assert (Hneq : S n - k <> 0) by lia.
         rewrite <- PeanoNat.Nat.eqb_neq in Hneq. rewrite Hneq.
         replace (S n - k - 1) with (n - k) by lia.
         replace (S n - S k) with (n - k) by lia.
         destruct (lookup_i ρ (n-k)) eqn:Hl.
         *** simpl. symmetry. apply subst_env_i_closed_eq.
             eapply (Forall_lookup_i _ _ _ (fun x => iclosed_n 0 x) Hfc Hl).
         *** remember (S n) as m. simpl.
             prop_to_leb_ltb. rewrite H. now rewrite Hneq.
      ** leb_ltb_to_prop.
         assert (HkSn :  S n <= k) by lia.
         case HkSn.
         *** rewrite PeanoNat.Nat.leb_refl. simpl.
             replace (n-n) with 0 by lia. simpl.
             now rewrite PeanoNat.Nat.leb_refl.
         *** intros m Hm. assert (H : S n < S m) by lia.
             rewrite <- PeanoNat.Nat.leb_gt in H. rewrite H.
             remember (S n) as n'. remember (S m) as m'. simpl.
             prop_to_leb_ltb. now rewrite H.
  + f_equal. eapply IHe;eauto.
  + f_equal. eapply IHe1;eauto. eapply IHe2;eauto.
  + f_equal. eapply IHe1;eauto. eapply IHe2;eauto.
  + f_equal. apply IHe;auto.
    rewrite map_map. simpl.
    eapply forall_map_spec;eauto.
    eapply Forall_impl;eauto.
    intros a Ha. simpl in *. f_equal.
    replace (#|pVars (fst a)| + S k) with (S (#|pVars (fst a)| + k)) by lia.
    now apply Ha.
  + f_equal. eapply IHe;eauto.
Qed.

Lemma subst_env_swap_app :
  forall (e: expr) (ρ1 ρ2 : env expr) n,
    Forall (fun x => iclosed_n 0 (snd x) = true) ρ1 ->
    Forall (fun x => iclosed_n 0 (snd x) = true) ρ2 ->
    (e.[ρ1](n+#|ρ2|)).[ρ2]n = e.[ρ2++ρ1]n.
Proof.
  induction ρ2.
  + intros. simpl. symmetry. rewrite <- subst_env_i_empty with (k:=n).
    f_equal. lia.
  + intros. simpl. destruct a.
    inversion H0. subst. clear H0.
    assert (Forall (fun x => iclosed_n 0 (snd x) = true) (ρ2++ρ1))
      by now rewrite Forall_app.
    rewrite subst_env_compose_1 with (ρ := ρ2 ++ ρ1) by auto.
    rewrite subst_env_compose_1 with (k:=n) by auto.
    simpl.
    rewrite <-IHρ2;eauto.
    replace (n + S #|ρ2|) with (S n + #|ρ2|) by lia. reflexivity.
Qed.

(* TODO: this should be an instance of a more general lemma, and
   we will restate this in terms of parallel substitutions *)
Lemma subst_env_compose_2 :
  forall (nm1 nm2 : Ast.name) (e e1 e2: expr) (ρ : env expr),
    Forall (fun x => iclosed_n 0 (snd x) = true) ρ ->
    iclosed_n 0 e1 = true ->
    iclosed_n 0 e2 = true ->
    e.[ρ # [nm1 ~> e1] # [nm2 ~> e2]] =
    (e.[ρ]2).[nil # [nm1 ~> e1] # [nm2 ~> e2]].
Proof.
  intros. change ((nm2, e2) :: (nm1, e1) :: ρ) with ([(nm2, e2);(nm1, e1)] ++ ρ).
  symmetry. eapply subst_env_swap_app;eauto.
Qed.


Lemma subst_term_subst_env_rec_n :
  forall v Σ (l : env expr) e,
  val_ok Σ v ->
  iclosed_n #|l| e = true ->
  Forall (fun x : string * expr => iclosed_n 0 (snd x) = true) l ->
  nsubst (map (fun x => expr_to_pcuic Σ (snd x)) l) (#|l| - 1) (T⟦e⟧ Σ) = (T⟦e.[rev l]⟧ Σ).
Proof.
  intros until l.
  induction l;intros.
  + simpl in *. unfold subst_env_i.
    rewrite <- subst_env_i_empty.
    reflexivity.
  + unfold subst_env_i. destruct a as [nm e0]. simpl in *.
    change (e .[ (nm,e0) :: l] 0) with (e .[l # [nm ~> e0]]).
    inversion H1. subst. clear H1.
    (* rewrite subst_env_compose_1 by assumption. *)
    unfold subst_env_i.
    rewrite subst_term_subst_env_rec with (e:=e)(nm:=nm);eauto. simpl.
    replace ((#|l| - 0 - 1)) with (#|l| - 1) by lia.
    erewrite IHl;eauto. f_equal.
    replace (#|l| - 0) with (#|l|) by lia.
    rewrite <- rev_length.
    eapply subst_env_swap_app;eauto.
    now apply Forall_rev.
    replace (#|l| - 0) with (#|l|) by lia.
    simpl in *. apply subst_env_iclosed_n;simpl;auto.
    replace (#|l| + 1) with (S (#|l|)) by lia. assumption.
    replace (#|l| - 0) with (#|l|) by lia.
    assumption.
Qed.

Import Basics.
Open Scope program_scope.

Lemma pat_match_succeeds {A} cn arity vals brs e (assig : list (Ast.name * A)) :
    match_pat cn arity vals brs = Some (assig, e) ->
    exists p, find (fun x => pName (fst x) =? cn) brs = Some (p,e)
         /\ #|arity| = #|p.(pVars)| /\ #|vals| =  #|p.(pVars)|
         /\ assig = combine p.(pVars) vals.
Proof.
  intros Hpm.
  unfold match_pat in Hpm. simpl in Hpm.
  destruct (find (fun x => pName (fst x) =? cn) brs) eqn:Hfnd;tryfalse.
  destruct p as [p' e0].
  destruct (Nat.eqb #|vals| #|pVars p'|) eqn:Hlength;tryfalse.
  destruct (Nat.eqb #|vals| #|arity|) eqn:Hlength';tryfalse.
  simpl in *.
  inversion Hpm. subst. clear Hpm.
  exists p'. rewrite PeanoNat.Nat.eqb_eq in *. easy.
Qed.

Lemma Forall_snd_combine {A B} (l1 : list A) (l2 : list B)
      (p : B -> Prop) : Forall p l2 -> Forall (p ∘ snd) (combine l1 l2).
Proof.
  revert l1.
  induction l2; intros ns H.
  + destruct ns;simpl;constructor.
  + inversion H. subst. destruct ns;unfold compose;simpl. constructor.
    constructor; unfold compose;simpl;auto.
Qed.

Lemma Forall_env_ok (ρ : env val) (l : list val) (ns : list name) Σ :
  Forall (val_ok Σ) l -> env_ok Σ (combine ns l).
Proof.
  apply Forall_snd_combine.
Qed.


Lemma eval_ge_val_ok n ρ Σ e v :
  ForallEnv (ge_val_ok Σ) ρ ->
  expr_eval_i n Σ ρ e = Ok v ->
  ge_val_ok Σ v.
Proof.
  revert dependent ρ. revert dependent v. revert dependent e.
  induction n;intros e v ρ Hok He;tryfalse.
  destruct e;unfold expr_eval_i in *;simpl in *;inversion He;tryfalse.
  + destruct (lookup_i ρ n0) eqn:Hlook;simpl in *;inversion He;subst.
    now eapply Forall_lookup_i with (e:=v).
  + simpl in *. now apply forallb_Forall.
  + destruct (expr_eval_general n _) eqn:He1;tryfalse.
    assert (ge_val_ok Σ v0) by now eapply IHn.
    eapply IHn with (e:=e2) (ρ:=(n0, v0) :: ρ);eauto with hints.
  + destruct (expr_eval_general n false Σ ρ e1) eqn:He1;tryfalse.
      2 : { try (destruct (expr_eval_general n false Σ ρ e2) eqn:He2);tryfalse. }
    destruct v0;try destruct c;
        destruct (expr_eval_general n false Σ ρ e2) eqn:He2;tryfalse.
    * inversion He;subst;clear He. simpl.
      assert (ge_val_ok Σ (vConstr i n0 l)) by eauto.
      assert (ge_val_ok Σ v0) by eauto.
      simpl in *. destruct (resolve_constr Σ i n0);eauto.
      simpl in *. rewrite forallb_app. split_andb;try split_andb;eauto.
    * destruct (expr_eval_general n _ _ _ e0) eqn:He0;tryfalse.
      inversion He;subst.
      assert (ge_val_ok Σ (vClos e n0 cmLam t0 t1 e0)) by eauto.
      assert (ge_val_ok Σ v0) by eauto.
      simpl in *.
      eapply IHn with (ρ:=(n0, v0) :: e);eauto with hints.
      apply forallb_Forall. simpl. now split_andb.
    * destruct (expr_eval_general n _ _ _ e0) eqn:He0;tryfalse.
      inversion He;subst. eapply IHn with (e:=e0); try eapply He0.
      assert (Hok_fix : ge_val_ok Σ (vClos e n0 (cmFix n1) t0 t1 e0)) by eauto.
      assert (ge_val_ok Σ v0) by eauto.
      simpl in Hok_fix. apply forallb_Forall in Hok_fix.
      unfold ForallEnv,compose. eauto with hints.
  + destruct (resolve_constr Σ i n0) eqn:Hres;tryfalse. inversion He.
    simpl. now rewrite Hres.
  +     destruct p as [ind e1]. destruct (expr_eval_general n false Σ ρ e) eqn:He';tryfalse.
    destruct v0;tryfalse. destruct (resolve_constr Σ i n0) eqn:Hres;tryfalse.
    destruct p as [n1 tys]. destruct (string_dec ind i);tryfalse;subst.
    destruct (match_pat n0 tys l0 l) eqn:Hpm;tryfalse. destruct p as [assign e2].
    apply pat_match_succeeds in Hpm. destruct Hpm as [pt Htmp].
    destructs Htmp. subst.
    assert (Hok_constr : ge_val_ok Σ (vConstr i n0 l0)) by now eapply IHn with (e:=e).
    simpl in Hok_constr. destruct (resolve_constr Σ i n0) eqn:Hres';tryfalse.
    assert (Hok_l2 : ForallEnv (fun x => ge_val_ok Σ x = true) (rev (combine (pVars pt) l0))).
    { apply Forall_rev. simpl in Hok_constr. apply forallb_Forall in Hok_constr. simpl in *.
      now apply Forall_snd_combine. }
    eapply IHn with (ρ := (rev (combine (pVars pt) l0) ++ ρ));eauto.
    now apply Forall_app.
  + simpl. now apply forallb_Forall.
Qed.


Lemma env_ok_concat Σ ρ1 ρ2 : env_ok Σ ρ1 -> env_ok Σ ρ2 -> env_ok Σ (ρ1 ++ ρ2).
Proof.
  intros Hok1 Hok2.
  apply Forall_app;split;auto.
Qed.

Lemma rev_env_ok ρ Σ : env_ok Σ ρ -> env_ok Σ (rev ρ).
Proof.
  intros Hok. now apply Forall_rev.
Qed.


Ltac apply_eq H n :=
  match number_to_nat n with
  | 0 => eapply equates_0;[eapply H | ]
  | 1 => eapply equates_1;[eapply H | ]
  | 2 => eapply equates_2;[eapply H | | ]
  | 3 => eapply equates_3;[eapply H | | ]
  | 4 => eapply equates_4;[eapply H | | ]
  end.

Lemma val_ok_ge_val_ok Σ v:
  val_ok Σ v -> ge_val_ok Σ v.
Proof.
  induction v using val_ind_full;intros Hok.
  + simpl. inversion Hok as [H1 | H2 | nm1 ];subst;clear Hok.
    destruct (resolve_constr Σ i n) eqn:Hres;tryfalse.
    inversion H1;subst. simpl in *.
    apply forallb_Forall. eapply Forall_impl_inner;eauto.
  + simpl. apply forallb_Forall.
    inversion Hok;subst;clear Hok; eapply Forall_impl_inner;eauto.
Qed.

Lemma env_ok_ForallEnv_ge_val_ok ρ Σ :
  env_ok Σ ρ -> ForallEnv (ge_val_ok Σ) ρ.
Proof.
  induction ρ.
  + intros. constructor.
  + intros Hok. inversion Hok;subst.
    constructor.
    * now apply val_ok_ge_val_ok.
    * now eapply IHρ.
Qed.

Lemma eval_val_ok n ρ Σ e v :
  env_ok Σ ρ ->
  iclosed_n #|ρ| e ->
  expr_eval_i n Σ ρ e = Ok v ->
  val_ok Σ v.
Proof.
  revert dependent ρ. revert dependent v. revert dependent e.
  induction n;intros e v ρ Hok Hc He;tryfalse.
  destruct e.
  + unfold expr_eval_i in *. simpl in *.
    destruct (lookup_i_length _ _ Hc) as [x Hsome].
    rewrite Hsome in He. simpl in *. inversion He;subst;clear He.
    now eapply Forall_lookup_i.
  + tryfalse.
  + unfold expr_eval_i in *. simpl. simpl in He. inversion_clear He.
    now constructor.
  + unfold expr_eval_i in *. simpl. simpl in He,Hc.
    destruct (expr_eval_general n false Σ ρ e1) eqn:He1;tryfalse.
    unfold is_true in *;inv_andb Hc.
    assert (env_ok Σ ((n0, v0) :: ρ)) by
        (constructor;[eapply IHn;eauto| easy]).
    eapply IHn with (ρ:=ρ # [n0 ~> v0]);eauto.
  + simpl in Hc. inv_andb Hc.
    autounfold with facts in *. simpl in He.
      destruct (expr_eval_general n false Σ ρ e1) eqn:He1;tryfalse.
      2 : { try (destruct (expr_eval_general n false Σ ρ e2) eqn:He2);tryfalse. }
    destruct v0;try destruct c;
        destruct (expr_eval_general n false Σ ρ e2) eqn:He2;tryfalse.
    * inversion_clear He.
      assert (Hge_ok : ge_val_ok Σ (vConstr i n0 l)) by
          (eapply eval_ge_val_ok;[now apply env_ok_ForallEnv_ge_val_ok | eauto]).
      assert (Hok_constr : val_ok Σ (vConstr i n0 l)) by now eapply IHn with (e:=e1).
      simpl in Hge_ok. destruct (resolve_constr Σ i n0) eqn:Hres;tryfalse.
      inversion Hok_constr. subst. clear Hok_constr.
      econstructor;eauto. apply Forall_app;split;eauto.
    * simpl. destruct (expr_eval_general n false Σ ((n0, v0) :: e) e0) eqn:He0;tryfalse.
      inversion He. subst.
      assert (Hok_v0 : val_ok Σ v0) by now eapply IHn.
      assert (Hok_lam : val_ok Σ (vClos e n0 cmLam t0 t1 e0)) by now eapply IHn with (e:=e1).
      inversion Hok_lam. subst. clear Hok_lam.
      eapply IHn with (e:=e0) (ρ:=(n0, v0) :: e);eauto with hints.
    * destruct (expr_eval_general n false Σ _ e0) eqn:He0;tryfalse.
      inversion He;subst;tryfalse.
      assert (Hok_v0 : val_ok Σ v0) by now eapply IHn.
      assert (Hok_fix : val_ok Σ (vClos e n0 (cmFix n1) t0 t1 e0)) by
          now eapply IHn with (ρ:=ρ) (e:=e1).
      inversion Hok_fix;subst.
      eapply IHn with (ρ:=((n0, v0) :: (n1, vClos e n0 (cmFix n1) t0 t1 e0) :: e));
        eauto with hints.
  + unfold expr_eval_i in *. simpl. simpl in He.
    destruct (resolve_constr Σ i n0) eqn:Hres;inversion He;tryfalse;eauto with hints.
  + tryfalse.
  + unfold expr_eval_i in *. simpl. simpl in He.
    simpl in Hc. inv_andb Hc.
    destruct p as [ind e1]. destruct (expr_eval_general n false Σ ρ e) eqn:He';tryfalse.
    destruct v0;tryfalse. destruct (resolve_constr Σ i n0) eqn:Hres;tryfalse.
    destruct p as [n1 tys]. destruct (string_dec ind i);tryfalse;subst.
    destruct (match_pat n0 tys l0 l) eqn:Hpm;tryfalse. destruct p as [assign e2].
    apply pat_match_succeeds in Hpm. destruct Hpm as [pt Htmp].
    destructs Htmp. subst.
    assert (Hok_constr : val_ok Σ (vConstr i n0 l0)) by now eapply IHn with (e:=e).
    inversion Hok_constr;subst;clear Hok_constr.
    assert (Hok_l2 : env_ok Σ (rev (combine (pVars pt) l0))) by
        now (apply rev_env_ok;apply Forall_env_ok).
    eapply IHn with (ρ := (rev (combine (pVars pt) l0) ++ ρ));eauto.
    apply env_ok_concat;auto.
    rewrite app_length,rev_length,combine_length.
    apply find_some in H1. destruct H1.
    apply forallb_Forall in H0. rewrite Forall_forall in *.
    rewrite H3,PeanoNat.Nat.min_id. now apply (H0 (pt,e2)).
  + unfold expr_eval_i in *. simpl. simpl in He.
    inversion He. constructor;eauto.
Qed.

Lemma from_vConstr_not_lambda :
  forall (Σ : global_env) (i : Ast.inductive) (n0 : name) (na : BasicAst.name) (t0 b : term) l,
    tLambda na t0 b = T⟦ from_val_i (vConstr i n0 l) ⟧ Σ -> False.
Proof.
  intros Σ i n0 na t0 b l H.
  induction l using rev_ind.
  + simpl in H. destruct (resolve_constr Σ i n0);tryfalse.
  + simpl_vars_to_apps in H.
    destruct (T⟦ vars_to_apps (eConstr i n0) (map from_val_i l) ⟧ Σ);tryfalse.
Qed.

Lemma expr_to_term_not_ind Σ e i u:
  tInd i u = T⟦e⟧Σ -> False.
Proof.
  induction e using expr_ind_case;intros Heq;simpl in Heq;tryfalse.
  destruct (resolve_constr Σ i0 n);tryfalse.
  destruct p;tryfalse.
Qed.

(* Lemma Wcbv_app_inv Σ Γ e t l : *)
(*   Σ ;;; Γ |- tApp e l ⇓ t -> *)
(*  (exists i n u, Σ ;;; Γ |- e ⇓ tConstruct i n u) \/ *)
(*  (exists nm ty b, Σ ;;; Γ |- e ⇓ tLambda nm ty b) \/ *)
(*  (exists f n, e = tFix f n) \/ *)
(*  (exists i u , Σ ;;; Γ |- e ⇓ tInd i u). *)
(* Proof. *)
(*   intros Happ. *)
(*   inversion Happ;subst; easy. *)
(* Qed. *)


Lemma tFix_eq_inv f l Σ e :
  T⟦e⟧Σ = tFix f l -> exists fixname var ty1 ty2 b, e = eFix fixname var ty1 ty2 b.
Proof.
  destruct e;intros H1;try easy.
  + simpl in *. now destruct (resolve_constr Σ i n).
  + simpl in *. now destruct p.
  + simpl in *. inversion H1. repeat eexists;eauto.
Qed.

Lemma inst_env_eFix_eq_inv (ρ : env val) ty1 ty2 e b fixname var :
  inst_env_i ρ e = eFix fixname var ty1 ty2 b ->
  (exists fixname1 var1 ty11 ty21 b1,
      e = eFix fixname1 var1 ty11 ty21 b1) \/
  (exists n fixname1 var1 ty11 ty21 b1,
    e = eRel n /\
    lookup_i (exprs ρ) n =
    Some (eFix fixname1 var1 ty11 ty21 b1)).
Proof.
  intros H.
  destruct e; try easy.
  right. cbn in H.
  replace (n-0) with n in * by lia.
  destruct ((lookup_i (exprs ρ) n)) eqn:Hlookup;tryfalse.
  simpl in *. subst.
  repeat eexists; eauto.
  left;repeat eexists; eauto.
Qed.

Lemma from_val_fix fixname var ty1 ty2 b v :
  from_val_i v = eFix fixname var ty1 ty2 b ->
  exists ρ b1, v = vClos ρ var (cmFix fixname) ty1 ty2 b1.
Proof.
  intros H. induction v.
  + cbn in  H.
    destruct l using rev_ind;try simpl_vars_to_apps in H;tryfalse.
  + destruct c; simpl in *.
    * tryfalse.
    * repeat eexists. inversion H. subst. f_equal.
Qed.

(* Lemma mkApps_isApp t args : *)
(*   args <> [] -> isApp t = true -> *)
(*   exists args' f, mkApps t args = tApp f (args' ++ args). *)
(* Proof. *)
(*   intros Hneq Happ. *)
(*   destruct args;tryfalse. cbn. *)
(*   destruct t;tryfalse. easy. *)
(* Qed. *)

(* Lemma mkApps_isApp_decompose_app t args : *)
(*   args <> [] -> isApp t = true -> *)
(*   exists args' f, mkApps t args = tApp f (args' ++ args) *)
(*                   /\ f = fst (decompose_app t) /\ args' = snd (decompose_app t). *)
(* Proof. *)
(*   intros Hneq Happ. *)
(*   destruct args;tryfalse. cbn. *)
(*   destruct t;tryfalse. simpl in *. easy. *)
(* Qed. *)

(* Definition decompose_eApp (e : expr) : expr * list expr := *)
(*   match e with *)
(*   | eApp e1 e2 => (e1,[e2]) *)
(*   | _ => (eVar "", []) *)
(*   end. *)


(* Fixpoint from_nested_app (e : expr) : expr := *)
(*   match e with *)
(*   | eApp e1 e2 => from_nested_app e1 *)
(*   | _ => e *)
(*   end. *)

(* Fixpoint args_nested_app (e : expr) : list expr := *)
(*   match e with *)
(*   | eApp e1 e2 => args_nested_app e1 ++ [e2] *)
(*   | _ => [] *)
(*   end. *)

(* Lemma from_nested_app_not_app e : *)
(*   is_app (from_nested_app e) = false. *)
(* Proof. *)
(*   induction e;simpl;auto. *)
(* Qed. *)

(* Lemma form_nested_app_id e : *)
(*   is_app e = false -> from_nested_app e = e. *)
(* Proof. *)
(*   induction e;intros;tryfalse;simpl;auto. *)
(* Qed. *)

(* Lemma not_is_app_decompose e : *)
(*   is_app e = false -> snd (decompose_eApp e) = []. *)
(* Proof. *)
(*   intros. destruct e;simpl in *;tryfalse;auto. *)
(* Qed. *)

(* Lemma is_app_split e : *)
(*   is_app e = false \/ *)
(*   exists args, e = vars_to_apps (from_nested_app e) args. *)
(* Proof. *)
(*   induction e using expr_ind_case;eauto. *)
(*   right. destruct IHe1 as [Happ | Hex]. *)
(*   + exists [e2]. simpl. now rewrite form_nested_app_id. *)
(*   + destruct Hex as [args Hargs]. *)
(*     eexists (args ++ [e2]). simpl. *)
(*     rewrite vars_to_apps_unfold. now rewrite <- Hargs. *)
(* Defined. *)

(* Lemma expr_apps e : *)
(*   e = vars_to_apps (from_nested_app e) (args_nested_app e). *)
(* Proof. *)
(*   induction e;eauto. *)
(*   simpl. rewrite vars_to_apps_unfold. f_equal. assumption. *)
(* Qed. *)

(* Lemma app_nested_app e1 e2 : *)
(*   eApp e1 e2 = vars_to_apps (from_nested_app e1) (args_nested_app e1 ++ [e2]). *)
(* Proof. *)
(*   apply expr_apps. *)
(* Qed. *)



(* Lemma mkApps_not_isApp t args : *)
(*   args <> [] -> isApp t = false -> mkApps t args = tApp t args. *)
(* Proof. *)
(*   intros. rewrite <- Bool.not_true_iff_false in *. *)
(*   now apply mkApps_tApp. *)
(* Qed. *)


(* Lemma mkApps_tApp_exists t args : *)
(*   args <> [] -> *)
(*   exists t' args', mkApps t args = tApp t' args'. *)
(* Proof. *)
(*   intros Hneq. *)
(*   destruct (isApp t) eqn:Happ. *)
(*   * specialize (mkApps_isApp _ _ Hneq Happ) as H;firstorder. *)
(*   * specialize (mkApps_not_isApp _ _ Hneq Happ) as H;firstorder. *)
(* Qed. *)

Ltac destruct_one_ex_named :=
  let tac x H := let x_new := fresh x in (destruct H as [x_new H]) in
    match goal with
      | [H : (exists x1, _) |- _] => tac x1 H
    end.

Ltac destruct_one_ex_named' Hex :=
  let tac x H := (destruct H as [x H]) in
  match Hex with
  | ex (fun x => _) => tac x Hex
  end.


Ltac destruct_ex_named := repeat (destruct_one_ex_named).

Lemma fix_not_constr {e ρ Σ mf n m i nm vs} :
  T⟦ e.[exprs ρ] ⟧ Σ = tFix mf m ->
  eval(n,Σ,ρ,e) = Ok (vConstr i nm vs) -> False.
Proof.
  intros H1 He.
  specialize (tFix_eq_inv _ _ _ _ H1) as HH.
  destruct_ex_named.
  apply inst_env_eFix_eq_inv in HH.
  destruct HH.
  + destruct_ex_named. subst. destruct n;tryfalse.
  + destruct_ex_named. destruct H as [Heq HH];subst.
    destruct n;tryfalse. simpl in He.
    apply option_to_res_ok in He.
    apply lookup_i_from_val_env in He. simpl in *.
    destruct vs using rev_ind;simpl in He;try simpl_vars_to_apps in He;tryfalse.
Qed.


(* Merge this with the generalisation of [fix_not_constr]
   to avoid copy-pasting  *)
Lemma fix_not_lambda {e e1 ty1 ty2 ρ1 ρ2 Σ mf n m nm} :
  T⟦ e.[exprs ρ1] ⟧ Σ = tFix mf m ->
  eval(n,Σ,ρ1,e) = Ok (vClos ρ2 nm cmLam ty1 ty2 e1) -> False.
Proof.
  intros H1 He.
  specialize (tFix_eq_inv _ _ _ _ H1) as HH.
  destruct_ex_named.
  apply inst_env_eFix_eq_inv in HH.
  destruct HH.
  + destruct_ex_named. subst. destruct n;tryfalse.
  + destruct_ex_named. destruct H as [Heq HH];subst.
    destruct n;tryfalse. simpl in He.
    apply option_to_res_ok in He.
    apply lookup_i_from_val_env in He;simpl in *. rewrite HH in He. inversion He.
Qed.

Lemma forall_Forall {A : Type} (P : A -> Prop) (l : list A) :
  (forall a, P a) -> Forall P l.
Proof.
  intros H.
  induction l;constructor;auto.
Qed.

Hint Resolve eval_val_ok from_value_closed : hints.

Lemma closed_exprs n (ρ : env val) Σ :
  env_ok Σ ρ ->
  Forall (fun x => iclosed_n n (snd x) = true) (exprs ρ).
Proof.
  intros H.
  induction ρ.
  + constructor.
  + destruct a;simpl. constructor.
    * inversion H. subst. unfold compose in *. simpl in *.
      eauto with hints.
    * inversion H. subst. unfold compose in *. simpl in *.
      now apply IHρ.
Qed.

Hint Resolve closed_exprs : hints.

Lemma app_inv1 {A} (l l1 l2 : list A) : l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
  intros H. induction l.
  + easy.
  + simpl in *. inversion H. easy.
Qed.

Lemma mkApps_inj :
  forall u v l,
    mkApps u l = mkApps v l ->
    u = v.
Proof.
  intros u v l eq.
  revert u v eq.
  induction l ; intros u v eq.
  - cbn in eq. assumption.
  - cbn in eq. apply IHl in eq.
    inversion eq. reflexivity.
Qed.

(* Lemma mkApps_constr_inv ind l1 l2 n1 n2 u1 u2: *)
(*   mkApps (tConstruct ind n1 u1) l1 = mkApps (tConstruct ind n2 u2) l2 -> *)
(*   l1 = l2 /\ n1 = n2 /\ u1 = u2. *)
(* Proof. *)
(*   intros H. *)
(*   destruct l1 eqn:Hl1;destruct l2 eqn:Hl2. *)
(*   + inversion H. easy. *)
(*   + simpl in *. destruct t;tryfalse. *)
(*   + simpl in *. destruct t;tryfalse. *)
(*   + simpl in *. destruct t;inversion H;  auto. *)
(* Qed. *)

Ltac inv_dummy :=
  match goal with
    [H : _ ;;; _ |- tDummy ⇓ _ |- _ ] => inversion H;inversion isdecl
  end.

Lemma nth_error_map_exists {A B} (f : A -> B) (l : list A) n p:
  nth_error (map f l) n = Some p ->
  exists p0 : A, p = f p0.
Proof.
  intros H.
  revert dependent l.
  induction n;simpl in *;intros l H;destruct l eqn:H1;inversion H;eauto.
Qed.

Section CombineProp.

Lemma map_combine_snd : forall A B C (f : B -> C) (l2 : list B) (l1 : list A),
    #|l1| = #|l2| ->
    (map f l2) = map f (map snd (combine l1 l2)).
Proof.
  induction l2.
  + simpl. intros l1 Heq. destruct l1;tryfalse. reflexivity.
  + simpl. intros l1 Heq. destruct l1;tryfalse. inversion Heq.
    simpl. f_equal. easy.
Qed.

Lemma map_combine_snd_funprod :
  forall A B C (f : B -> C) (l1 : list A) (l2 : list B),
    map (fun_prod id f) (combine l1 l2) = combine l1 (map f l2).
Proof.
  induction l1;intros.
  + reflexivity.
  + destruct l2.
    * reflexivity.
    * cbn. f_equal. apply IHl1.
Qed.

End CombineProp.

Hint Resolve env_ok_concat Forall_env_ok rev_env_ok : hints.

Definition Σ' : global_env :=
  [gdInd "blah" [("Bar", [tyInd "blah"; tyInd "blah"]); ("Baz", [])]].


Parameter a b c d e : val.

Definition blah := vConstr "blah" "Bar" [a;b;c;d;e].

Eval simpl in (T⟦from_val blah⟧  Σ').

Lemma from_val_closed_0 e ρ :
  Forall (fun e0 : string * expr => iclosed_n 0 (snd e0) = true) (exprs ρ) ->
  iclosed_n 0 (e.[exprs ρ]) = true -> iclosed_n #|ρ| e.
Proof.
  intros H. erewrite <- map_length.
  eauto with hints.
Qed.

Hint Resolve map_length from_val_closed_0 val_ok_ge_val_ok : hints.

Lemma not_is_app_isApp e Σ :
  is_app e = false -> isApp (T⟦e⟧Σ) = false.
Proof.
  intros Happ. destruct e;simpl;tryfalse;auto.
  destruct (resolve_constr Σ i n);auto.
  destruct p;auto.
Qed.

(* Lemma eval_var_to_apps  : *)
(*   eval(n, Σ1, ρ, vars_to_apps e1 (e2 :: es)) = Ok v -> *)
(*   exists v, eval (nΣ1, ρ #[nm ~> e2],) *)

(* Lemma mkApps_eval_sound (n : nat) (ρ : env val) Σ1 Σ2 (Γ:=[]) *)
(*       (e1 e2 : expr) (es : list expr) (t : term) (v : val) : *)
(*   (forall (e1 e2 : expr) (ρ : env val) (t : term) (v : val), *)
(*         env_ok Σ1 ρ -> *)
(*         Σ2;;; Γ |- T⟦ e2 ⟧ Σ1 ⇓ t -> *)
(*         (eval (n, Σ1, ρ, e1)) = Ok v -> *)
(*         e1 .[ exprs ρ] = e2 -> iclosed_n 0 e2 = true -> t = T⟦ from_val_i v ⟧ Σ1) -> *)
(*   isApp (T⟦e2⟧Σ1) <> true -> *)
(*   env_ok Σ1 ρ -> *)
(*   Σ2 ;;; Γ |- mkApps (T⟦e2⟧Σ1) (map (expr_to_term Σ1) es) ⇓ t -> *)
(*   eval(n, Σ1, ρ, vars_to_apps e1 es) = Ok v -> *)
(*   e1.[exprs ρ] = e2 -> *)
(*   iclosed_n 0 e2 = true -> *)
(*   t = T⟦from_val_i v⟧Σ1. *)
(* Proof. *)
(*   intros IHn. *)
(*   revert dependent v. *)
(*   revert dependent t. *)
(*   revert dependent ρ. *)
(*   revert dependent e2. *)
(*   revert dependent e1. *)
(*   induction es as [ | e' es'];intros e1 e2 ρ t0 v Happ Henv Hcbv He Heq Hc. *)
(*   + simpl in *. easy. *)
(*   + rewrite mkApps_not_isApp in Hcbv. *)
(*     inversion Hcbv;subst;clear Hcbv. *)
(*     * eapply IHes';eauto. simpl in He. *)
(* Admitted. *)

Hint Constructors Pcbv.value : hints.

(* Lemma mkApps_fp : mkApps t ts = t -> *)

(* Lemma mkApps_inv_singleton x t ts : *)
(*   isApp t = false -> *)
(*   mkApps t ts = mkApps t [x] -> ts = [x]. *)
(* Proof. *)
(*   revert x t. *)
(*   induction ts; intros x1 t0 Hf Heq. *)
(*   - cbn in Heq. destruct t0;tryfalse. *)
(*   - cbn in Heq. destruct ts. *)
(*     * simpl in *. inversion Heq. easy. *)
(*     * simpl in *. inversion Heq. easy. *)

(*     inversion Heq. subst. *)
(*     specialize (IHts _ _ Hf H0). *)
(*     apply IHts in H0. *)
(*     inversion eq. reflexivity. *)


Theorem expr_to_term_sound (n : nat) (ρ : env val) Σ1 Σ2 (Γ:=[]) (e1 e2 : expr) (t : term) (v : val) :
  env_ok Σ1 ρ ->
  Σ2 ;;; Γ |- T⟦e2⟧Σ1 ⇓ t ->
  eval(n, Σ1, ρ, e1) = Ok v ->
  e1.[exprs ρ] = e2 ->
  iclosed_n 0 e2 = true ->
  t = T⟦from_val_i v⟧Σ1.
Proof.
  revert dependent v.
  revert dependent t.
  revert dependent ρ.
  revert dependent e2.
  revert dependent e1.
  induction n.
  - intros;tryfalse.
  - intros e1 e2 ρ t v Hρ_ok HT He Henv Hc.
    destruct e1.
    + (* eRel*)
      autounfold with facts in *. simpl in *.
      destruct (lookup_i ρ n0) as [v1| ] eqn:Hlookup;tryfalse; simpl in He;inversion He;subst.
      assert (Hn0 : n0 < length ρ \/ length ρ <= n0) by lia.
      destruct Hn0 as [Hlt | Hge].
      * destruct (inst_env_i_in _ _ Hlt) as [v2 HH].
        destruct HH as [H1 H2].
        assert (v = v2) by congruence. subst.
        assert (ge_val_ok Σ1 v2) by (apply val_ok_ge_val_ok;eapply Forall_lookup_i;eauto).
        rewrite H2 in HT.
        symmetry.
        eapply Wcbv_eval_value_determ;
        [apply Wcbv_from_value_value;assumption | eassumption ].
      * rewrite <- PeanoNat.Nat.ltb_ge in Hge.
        specialize (lookup_i_length_false _ _ Hge) as Hnone;tryfalse.
    + (* eVar *)
      (* This case is trivial because we only consider terms with de Bruijn indices *)
      destruct n0; tryfalse.
    + (* eLambda *)
      autounfold with facts in *. simpl in HT. simpl in He.
      inversion He. rewrite <- Henv in HT. simpl.
      simpl in HT. apply Wcbv_eval_value_determ in HT; eauto with hints.
    + (* eLetIn *)
      cbn in He.
      destruct (expr_eval_general n false Σ1 ρ e1_1) eqn:He1;tryfalse.
      rewrite <- Henv in HT.
      unfold inst_env_i,subst_env_i in Henv. simpl in Henv.
      simpl in *. inversion HT;subst;simpl;tryfalse.
      * simpl in Hc.
        apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
        specialize (IHn _ _ _ _ _ Hρ_ok H4 He1 eq_refl Hce1) as IH.
        rewrite IH in H5.
        assert (Hv0_ok : val_ok Σ1 v0) by eauto with hints.
        (* An important bit of the proof is to show how substitution of the environment into an expression
         interacts with the substitution of MetaCoq *)
        (* NOTE: subst1 is inconvenient to use, but it's part of the def of
         Pcbv.eval *)
        unfold subst1 in *.
        rewrite subst_term_subst_env with (nm:=n0) in H5 by auto.

        assert (Hρ_ok1 : env_ok Σ1 (ρ # [n0 ~> v0])) by (cbv;eauto with hints).
        eapply IHn;eauto with hints.
        apply subst_env_compose_1; eauto with hints.
        eapply subst_env_iclosed_0;autounfold with hints; eauto with hints.
      * exfalso;eapply mkApps_eq_false;eauto;(try intros ???;tryfalse);
          try intros ?;tryfalse.
      * admit.
      * admit.
    + (* eApp *)
      autounfold with facts in *. simpl in He.
      pose proof HT as HT1.
      rewrite <- Henv in HT.
      destruct (expr_eval_general n false Σ1 ρ e1_1) eqn:He1;tryfalse.
      2 :
        { try (destruct (expr_eval_general n false Σ1 ρ e1_2) eqn:He2);tryfalse. }
      change (eApp e1_1 e1_2 .[ exprs ρ]) with
             (eApp (e1_1.[ exprs ρ]) (e1_2.[ exprs ρ])) in HT.

      (* rewrite app_nested_app in HT. *)
      (* rewrite <- mkApps_vars_to_apps in HT by apply from_nested_app_not_app. *)
      (* rewrite map_app in HT. *)
      (* assert ((map (expr_to_term Σ1) (args_nested_app (e1_1 .[ exprs ρ])) ++ *)
      (*        map (expr_to_term Σ1) [e1_2 .[ exprs ρ]]) <> []). *)
      (* { simpl;intros ?;eapply app_cons_not_nil; symmetry;eauto. } *)
      (* rewrite mkApps_not_isApp in HT;auto; *)
      (*   try (apply not_is_app_isApp;apply from_nested_app_not_app). *)
      (* simpl in HT. *)
      cbn -[mkApps] in HT.
      rewrite <- Henv in Hc.
      simpl in Hc.
      apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
      assert (Hneq1 : [T⟦ inst_env_i ρ e1_2 ⟧ Σ1] <> []) by easy.
      destruct_ex_named.
      destruct v0;
        destruct (expr_eval_general n false Σ1 ρ e1_2) eqn:He2;tryfalse.
      * (* application evaluates to a constructor *)
        inversion_clear He.
        (* there are four possibilities for the application with Wcbv
           of MetaCoq and only one of these should be possible *)
        inversion HT;subst;simpl;tryfalse.
        ** exfalso;eapply from_vConstr_not_lambda. eapply IHn;eauto.
        ** exfalso;symmetry in H; eapply fix_not_constr;eauto.
           admit.
        ** exfalso;eapply expr_to_term_not_ind;eauto.
           admit.
        ** (* the only "real" case *)
          rewrite <- mkApps_vars_to_apps. f_equal.
          change (tConstruct i0 k u = T⟦ from_val_i (vConstr i n0 []) ⟧ Σ1).
          eapply IHn;eauto.
          (*  specialize (IHn _ _ _ _ _ Hρ_ok HT1 He1 eq_refl Hce1) as IH. *)
          (*  simpl in IH. *)
          (*  inversion H4;subst. inversion H6;subst. inversion H4;subst. *)
          (*  assert (l = []). *)
          (*  { destruct l using rev_ind. reflexivity. *)
          (*    simpl_vars_to_apps in IH. *)
          (*    destruct (T⟦ vars_to_apps _ _ ⟧ _);tryfalse. } *)
          (*  subst. *)
          (*  assert (H : y = T⟦ from_val_i v0 ⟧ Σ1) by eauto. subst. *)
          (*  rewrite IH. simpl. *)
           destruct (resolve_constr Σ1 i n0). simpl. f_equal. reflexivity.
      * (* application evaluates to a closure *)
        destruct c0.
        ** (* the closure corresponds to lambda *)
          simpl in *.
          destruct (expr_eval_general n false Σ1 (e0 # [n0 ~> v0]) e1) eqn:Hee1;tryfalse.
          inversion He;subst.
          (* there are four possibilities for the application with Wcbv
           of MetaCoq and only one of these should be possible *)
          inversion HT';subst;simpl;tryfalse.
          *** (* the only "real" case *)
              specialize (IHn _ _ _ _ _ Hρ_ok H4 He2 eq_refl Hce2) as IH.
              simpl in H5.
              rewrite IH in H5.
              assert (Hv0_ok : val_ok Σ1 v0) by eauto with hints.
              assert (Hlam_ok : val_ok Σ1 (vClos e0 n0 cmLam t0 t1 e1))
                by eauto with hints.
              inversion Hlam_ok;subst.
              assert (He_ok1 : env_ok Σ1 (e0 # [n0 ~> v0])) by now constructor.
              specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH'.
              inversion IH'; subst. clear IH'.
              assert
                (ForallEnv (fun e1 : expr => iclosed_n 0 e1 = true) (exprs e0)).
              { inversion He_ok1. subst.
                apply Forall_map. unfold compose. simpl.
                eapply Forall_impl with (P := fun x => val_ok Σ1 (snd x)).
                intros a ?; destruct a; simpl;eauto with hints. assumption. }
              assert (iclosed_n 1 (e1 .[ exprs e0] 1) = true)
                by eauto with hints.

              (* This is an important bit about substitutions again, similarly to the LetIn case *)
              rewrite subst_term_subst_env with (nm:=n0) in H5 by auto.
              eapply IHn;eauto.
              apply subst_env_compose_1;auto with hints.
              eauto with hints.
              apply subst_env_iclosed_n;autounfold with hints;eauto with hints.
          *** exfalso;eapply fix_not_lambda;eauto.
          *** exfalso;now eapply expr_to_term_not_ind.
          *** exfalso;specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH;inversion IH.
        ** (* the closure corresponds to fix *)
          simpl in *. rename e0 into ρ'.
          destruct (expr_eval_general n false Σ1 (((n1, vClos ρ' n0 (cmFix n1) t0 t1 e1) :: ρ') # [n0 ~> v0]) e1) eqn:Hee1;tryfalse.
          inversion He;subst.
          inversion HT';subst;simpl;tryfalse.
          *** exfalso;specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH;inversion IH.
          *** (* the only "real" case *)
            symmetry in H.
            specialize (tFix_eq_inv _ _ _ _ H) as HH.
            destruct_ex_named.
            apply inst_env_eFix_eq_inv in HH.
            destruct HH.
            **** destruct_ex_named. subst. destruct n;tryfalse. simpl in He1.
                 inversion He1. subst. clear He1.
                 simpl in H.
                 inversion H. subst. clear H.
                 inversion H1. subst. clear H1.
                 rewrite type_to_term_subst in H5. inversion H2. subst. clear H2.
                 inversion H6. subst. clear H6.
                 specialize (IHn _ _ _ _ _ Hρ_ok H1 He2 eq_refl Hce2) as IH.
                 subst.
                 (* Now we have a lambda applied to the translation of the argument, so we do inversion
                    on this application *)
                 inversion H5. subst. clear H5.
                 simpl in H8.
                 inversion H4. subst. clear H4.
                 remember
                   (tFix
                      [{| dname := nNamed n1;
                          dtype := tProd nAnon (type_to_term t0) (type_to_term t1);
                          dbody := tLambda (nNamed n0) (type_to_term t0) (T⟦ e1 .[ exprs ρ'] 2 ⟧ Σ1);
                          rarg := 0 |}] 0) as tfix.
                 assert (tfix = T⟦eFix n1 n0 t0 t1 (e1.[exprs ρ']2)⟧ Σ1)
                   by assumption.

                 change (eFix n1 n0 t0 t1 (e1.[exprs ρ']2)) with
                        (from_val_i (vClos ρ' n0 (cmFix n1) t0 t1 e1)) in H.
                 rewrite H in H8.
                 assert (Ha' : a' = T⟦from_val_i v0⟧ Σ1).
                 { symmetry;eapply Wcbv_eval_value_determ;eauto.
                   apply Wcbv_from_value_value;eauto with hints. }
                 assert (val_ok Σ1 v0) by eauto with hints.
                 assert (Hexprs : ForallEnv (fun e => iclosed_n 0 e = true)
                                            (exprs ρ')).
                 { apply Forall_map. unfold compose;simpl.
                   eapply Forall_impl with (P := fun v => val_ok Σ1 (snd v)).
                   { intros a ?;destruct a;cbv;eauto with hints. }
                   assumption. }
                 simpl in Hce1.
                 assert (Hlen_ρ' : #|ρ'| = #|exprs ρ'|) by (symmetry;apply map_length).
                 assert (env_ok Σ1 (ρ' # [n1 ~> vClos ρ' n0 (cmFix n1) t0 t1 e1]
                                   # [n0 ~> v0])) by (constructor;cbv;eauto with hints).
                 rewrite subst_term_subst_env_rec with (nm:=n1) in H8 by eauto.
                 rewrite Ha' in H8.
                 rewrite subst_term_subst_env_rec with (nm:=n0) in H8 by eauto with hints.
                 eapply IHn with (ρ:= ρ' # [n1 ~> vClos ρ' n0 (cmFix n1) t0 t1 e1] # [n0 ~> v0]);
                   (try apply subst_env_iclosed_n;unfold snd);eauto with hints.
                 all: tryfalse.
                 rewrite <- subst_env_compose_1 by eauto with hints.
                 rewrite <- subst_env_compose_2 by eauto with hints.
                 reflexivity.
                 exfalso;easy.
                 exfalso;easy.
            ****
              (* TODO: we have a huge code duplication here, the previous
                 case is pretty much the same *)
              destruct_ex_named. destruct H0. subst. destruct n;tryfalse. simpl in He1.
                 apply option_to_res_ok in He1.
                 assert (Hclos_ok : val_ok Σ1 (vClos ρ' n0 (cmFix n1) t0 t1 e1))
                   by (eapply Forall_lookup_i;eauto).
                 assert (env_ok Σ1 ρ') by now inversion Hclos_ok.
                 apply lookup_i_from_val_env in He1. simpl in He1.
                 rewrite H4 in He1.
                 inversion He1. subst. clear He1.
                 unfold subst_env_i in H. simpl in H.
                 replace (n2-0) with n2 in * by lia.
                 rewrite H4 in H. simpl in H.
                 inversion H. subst. clear H.
                 inversion H1. subst. clear H1.
                 rewrite type_to_term_subst in H5. inversion H2. subst. clear H2.
                 specialize (IHn _ _ _ _ _ Hρ_ok H6 He2 eq_refl Hce2) as IH.
                 subst.
                 (* Now we have lambda applied to the translation of the argument, so we do inversion
                    on this application *)
                 inversion H5. subst. clear H5.
                 inversion H7. subst. clear H7.
                 remember
                   (tFix
                      [{| dname := nNamed n1;
                          dtype := tProd nAnon (type_to_term t0) (type_to_term t1);
                          dbody := tLambda (nNamed n0) (type_to_term t0)
                                           (T⟦e1.[exprs ρ']2⟧ Σ1);
                          rarg := 0 |}] 0) as tfix.
                 assert (H : tfix = T⟦ eFix n1 n0 t0 t1 (e1.[exprs ρ']2) ⟧ Σ1)
                   by assumption.

                 change (eFix n1 n0 t0 t1 (e1.[exprs ρ']2)) with
                        (from_val_i (vClos ρ' n0 (cmFix n1) t0 t1 e1)) in H.
                 rewrite H in *. clear H. clear Heqtfix.
                 assert (Ha' : a' = T⟦ from_val_i v0 ⟧ Σ1).
                 { symmetry;eapply Wcbv_eval_value_determ;eauto.
                   apply Wcbv_from_value_value;eauto with hints. }
                 assert (val_ok Σ1 v0) by eauto with hints.
                 assert (Hexprs : ForallEnv (fun e => iclosed_n 0 e = true)
                                            (exprs ρ')).
                 { apply Forall_map. unfold compose;simpl.
                   eapply Forall_impl with (P := fun v => val_ok Σ1 (snd v)).
                   { intros a ?;destruct a;cbv;eauto with hints. }
                   assumption. }
                 assert (env_ok Σ1 (ρ' # [n1 ~> vClos ρ' n0 (cmFix n1) t0 t1 e1]
                                   # [n0 ~> v0]))
                   by (constructor;cbv;eauto with hints).
                 inversion H8;subst;clear H8.

                 assert (Hce0 : iclosed_n 2 (e1 .[ exprs ρ'] 2) = true) by
                     (inversion Hclos_ok; apply subst_env_iclosed_n; auto with hints).
                 rewrite subst_term_subst_env_rec with (nm:=n1) in H11
                   by eauto with hints.
                 rewrite subst_term_subst_env_rec with (nm:=n0) in H11 by
                     (try apply subst_env_iclosed_n;simpl;eauto with hints).

                 (* we could do better here, but [auto] does not simplify expresions, and
                    [snd] gets on the way. Maybe we should chnage the definition of [ForallEnv]? *)
                 eapply IHn with
                 (ρ:= ρ' # [n1 ~> vClos ρ' n0 (cmFix n1) t0 t1 e1] # [n0 ~> v0]);
                   simpl;(try apply subst_env_iclosed_n;unfold snd);eauto with hints.
                 all : tryfalse.
                 rewrite <- subst_env_compose_1 by eauto with hints.
                 rewrite <- subst_env_compose_2 by eauto with hints.
                 reflexivity.
                 exfalso;easy.
                 exfalso;easy.
          *** exfalso;eapply expr_to_term_not_ind;eauto.
          *** exfalso;specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH;inversion IH.
      * destruct c0;tryfalse.
      * destruct c0;tryfalse.
    + (* eConstr *)
      inversion He. subst. clear He.
      simpl in *. cbn in H0.
      destruct (resolve_constr Σ1 i n0) eqn:Hres;tryfalse.
      inversion HT;subst;simpl in *;eauto. inversion H0. simpl. rewrite Hres. reflexivity.
    + (* eConst *)
      (* The traslation does not support constants yet *)
      inversion He.
    + (* eCase *)
      unfold expr_eval_i in He. destruct p.

      (* dealing with the interpreter *)
      simpl in He.
      destruct (expr_eval_general n false Σ1 ρ e1) eqn:He1;tryfalse.
      destruct v0;tryfalse.
      unfold resolve_constr in *.
      destruct (resolve_inductive Σ1 i0) eqn:HresI;tryfalse.
      destruct (lookup_with_ind l1 n1) eqn:Hfind_i;tryfalse.
      assert (HresC: resolve_constr Σ1 i0 n1 = Some p).
      { unfold resolve_constr. rewrite HresI. rewrite Hfind_i. reflexivity. }

      destruct p as [? ci].
      destruct (string_dec i i0) eqn:Hi;tryfalse.
      destruct (match_pat n1 ci l0 l) eqn:Hpat;tryfalse.
      destruct p. subst.

      (* dealing with the translation and the evaluation in MetaCoq *)
      simpl in HT. inversion HT;simpl;tryfalse. subst. clear HT.
      simpl in Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 HH].
      specialize (IHn _ _ _ _ _ Hρ_ok H5 He1 eq_refl Hce1) as IH. clear H5.
      simpl in IH.
      rewrite map_map in H6. simpl in H6.
      erewrite <- mkApps_vars_to_apps_constr in IH by eauto.
      simpl in IH. apply mkApps_constr_inv in IH .
      destruct IH as [? Htmp]. destruct Htmp. subst.
      unfold iota_red in H6. simpl in H6.
      rewrite <- nth_default_eq in H6.
      unfold nth_default in *.
      destruct (nth_error _) eqn:Hnth;remember ((fun (x : pat * expr) => _)) as f in Hnth.
      * rewrite HresI in Hnth.
        simpl in *.
        destruct p as [i ci0].
        simpl in *.
        specialize (lookup_ind_nth_error _ _ _ _ Hfind_i) as Hnth_eq.
        simpl in Hnth_eq.
        erewrite map_nth_error in Hnth by eauto.
        inversion Hnth as [H1]. clear Hnth.
        (* Exploiting the fact that pattern-matching succeeds *)
        apply pat_match_succeeds in Hpat.
        destruct Hpat as [p Htmp].
        destruct Htmp as [Hfnd Htmp]. destruct Htmp as [Hci Htmp]. destruct Htmp as [Hl0 Hl2].
        assert (Hfind :
        find (fun x => (pName (fst x) =? n1)) (map f l) = Some (f (p, e3))).
        { apply find_map with (p1 := fun x => (pName (fst x) =? n1));auto.
          intros a;destruct a. subst f. cbn. reflexivity. }
        specialize (find_forallb_map _ Hfnd HH) as Hce1'. simpl in Hce1'.
        rewrite Hfind in H1.
        subst f. unfold id in *. simpl in H1.
        rewrite Hci in H1. rewrite PeanoNat.Nat.eqb_refl in H1.
        inversion H1;clear H1. clear Hfind.
        subst. replace ((#|pVars p| + 0)) with (#|pVars p|) in * by lia.
        assert (Hcomb :
                  #|combine (pVars p) ci| = #|map (fun x : val => T⟦ from_val_i x ⟧ Σ1) l0|).
        { rewrite map_length. rewrite Hl0. rewrite combine_length. rewrite Hci. lia. }
        assert (Hok_constr: val_ok Σ1 (vConstr i0 n1 l0)) by eauto with hints.
        inversion Hok_constr. subst.
        apply pat_to_lam_app in H6;auto with hints.
        rewrite <- map_map in H6.
        rewrite map_combine_snd with (l1:=p.(pVars)) in H6 by (now rewrite map_length).
        rewrite map_map in H6.
        assert (Hcomb_ci : #|combine (pVars p) ci| = #|combine (pVars p) (map from_val_i l0)|).
        { repeat rewrite combine_length. rewrite map_length. easy. }
        rewrite Hcomb_ci in H6.

        assert (val_ok Σ1 v).
        { eapply eval_val_ok with (e:=e3) (ρ:=(rev (combine (pVars p) l0) ++ ρ));
            eauto with hints.
          rewrite app_length. rewrite rev_length. rewrite combine_length.
          rewrite Hl0. rewrite PeanoNat.Nat.min_id. eauto with hints. }

        assert (Hlen : #|pVars p| = #|combine (pVars p) (map from_val_i l0)|).
        { rewrite combine_length. rewrite map_length. lia. }
        rewrite  Hlen in H6. rewrite Hlen in Hce1'.

        rewrite subst_term_subst_env_rec_n with (v:=v) in H6;eauto with hints.
        eapply IHn with (ρ:=(rev (combine (pVars p) l0) ++ ρ)); eauto with hints.
        rewrite map_app.
        symmetry.
        rewrite <- map_combine_snd_funprod.
        rewrite <- map_rev.
        assert (Hlen' : #|map (fun_prod id from_val_i) (combine (pVars p) l0)| =
                #|exprs (rev (combine (pVars p) l0))|).
        { repeat rewrite map_length. rewrite rev_length. reflexivity. }
        rewrite Hlen'.
        apply subst_env_swap_app;eauto with hints.
        apply subst_env_iclosed_n; rewrite <- map_combine_snd_funprod.
        rewrite <- map_rev; eauto with hints.

        simpl. rewrite rev_length. rewrite map_length.
        rewrite map_combine_snd_funprod.
        assert (Hlen'' :
                  #|combine (pVars p) l0| =
                  #|combine (pVars p) (map from_val_i l0)|).
        { repeat rewrite combine_length. rewrite map_length. reflexivity. }
        rewrite Hlen''.
        auto with hints.
        rewrite <- map_combine_snd_funprod.
        apply Forall_map. unfold compose; simpl.
        eapply Forall_impl_inner with (P:=(val_ok Σ1) ∘ snd).
        now apply Forall_env_ok.
        apply Forall_forall. intros x Hin Hx. cbv in Hx.
        destruct x;simpl. eauto with hints.
        apply Forall_map. apply Forall_forall. intros a Hin.
        assert (val_ok Σ1 a). apply -> Forall_forall;eauto.
        apply Wcbv_from_value_value;auto with hints.
      * destruct l0.
        ** simpl in *. inversion H6;subst;try inv_dummy;simpl;tryfalse.
        ** simpl in H6. simpl in *; inversion H6;subst;try inv_dummy;simpl;tryfalse.
    + inversion He;subst;clear He.
      simpl in *.
      inversion HT;simpl;tryfalse;easy.
Qed.
