(* Proof of correctness of the translation from core language expression to the Template Coq terms *)
Require Template.WcbvEval.
Require Import Template.LiftSubst.
Require Import Template.All.

Require Import String List.

Require Import CustomTactics MyEnv Ast EvalE Facts.

Import InterpreterEnvList.
Notation "'eval' ( n , Σ , ρ , e )"  := (expr_eval_i n Σ ρ e) (at level 100).

Import ListNotations.
Open Scope list_scope.

Import Lia.

Notation "Σ ;;; Γ |- t1 ⇓ t2 " := (WcbvEval.eval Σ Γ t1 t2) (at level 50).
Notation "T⟦ e ⟧ Σ " := (expr_to_term Σ e) (at level 49).

Tactic Notation "simpl_vars_to_apps" "in" ident(H) :=
  simpl in H;try rewrite map_app in H; simpl in H;
  rewrite vars_to_apps_unfold in H;simpl in H.

Tactic Notation "simpl_vars_to_apps" :=
  simpl;try rewrite map_app; simpl; rewrite vars_to_apps_unfold;simpl.


Notation exprs := (map (fun '(nm,v) => (nm, from_val_i v))).

Lemma expr_closed_term_closed e n Σ:
  iclosed_n n e = true -> closedn n (T⟦e⟧Σ) = true.
Admitted.

Lemma from_option_indep {A} (o : option A) d  d' v :
  o = Some v -> from_option o d = from_option o d'.
Proof.
  intros;subst;easy.
Qed.

Lemma lookup_i_form_val_env ρ n v :
  lookup_i ρ n = Some v -> lookup_i (exprs ρ) n = Some (from_val_i v).
Proof.
  Admitted.

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
         apply lookup_i_form_val_env in H.
         now eapply from_option_indep.
Qed.

Lemma lookup_i_notin {A} (ρ : env A) n :
  length ρ <= n -> lookup_i ρ n = None.
Proof.
  Admitted.

Lemma Wcbv_from_value_value v Σ :
  val_ok v -> WcbvEval.value (T⟦ from_val_i v⟧Σ).
Proof.
Admitted.

Lemma Wcbv_from_value_closed v Σ n :
  val_ok v -> closedn n (T⟦ from_val_i v⟧Σ) = true.
Proof.
Admitted.

(* This should from the fact that ⇓ is deterministic and
   the fact that value evaluates to itself, but the fact that
   ⇓ is deterministic is not yet proved in Template Coq *)
Lemma Wcbv_eval_value_determ Σ Γ t1 t2 :
  WcbvEval.value t1 -> Σ ;;; Γ |- t1 ⇓ t2 -> t1 = t2.
Proof.
  Admitted.

Lemma closedn_n_m n m t: closedn n t = true -> closedn (m+n) t = true.
Proof.
  revert n. revert m.
  induction t;intros n0 m0 H;auto.
  + simpl in *. rewrite PeanoNat.Nat.ltb_lt in *;lia.
  + simpl in *. induction l;simpl in *;auto.
    rewrite Bool.andb_true_iff in *. destruct H.
    (* TODO: we need a better induction principle for [term]
       capturing nested lists of terms *) admit.
  + simpl in *. rewrite Bool.andb_true_iff in *. destruct H.
    split;easy.
  + simpl in *.
    rewrite Bool.andb_true_iff in *. destruct H.
    rewrite IHt1 by assumption. replace (S (n0 + m0)) with (n0 + S m0) by lia.
    rewrite IHt2 by assumption. auto.
  + simpl in *.
    rewrite Bool.andb_true_iff in *. destruct H.
    rewrite IHt1 by assumption. replace (S (n0 + m0)) with (n0 + S m0) by lia.
    rewrite IHt2 by assumption. auto.
  + simpl in *.
    repeat rewrite Bool.andb_true_iff in *. destruct H as [Htmp H]. destruct Htmp.
    rewrite IHt1 by assumption. replace (S (n0 + m0)) with (n0 + S m0) by lia.
    rewrite IHt2 by assumption. rewrite IHt3 by assumption.
    auto.
  + simpl in *. rewrite Bool.andb_true_iff in *.
    destruct H. rewrite IHt by assumption.
    (* we need a better induction principle for [term]
       capturing nested lists of terms *) admit.
  + simpl in *.
    repeat rewrite Bool.andb_true_iff in *. destruct H as [Htmp H]. destruct Htmp.
    rewrite IHt1 by assumption. replace (S (n0 + m0)) with (n0 + S m0) by lia.
    rewrite IHt2 by assumption.
    (* we need a better induction principle for [term]
       capturing nested lists of terms *) admit.
  + simpl in *. easy.
  + simpl in *. (* again, list of fixpoints needs to be considered in IH *)
    admit.
  + simpl in *. (* again, list of fixpoints needs to be considered in IH *)
    admit.
Admitted.

Lemma type_to_term_closed ty n : closedn n (type_to_term ty) = true.
Proof.
  induction ty;simpl;auto.
  rewrite IHty1. simpl.
  apply closedn_n_m with (m:=1). easy.
Qed.

(* This should follow from the closedness of  [type_to_term ty] but there is no
   theorem about substituting to closed terms (yet) in MetaCoq *)
Lemma type_to_term_subst ty n t : (type_to_term ty) {n:=t} = type_to_term ty.
Proof.
Admitted.

Lemma closed_mkApps n t1 t2 :
  closedn n (mkApps t1 [t2]) = true ->
  closedn n t1 = true /\ closedn n t2 = true.
Proof.
  intros Hc.
  simpl in Hc. destruct t1;simpl in Hc;
  try (apply Bool.andb_true_iff in Hc; destruct Hc as [Hct1 HH]);
  try (apply Bool.andb_true_iff in HH; destruct HH as [Hct2 ?]);split;auto.
  rewrite forallb_app in HH.
  apply Bool.andb_true_iff in HH; destruct HH as [Hct2 ?]. simpl in H.
  apply Bool.andb_true_iff in H; destruct H as [H' ?].
  simpl. rewrite Hct1. rewrite Hct2. reflexivity.
  rewrite forallb_app in HH.
  apply Bool.andb_true_iff in HH; destruct HH as [Hct2 ?]. simpl in H.
  apply Bool.andb_true_iff in H; destruct H as [H' ?]. assumption.
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


Compute ((tRel 1) {0:=tVar "a"}).
Compute ((tLambda (nNamed"x") (tInd (mkInd "nat" 0) []) (tApp (tRel 1) [tRel 2])) {0:=tRel 0}).
Compute ( (tApp (tApp (tApp (tApp (tRel 1) [tRel 1]) [tRel 1]) [tRel 1]) [tRel 2]) {0:=tVar "blah"}).
Compute ( T⟦(eApp (eApp (eApp (eApp (eRel 1) (eRel 1)) (eRel 1)) (eRel 1)) (eRel 2))⟧ []).

Lemma option_to_res_ok {A} (o : option A) s v:
  option_to_res o s = Ok v ->
  o = Some v.
Proof.
  intros H. destruct o. inversion H;auto. tryfalse.
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
    simpl.
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
    simpl in *.
    rewrite type_to_term_subst.
    destruct Hc.
    f_equal. easy.
  + (* eLetIn *)
    simpl in *.
    rewrite type_to_term_subst.
    apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
    f_equal;eauto.
  + (* eApp *)
    change ((T⟦ eApp e1 e2 ⟧ Σ)) with ((mkApps (T⟦e1⟧Σ) [T⟦e2⟧Σ])) in *.
    simpl in Hc.
    apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
    rewrite subst_mkApps.
    erewrite IHe1 by eauto. simpl.
    erewrite IHe2 by eauto. reflexivity.
  + (* eConstr *)
    simpl. destruct (resolve_constr Σ i n);auto.
  + (* eConst *)
    reflexivity.
  + (* eCase *)
    simpl in *. destruct p. simpl in *.
    apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
    repeat f_equal.
    * rewrite type_to_term_subst. reflexivity.
    * eapply IHe; eauto.
    * rewrite_all map_map. simpl.
      (* we need something similar to [map_ext], but involving [Forall] coming from IH *)
      apply map_ext.
      intros a. destruct a.
      simpl. unfold on_snd. simpl. f_equal.
      admit.
  + (* eFix *)
    simpl. unfold map_def. simpl. repeat f_equal;try apply type_to_term_subst.
    easy.
Admitted.

Lemma subst_term_subst_env e :
  forall v Σ nm,
  val_ok v ->
  iclosed_n 1 e = true ->
  (T⟦e⟧ Σ) {0:=T⟦ from_val_i v ⟧ Σ} =
  (T⟦e.[nil # [nm ~> from_val_i v]]⟧ Σ).
Proof.
  intros.
  assert (iclosed_n 0 (from_val_i v) = true) by now apply from_value_closed.
  now apply subst_term_subst_env_rec.
Qed.

Lemma subst_env_i_closed_eq :
  forall (e : expr) (n : nat) (ρ : env expr),
    iclosed_n 0 e = true ->
    e.[ρ]n = e.
Proof.
  intros e n ρ Hc.
Admitted.


(* TODO: This lemma should be generalized.
   At least for [subst_env_i_aux n].
   we will restate this in terms of parallel substitutions *)
Lemma subst_env_compose_1 k :
  forall (nm : Ast.name) (e e1: expr) (ρ : env expr),
    Forall (fun x => iclosed_n 0 (snd x) = true) ρ ->
    iclosed_n 0 e1 = true ->
    e.[ρ # [nm ~> e1]]k =
    (e.[ρ](1+k)).[nil # [nm ~> e1]]k.
Proof.
  intros nm e e1 ρ.
  unfold inst_env_i,subst_env_i in *. simpl in *.
  induction e using expr_ind_case;intros Hfc.
  + simpl. destruct n.
    * reflexivity.
    * simpl. destruct k. simpl. replace (n-0) with n by lia.
      destruct (lookup_i ρ n) eqn:Hl;auto.
      simpl. assert (iclosed_n 0 e = true) by
          (eapply Forall_lookup_i with
               (P:=fun x : expr => iclosed_n 0 x = true);eauto).
      symmetry. apply subst_env_i_closed_eq. assumption.
Admitted.

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


Fixpoint nsubst (ts : list term) (n : nat) (t :term) :=
  match ts with
  | [] => t
  | t0 :: ts0 => nsubst ts0 (n-1) (subst t0 n t)
  end.

Parameter a0 : term.
Parameter a1 : term.
Parameter a2 : term.
Parameter t : term.

Eval simpl in nsubst [a0;a1;a2] 2 t.

Lemma subst_term_subst_env_rec_n :
  forall v Σ (l : env expr) e,
  val_ok v ->
  iclosed_n 0 e = true ->
  Forall (fun x : string * expr => iclosed_n 0 (snd x) = true) l ->
  nsubst (map (fun x => expr_to_term Σ (snd x)) l) (#|l| - 1) (T⟦e⟧ Σ) = (T⟦e.[rev l]⟧ Σ).
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
    rewrite subst_term_subst_env_rec with (nm:=nm);eauto. simpl.
    replace ((#|l| - 0 - 1)) with (#|l| - 1) by lia.
    erewrite IHl;eauto. f_equal.
    replace (#|l| - 0) with (#|l|) by lia.
    rewrite <- rev_length.
    eapply subst_env_swap_app;eauto.
    now apply Forall_rev.
    replace (#|l| - 0) with (#|l|) by lia.
    simpl in *. now rewrite subst_env_i_closed_eq by assumption.
    now apply iclosed_n_0.
Qed.

Import Basics.
Open Scope program_scope.

(* Lemma forall_ForallEnv {A} (ρ : env A) (P : A -> Prop) : *)
(*   (forall a : A, P a) -> ForallEnv P ρ. *)
(* Proof. *)
(*   induction ρ;intros HP;constructor;auto. *)
(* Qed. *)

(* Lemma ForallEnv_impl: *)
(*   forall (A : Type) (P Q : A -> Prop), *)
(*     (forall a : A, P a -> Q a) -> forall ρ, ForallEnv P ρ -> ForallEnv Q ρ. *)
(* Proof. *)
(*   intros. *)
(*   Admitted. *)

Lemma eval_val_ok  n ρ Σ e v :
  env_ok ρ ->
  expr_eval_i n Σ ρ e = Ok v ->
  val_ok v.
Admitted.

Lemma from_vConstr_not_lambda :
  forall (Σ : global_env) (i : Ast.inductive) (n0 : Ast.name) (na : Template.Ast.name) (t0 b : term) l,
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
  destruct (T⟦ e1 ⟧ Σ);tryfalse.
  destruct (resolve_constr Σ i0 n);tryfalse.
  destruct p;tryfalse.
Qed.

Lemma Wcbv_app_inv Σ Γ e t l :
  Σ ;;; Γ |- tApp e l ⇓ t ->
 (exists i n u, Σ ;;; Γ |- e ⇓ tConstruct i n u) \/
 (exists nm ty b, Σ ;;; Γ |- e ⇓ tLambda nm ty b) \/
 (exists f n, e = tFix f n) \/
 (exists i u , Σ ;;; Γ |- e ⇓ tInd i u).
Proof.
  intros Happ.
  inversion Happ;subst; easy.
Qed.


Lemma tFix_eq_inv f l Σ e :
  T⟦e⟧Σ = tFix f l -> exists fixname var ty1 ty2 b, e = eFix fixname var ty1 ty2 b.
Proof.
  destruct e;intros H1;try easy.
  + simpl in *. now destruct (T⟦ e1 ⟧ Σ).
  + simpl in *. now destruct (resolve_constr Σ i n).
  + simpl in *. now destruct p.
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
  destruct e;try easy.
  right. cbn in H.
  replace (n-0) with n in * by lia.
  destruct ((lookup_i (exprs ρ) n)) eqn:Hlookup;tryfalse.
   simpl in *. subst.
  repeat eexists; easy.
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

Lemma mkApps_isApp t args :
  args <> [] -> isApp t = true -> exists args' f, mkApps t args = tApp f (args' ++ args).
Proof.
  intros Hneq Happ.
  destruct args;tryfalse. cbv.
  cbv in Happ. destruct t;tryfalse. easy.
Qed.

Lemma mkApps_not_isApp t args :
  args <> [] -> isApp t = false -> mkApps t args = tApp t args.
Proof.
  intros. rewrite <- Bool.not_true_iff_false in *.
  now apply mkApps_tApp.
Qed.


Lemma mkApps_tApp_exists t args :
  args <> [] ->
  exists t' args', mkApps t args = tApp t' args'.
Proof.
  intros Hneq.
  destruct (isApp t) eqn:Happ.
  * specialize (mkApps_isApp _ _ Hneq Happ) as H;firstorder.
  * specialize (mkApps_not_isApp _ _ Hneq Happ) as H;firstorder.
Qed.

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

(* Since [mkApps] a smart constructor, it should be semantically
   equivalent to the ordinary [tApp] *)
Lemma mkApps_sound Σ Γ e l t :
  l <> [] ->
  Σ ;;; Γ |- mkApps e l ⇓ t ->
  Σ ;;; Γ |- tApp e l ⇓ t.
Proof.
Admitted.

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
    apply lookup_i_form_val_env in He. simpl in *.
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
    apply lookup_i_form_val_env in He;simpl in *. rewrite HH in He. inversion He.
Qed.

Lemma forall_Forall {A : Type} (P : A -> Prop) (l : list A) :
  (forall a, P a) -> Forall P l.
Proof.
  intros H.
  induction l;constructor;auto.
Qed.

Lemma closed_exprs_len_iff e n (ρ : env val) :
  iclosed_n (n + #|exprs ρ|) e = true <->
  iclosed_n (n + #|ρ|) e = true.
Proof.
  split.
  intros H. rewrite map_length in H. assumption.
  intros H. rewrite map_length. assumption.
Qed.

Hint Constructors val_ok Forall : hints.

Hint Resolve eval_val_ok from_value_closed : hints.

Hint Resolve <- subst_env_iclosed_n closed_exprs_len_iff : hints.
Hint Resolve -> subst_env_iclosed_n closed_exprs_len_iff : hints.

Lemma closed_exprs n (ρ : env val) :
  env_ok ρ ->
  Forall (fun x => iclosed_n n (snd x) = true) (exprs ρ).
Proof.
  intros H.
  induction ρ.
  + constructor.
  + destruct a;simpl. constructor.
    * inversion H. subst. unfold compose in *. simpl in *.
      auto with hints.
    * inversion H. subst. unfold compose in *. simpl in *.
      now apply IHρ.
Qed.

Hint Resolve closed_exprs : hints.

Lemma mkApps_vars_to_apps:
  forall (Σ1 : global_env) (i0 : Ast.inductive) (n1 : Ast.name) (l0 : list val) ci,
    resolve_constr Σ1 i0 n1 = Some ci ->
    mkApps (tConstruct (mkInd i0 0) (fst ci) []) (map (fun x => T⟦from_val_i x⟧ Σ1) l0) =
    T⟦ vars_to_apps (eConstr i0 n1) (map from_val_i l0) ⟧ Σ1.
Proof.
  intros Σ1 i0 n1 l0 ci Hci.
  induction l0 using rev_ind.
  + simpl. rewrite Hci. reflexivity.
  + repeat rewrite map_app. simpl. rewrite vars_to_apps_unfold.
    change (mkApps (tConstruct {| inductive_mind := i0; inductive_ind := 0 |} (fst ci) [])
                   (map (fun x0 : val => T⟦ from_val_i x0 ⟧ Σ1) l0 ++ [T⟦ from_val_i x ⟧ Σ1]) =
            mkApps (T⟦vars_to_apps (eConstr i0 n1) (map from_val_i l0)⟧ Σ1) [T⟦from_val_i x⟧ Σ1]).
    rewrite <- IHl0. rewrite mkApp_nested. reflexivity.
Qed.

Lemma app_inv1 {A} (l l1 l2 : list A) : l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
  intros H. induction l.
  + easy.
  + simpl in *. inversion H. easy.
Qed.

Lemma mkApps_constr_inv ind l1 l2 n1 n2 u1 u2:
  mkApps (tConstruct ind n1 u1) l1 = mkApps (tConstruct ind n2 u2) l2 ->
  l1 = l2 /\ n1 = n2 /\ u1 = u2.
Proof.
  intros H.
  destruct l1 eqn:Hl1;destruct l2 eqn:Hl2.
  + inversion H. easy.
  + simpl in *. destruct t;tryfalse.
  + simpl in *. destruct t;tryfalse.
  + simpl in *. destruct t;inversion H;  auto.
Qed.

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

Section FindLookupProperties.

  Context {A : Type}
          {B : Type}
          {p : A -> bool}.

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
      destruct p0; destruct (s =? key) eqn:Heq; try rewrite eqb_eq in *;subst.
      inversion H;eauto.
      now apply (lookup_ind_nth_error_False _ 0 0) in H.
    + destruct ρ0;tryfalse. unfold lookup_with_ind in H. simpl in *.
      destruct p0; destruct (s =? key) eqn:Heq;
        try rewrite eqb_eq in *;subst;tryfalse.
      apply IHi. now apply lookup_ind_nth_error_shift.
  Qed.

  Lemma find_map p1 p2 a (f : A -> B) (l : list A) :
    find p1 l = Some a -> (forall a, p1 a = p2 (f a)) -> find p2 (map f l) = Some (f a).
  Proof.
    intros Hfind Heq.
    induction l;tryfalse.
    simpl in *. rewrite <- Heq.
    destruct (p1 a3);inversion Hfind;subst;auto.
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

  Lemma find_forallb {xs : list A} {p1 : A -> bool}:
    forall x, find p xs = Some x -> forallb p1 xs = true -> p1 x = true.
  Proof.
    intros x Hfnd Hall.
    replace xs with (map id xs) in Hall by apply map_id.
    eapply @find_forallb_map with (f:=id);eauto.
  Qed.

End FindLookupProperties.


Lemma pat_match_succeeds {A} cn arity vals brs e (assig : list (Ast.name * A)) :
    match_pat cn arity vals brs = Some (assig, e) ->
    exists p, find (fun '(p, _) => pName p =? cn) brs = Some (p,e)
         /\ #|arity| = #|p.(pVars)| /\ #|vals| =  #|p.(pVars)|
         /\ assig = combine p.(pVars) vals.
Proof.
  intros Hpm.
  unfold match_pat in Hpm. simpl in Hpm.
  destruct (find (fun '(p, _) => pName p =? cn) brs) eqn:Hfnd;tryfalse.
  destruct p as [p' e0].
  destruct (Nat.eqb #|vals| #|pVars p'|) eqn:Hlength;tryfalse.
  destruct (Nat.eqb #|vals| #|arity|) eqn:Hlength';tryfalse.
  simpl in *.
  inversion Hpm. subst. clear Hpm.
  exists p'. rewrite PeanoNat.Nat.eqb_eq in *. easy.
Qed.

Hint Resolve -> length_zero_iff_nil : hints.
Hint Resolve <- length_zero_iff_nil : hints.
Hint Resolve type_to_term_subst : hints.
Hint Resolve type_to_term_closed : hints.

Lemma subst_pat_to_lam l t u n:
  (pat_to_lam l t) {n:=u} = pat_to_lam l (t {#|l|+n := u}).
Proof.
  revert dependent n.
  induction l;intros n.
  + simpl. reflexivity.
  + destruct a; simpl. f_equal. auto with hints.
    replace (S (#|l| + n)) with (#|l|+S n) by lia.
    apply IHl.
Qed.

Lemma pat_to_lam_app l args t v Σ Γ :
  Forall WcbvEval.value args ->
  #|l| = #|args| ->
  Σ ;;; Γ |- mkApps (pat_to_lam l t) args ⇓ v ->
  Σ ;;; Γ |- nsubst args (#|l| - 1) t ⇓ v.
Proof.
  revert args. revert t.
  induction l; intros t0 args Hval Heq He.
  + simpl in *. destruct args;tryfalse. simpl in *. easy.
  + destruct a. simpl in *.
    destruct args as [ | a0 args0];tryfalse. inversion Heq. clear Heq.
    simpl in *. replace (#|l| - 0) with (#|l|) by lia.
    inversion He; try inversion H3;subst;tryfalse.
    rewrite subst_pat_to_lam in *.
    replace (#|l| + 0) with (#|l|) in * by lia.
    inversion Hval. subst. clear Hval.
    assert (a0=a') by now eapply Wcbv_eval_value_determ.
    subst. now apply IHl.
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

Lemma env_ok_concat ρ1 ρ2 : env_ok ρ1 -> env_ok ρ2 -> env_ok (ρ1 ++ ρ2).
Proof.
Admitted.

Lemma rev_env_ok ρ : env_ok ρ -> env_ok (rev ρ).
Proof.
Admitted.

Lemma Forall_env_ok (ρ : env val) (l : list val) (ns : list name) :
  Forall val_ok l -> env_ok (combine ns l).
Proof.
  revert ns.
  induction l; intros ns H.
  + destruct ns;simpl;constructor.
  + inversion H. subst. destruct ns;unfold compose;simpl. constructor.
    constructor; unfold compose;simpl;auto. now apply IHl.
Qed.

Hint Resolve env_ok_concat Forall_env_ok rev_env_ok : hints.

Theorem expr_to_term_sound (n : nat) (ρ : env val) Σ1 Σ2 (Γ:=[]) (e1 e2 : expr) (t : term) (v : val) :
  env_ok ρ ->
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
        assert (val_ok v2) by (eapply Forall_lookup_i;eauto).
        rewrite H2 in HT.
        symmetry.
        eapply Wcbv_eval_value_determ;
        [apply Wcbv_from_value_value;assumption | eassumption ].
      * specialize (lookup_i_notin _ _ Hge) as Hnone;tryfalse.
    + (* eVar *)
      (* This case is trivial because we only consider terms with de Bruijn indices *)
      destruct n0; tryfalse.
    + (* eLambda *)
      autounfold with facts in *. simpl in HT. simpl in He.
      inversion He. rewrite <- Henv in HT. simpl. inversion HT;simpl;tryfalse. subst.
      reflexivity.
    + (* eLetIn *)
      cbn in He.
      destruct (expr_eval_general n false Σ1 ρ e1_1) eqn:He1;tryfalse.
      rewrite <- Henv in HT.
      unfold inst_env_i,subst_env_i in Henv. simpl in Henv.
      simpl in *. inversion_clear HT;simpl;tryfalse.
      rewrite <- Henv in Hc.
      simpl in Hc.
      apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
      specialize (IHn _ _ _ _ _ Hρ_ok H He1 eq_refl Hce1) as IH.
      rewrite IH in H0.
      assert (Hv0_ok : val_ok v0) by eauto with hints.
      (* An important bit of the proof is to show how substitution of the environment into an expression
         interacts with the substitution of MetaCoq *)
      rewrite subst_term_subst_env with (nm:=n0) in H0 by auto.

      assert (Hρ_ok1 : env_ok (ρ # [n0 ~> v0])) by (cbv;eauto with hints).
      eapply IHn;eauto. apply subst_env_compose_1; auto with hints.
      apply subst_env_iclosed_n;cbv;auto with hints.
    + (* eApp *)
      autounfold with facts in *. simpl in He.
      pose proof HT as HT1.
      rewrite <- Henv in HT.
      destruct (expr_eval_general n false Σ1 ρ e1_1) eqn:He1;tryfalse.
      2 :
        { try (destruct (expr_eval_general n false Σ1 ρ e1_2) eqn:He2);tryfalse. }
      change (T⟦(eApp e1_1 e1_2.[exprs ρ])⟧Σ1) with
             (mkApps (T⟦e1_1.[exprs ρ]⟧Σ1) [T⟦e1_2.[exprs ρ]⟧Σ1]) in HT.
      assert (Hneq: [T⟦e1_2.[exprs ρ]⟧Σ1] <> []) by (intros HH;tryfalse).
      specialize (mkApps_sound _ _ _ _ _ Hneq HT) as HT'. clear HT.
      rewrite <- Henv in Hc.
      simpl in Hc.
      apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
      assert (Hneq1 : [T⟦ inst_env_i ρ e1_2 ⟧ Σ1] <> []) by easy.
      destruct_ex_named.
      (* apply Wcbv_app_inv in HT'. *)
      destruct v0;
        destruct (expr_eval_general n false Σ1 ρ e1_2) eqn:He2;tryfalse.
      * (* application evaluates to a constructor *)
        inversion_clear He.
        (* there are four possibilities for the application with Wcbv
           of MetaCoq and only one of these should be possible *)
        inversion HT';subst;simpl;tryfalse.
        ** exfalso; eapply from_vConstr_not_lambda;eauto.
        ** exfalso;symmetry in H; eapply fix_not_constr;eauto.
        ** exfalso;eapply expr_to_term_not_ind;eauto.
        ** (* the only "real" case *)
           specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH.
           simpl in IH.
           inversion H4;subst. inversion H6;subst. inversion H4;subst.
           assert (l = []).
           { destruct l using rev_ind. reflexivity.
             simpl_vars_to_apps in IH.
             destruct (T⟦ vars_to_apps _ _ ⟧ _);tryfalse. }
           subst.
           assert (H : y = T⟦ from_val_i v0 ⟧ Σ1) by eauto. subst.
           rewrite IH. simpl.
           destruct (resolve_constr Σ1 i n0); reflexivity.
      * (* application evaluates to a closure *)
        destruct c.
        ** (* the closure corresponds to lambda *)
          simpl in *.
          destruct (expr_eval_general n false Σ1 (e # [n0 ~> v0]) e0) eqn:Hee1;tryfalse.
          inversion He;subst.
          (* there are four possibilities for the application with Wcbv
           of MetaCoq and only one of these should be possible *)
          inversion HT';subst;simpl;tryfalse.
          *** (* the only "real" case *)
              specialize (IHn _ _ _ _ _ Hρ_ok H4 He2 eq_refl Hce2) as IH.
              simpl in H5.
              rewrite IH in H5.
              assert (Hv0_ok : val_ok v0) by eauto with hints.
              assert (Hlam_ok : val_ok (vClos e n0 cmLam t0 t1 e0)) by eauto with hints.
              inversion Hlam_ok;subst.
              assert (He_ok1 : env_ok (e # [n0 ~> v0])) by now constructor.
              specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH'.
              inversion IH'; subst. clear IH'.
              assert
                (ForallEnv (fun e1 : expr => iclosed_n 0 e1 = true) (exprs e)).
              { apply Forall_map. unfold compose.
                 apply Forall_impl with
                   (P := fun x => val_ok (snd x)).
                 intros a ?. destruct a. inversion He_ok1. subst.
                 simpl;eauto with hints. assumption. }
              assert (iclosed_n 1 (e0 .[ exprs e] 1) = true).
              { apply subst_env_iclosed_n; simpl;try rewrite map_length; eauto with hints. }

              (* This is an important bit about substitutions again, similarly to the LetIn case *)
              rewrite subst_term_subst_env with (nm:=n0) in H5 by auto.
              eapply IHn;eauto. apply subst_env_compose_1;auto with hints.
              apply subst_env_iclosed_n;unfold snd;eauto with hints.
          *** exfalso;eapply fix_not_lambda;eauto.
          *** exfalso;now eapply expr_to_term_not_ind.
          *** exfalso;specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH;inversion IH.
        ** (* the closure corresponds to fix *)
          simpl in *. rename e into ρ'.
          destruct (expr_eval_general n false Σ1 (((n1, vClos ρ' n0 (cmFix n1) t0 t1 e0) :: ρ') # [n0 ~> v0]) e0) eqn:Hee1;tryfalse.
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
                          dbody := tLambda (nNamed n0) (type_to_term t0) (T⟦ e0 .[ exprs ρ'] 2 ⟧ Σ1);
                          rarg := 0 |}] 0) as tfix.
                 assert (tfix = T⟦ eFix n1 n0 t0 t1 (e0.[ exprs ρ'] 2) ⟧ Σ1)
                   by assumption.

                 change (eFix n1 n0 t0 t1 (e0 .[ exprs ρ'] 2)) with
                        (from_val_i (vClos ρ' n0 (cmFix n1) t0 t1 e0)) in H.
                 rewrite H in H8.
                 assert (Ha' : a' = T⟦ from_val_i v0 ⟧ Σ1).
                 { symmetry;eapply Wcbv_eval_value_determ;eauto.
                   apply Wcbv_from_value_value;eauto with hints. }
                 assert (val_ok v0) by eauto with hints.
                 assert (Hexprs : ForallEnv (fun e => iclosed_n 0 e = true)
                                            (exprs ρ')).
                 { apply Forall_map. unfold compose;simpl.
                   eapply Forall_impl with (P := fun v => val_ok (snd v)).
                   { intros a ?;destruct a;cbv;eauto with hints. }
                   assumption. }
                 assert (env_ok (ρ' # [n1 ~> vClos ρ' n0 (cmFix n1) t0 t1 e0]
                                   # [n0 ~> v0]))
                   by (constructor;cbv;eauto with hints).
                 rewrite subst_term_subst_env_rec with (nm:=n1) in H8;eauto.
                 rewrite Ha' in H8.
                 rewrite subst_term_subst_env_rec with (nm:=n0) in H8;eauto.
                 eapply IHn with (ρ:= ρ' # [n1 ~> vClos ρ' n0 (cmFix n1) t0 t1 e0] # [n0 ~> v0]);
                   eauto. all: tryfalse.
                 rewrite <- subst_env_compose_1 by eauto with hints.
                 rewrite <- subst_env_compose_2 by eauto with hints.
                 reflexivity.
                 (* we could do better here, by [auto] does not simplify expresions, and
                    [snd] gets on the way. Maybe we should chnage the definition of [ForallEnv]? *)
                 apply subst_env_iclosed_n; unfold snd;eauto with hints.
                 apply subst_env_iclosed_n; unfold snd;eauto with hints.
                 eauto with hints.
                 exfalso;easy.
                 exfalso;easy.
            ****
              (* TODO: we have a huge code duplication here, the previous
                 case is pretty much the same *)
              destruct_ex_named. destruct H0. subst. destruct n;tryfalse. simpl in He1.
                 apply option_to_res_ok in He1.
                 assert (Hclos_ok : val_ok (vClos ρ' n0 (cmFix n1) t0 t1 e0))
                   by (eapply Forall_lookup_i;eauto).
                 assert (env_ok ρ') by now inversion Hclos_ok.
                 apply lookup_i_form_val_env in He1. simpl in He1.
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
                          dbody := tLambda (nNamed n0) (type_to_term t0) (T⟦ e0 .[ exprs ρ'] 2 ⟧ Σ1);
                          rarg := 0 |}] 0) as tfix.
                 assert (H : tfix = T⟦ eFix n1 n0 t0 t1 (e0.[ exprs ρ'] 2) ⟧ Σ1)
                   by assumption.

                 change (eFix n1 n0 t0 t1 (e0 .[ exprs ρ'] 2)) with
                        (from_val_i (vClos ρ' n0 (cmFix n1) t0 t1 e0)) in H.
                 rewrite H in *. clear H. clear Heqtfix.
                 assert (Ha' : a' = T⟦ from_val_i v0 ⟧ Σ1).
                 { symmetry;eapply Wcbv_eval_value_determ;eauto.
                   apply Wcbv_from_value_value;eauto with hints. }
                 assert (val_ok v0) by eauto with hints.
                 assert (Hexprs : ForallEnv (fun e => iclosed_n 0 e = true)
                                            (exprs ρ')).
                 { apply Forall_map. unfold compose;simpl.
                   eapply Forall_impl with (P := fun v => val_ok (snd v)).
                   { intros a ?;destruct a;cbv;eauto with hints. }
                   assumption. }
                 assert (env_ok (ρ' # [n1 ~> vClos ρ' n0 (cmFix n1) t0 t1 e0]
                                   # [n0 ~> v0]))
                   by (constructor;cbv;eauto with hints).
                 inversion H8. subst. clear H8.

                 assert (Hce0 : iclosed_n 2 (e0 .[ exprs ρ'] 2) = true) by
                     (inversion Hclos_ok;auto with hints).

                 rewrite subst_term_subst_env_rec with (nm:=n1) in *
                   by eauto with hints.
                 rewrite subst_term_subst_env_rec with (nm:=n0) in *
                   by eauto with hints.

                 (* we could do better here, but [auto] does not simplify expresions, and
                    [snd] gets on the way. Maybe we should chnage the definition of [ForallEnv]? *)
                 eapply IHn with
                 (ρ:= ρ' # [n1 ~> vClos ρ' n0 (cmFix n1) t0 t1 e0] # [n0 ~> v0]);
                   try apply subst_env_iclosed_n; simpl;unfold snd;eauto with hints.
                 all : tryfalse.
                 rewrite <- subst_env_compose_1 by (unfold snd;eauto with hints).
                 rewrite <- subst_env_compose_2 by eauto with hints.
                 reflexivity.
                 exfalso;easy.
                 exfalso;easy.
          *** exfalso;eapply expr_to_term_not_ind;eauto.
          *** exfalso;specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH;inversion IH.
      * destruct c;tryfalse.
      * destruct c;tryfalse.
    + (* eConstr *)
      inversion He. subst. clear He.
      simpl in *.
      destruct (resolve_constr Σ1 i n0);tryfalse;
        inversion HT;eauto.
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
      erewrite <- mkApps_vars_to_apps in IH by eauto.
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
        assert (Hfind :find (fun '(p, _) => pName p =? n1) (map f l) = Some (f (p, e0))).
        { apply find_map with (p1 := fun '(p, _) => pName p =? n1);auto.
          intros a;destruct a. subst f. reflexivity. }
        specialize (find_forallb_map _ Hfnd HH) as Hce1'. simpl in Hce1'.
        rewrite Hfind in H1.
        subst f. unfold id in *. simpl in H1.
        inversion H1;clear H1. clear Hfind.
        subst. replace ((#|pVars p| + 0)) with (#|pVars p|) in * by lia.
        assert (Hcomb :
                  #|combine (pVars p) ci| = #|map (fun x : val => T⟦ from_val_i x ⟧ Σ1) l0|).
        { rewrite map_length. rewrite Hl0. rewrite combine_length. rewrite Hci. lia. }
        apply pat_to_lam_app in H6;auto.
        rewrite <- map_map in H6.
        rewrite map_combine_snd with (l1:=p.(pVars)) in H6 by (now rewrite map_length).
        rewrite map_map in H6.
        assert (Hcomb_ci : #|combine (pVars p) ci| = #|combine (pVars p) (map from_val_i l0)|).
        { repeat rewrite combine_length. rewrite map_length. easy. }
        rewrite Hcomb_ci in H6.
        assert (Hok_constr: val_ok (vConstr i0 n1 l0)) by eauto with hints.
        inversion Hok_constr. subst.
        assert (val_ok v) by
            (eapply eval_val_ok with (ρ := rev (combine (pVars p) l0) ++ ρ);eauto with hints).
        rewrite subst_term_subst_env_rec_n with (v:=v) in H6;auto.
        eapply IHn with (ρ:=(rev (combine (pVars p) l0) ++ ρ));eauto with hints.
        rewrite map_app.
        assert (Hlen : #|pVars p| = #|exprs (rev (combine (pVars p) l0))|).
        { rewrite map_length in Hcomb. rewrite map_length. rewrite rev_length.
          rewrite combine_length. lia. }
        rewrite Hlen.
        symmetry. rewrite <- map_combine_snd_funprod.
        rewrite <- map_rev.
        apply subst_env_swap_app;auto with hints.
        apply subst_env_iclosed_n. rewrite <- map_combine_snd_funprod.
        rewrite <- map_rev. auto with hints.
        simpl.
        assert (Hlen : #|pVars p| = #|rev (combine (pVars p) (map from_val_i l0))|).
        { rewrite rev_length. rewrite combine_length. rewrite map_length. lia. }
        rewrite Hlen.
        apply subst_env_iclosed_n;auto with hints.
        rewrite <- Hlen.
        apply subst_env_iclosed_n;auto with hints.
        now apply iclosed_n_0.
        rewrite <- map_combine_snd_funprod;auto with hints.

        assert (Hok_constr: val_ok (vConstr i0 n1 l0)) by eauto with hints.
        inversion Hok_constr. subst.
        apply Forall_map.  unfold compose; simpl.
        apply Forall_impl_inner with (P:=val_ok). apply H0.
        apply forall_Forall;intros;apply Wcbv_from_value_value;auto with hints.
      * destruct l0.
        ** simpl in *. inversion H6;subst;try inv_dummy;simpl;tryfalse.
        ** apply mkApps_sound in H6; simpl in *; inversion H6;subst;try inv_dummy;simpl;tryfalse.
    + inversion He;subst;clear He.
      simpl in *.
      inversion HT;simpl;tryfalse;easy.
Qed.
