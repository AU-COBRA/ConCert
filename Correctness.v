(* Proof of correctness of the translation from core language expression to the Template Coq terms *)
Require Import Program.Tactics.
Require Import Ast EvalE Facts CustomTactics String.
Require Template.WcbvEval.
Require Import Template.LiftSubst.
Require Import Template.All.

Require Import List.

Import InterpreterEnvList.
Notation "'eval' ( n , Σ , ρ , e )"  := (expr_eval_i n Σ ρ e) (at level 100).

Import ListNotations.

Import Lia.

Notation "Σ ;;; Γ |- t1 ⇓ t2 " := (WcbvEval.eval Σ Γ t1 t2) (at level 50).
Notation "T⟦ e ⟧ Σ " := (expr_to_term Σ e) (at level 49).

Tactic Notation "simpl_vars_to_apps" "in" ident(H) :=
  simpl in H;try rewrite map_app in H; simpl in H;
  rewrite vars_to_apps_unfold in H;simpl in H.

Tactic Notation "simpl_vars_to_apps" :=
  simpl;try rewrite map_app; simpl; rewrite vars_to_apps_unfold;simpl.


Notation exprs := (map_env from_val_i).

Lemma expr_closed_term_closed e n Σ:
  iclosed_n n e = true -> closedn n (T⟦e⟧Σ) = true.
Admitted.

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
  exists v, lookup_i ρ n = Some v /\ (eRel n).[exprs ρ] = from_val_i v.
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

Lemma Wcbv_from_value_closed v Σ n :
  val_ok v -> closedn n (T⟦ from_val_i v⟧Σ) = true.
Proof.
Admitted.

(* This should from the fact that ⇓ is deterministic and
   the fact that value evaluates to itself, but the fact that
   ⇓ is deterministic is not yet proved in Template Coq *)
Lemma Wcbv_eval_value_determ Σ (Γ:=[]) t1 t2 :
  WcbvEval.value t1 -> Σ ;;; Γ |- t1 ⇓ t2 -> t1 = t2.
Proof.
  Admitted.

Lemma type_to_term_closed ty n : closedn n (type_to_term ty) = true.
Proof.
Admitted.

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

Lemma lookups_eq {ρ i v1 v2} :
  lookup_i_norec ρ i = Some v1 -> lookup_i ρ i = Some v2 ->
  v1 = v2 \/ exists ρ nm fixname ty1 ty2 e,
      v2 = vClos ρ nm (cmFix fixname) ty1 ty2 e.
Proof.
  intros H1 H2.
  revert dependent i.
  induction ρ; intros i H1 H2;tryfalse.
  simpl in *;destruct i;simpl in *;
       [some_inv;subst;easy | replace (i-0) with i in * by lia;easy].
  simpl in *; destruct i;simpl in *. some_inv. right. easy.
  replace (i-0) with i in * by lia;easy.
Qed.

Lemma option_to_res_ok {A} (o : option A) s v:
  option_to_res o s = Ok v ->
  o = Some v.
Proof.
  intros H. destruct o. inversion H;auto. tryfalse.
Qed.

Lemma subst_term_subst_env_rec  e :
  forall v Σ n nm,
  val_ok v ->
  iclosed_n (1+n) e = true ->
  (T⟦e⟧ Σ) {n:=T⟦ from_val_i v ⟧ Σ} =
  (T⟦e.[enEmpty # [nm ~> from_val_i v]]n⟧ Σ).
Proof.
  induction e using expr_ind_case;intros v Σ n1 nm nmHv Hc.
  + (* eRel *)
    simpl.
    destruct (Nat.compare n1 n) eqn:Hn.
    * assert (n1 = n) by auto with facts.
      subst. simpl in *.
      assert (Hn0: Nat.leb n n = true) by auto with facts.
      rewrite Hn0. replace (n - n) with 0 by lia. simpl.
      assert (closed (T⟦ from_val_i v ⟧ Σ) = true) by (apply Wcbv_from_value_closed;auto).
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
    * apply IHe; auto.
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
  (T⟦e.[enEmpty # [nm ~> from_val_i v]]⟧ Σ).
Proof.
  intros.
  apply subst_term_subst_env_rec;auto.
Qed.

Lemma subst_env_i_closed_eq :
  forall (e : expr) (n : nat) (ρ : env expr),
    iclosed_n 0 e = true ->
    subst_env_i_aux n ρ e = e.
Proof.
  intros e n ρ Hc.
Admitted.

(* TODO: This lemma should be generalized.
   At least for [subst_env_i_aux n] *)
Lemma subst_env_compose_1 :
  forall (nm : Ast.name) (e e1: expr) (ρ : env expr),
    ForallEnv (fun x => iclosed_n 0 x = true) ρ ->
    e.[ρ # [nm ~> e1]] =
    (e.[ρ]1).[enEmpty # [nm ~> e1]].
Proof.
  intros nm e e1 ρ.
  unfold inst_env_i,subst_env_i in *. simpl in *.
  induction e using expr_ind_case;intros Hfc.
  + simpl. destruct n.
    * reflexivity.
    * simpl. replace (n-0) with n by lia.
      destruct (lookup_i_norec ρ n) eqn:Hl;auto.
      simpl. assert (iclosed_n 0 e = true) by
          (eapply ForallEnv_lookup_i_norec with
               (P:=fun x : expr => iclosed_n 0 x = true);eauto).
      symmetry. apply subst_env_i_closed_eq. assumption.
  + reflexivity.
  + simpl. f_equal.
Admitted.

(* TODO: this should be an instance of a more general lemma, and
   we will restate this in terms of parallel substitutions *)
Lemma subst_env_compose_2 :
  forall (nm1 nm2 : Ast.name) (e e1 e2: expr) (ρ : env expr),
    ForallEnv (fun x => iclosed_n 0 x = true) ρ ->
    e.[ρ # [nm1 ~> e1] # [nm2 ~> e2]] =
    (e.[ρ]2).[enEmpty # [nm1 ~> e1] # [nm2 ~> e2]].
Proof.
  Admitted.

Import Basics.
Open Scope program_scope.

Lemma ForallEnv_map {A B} (f : A -> B) (ρ : env A) (P : B -> Prop) :
  ForallEnv (P ∘ f) ρ -> ForallEnv P (map_env f ρ).
Proof.
  induction ρ; intros HP; inversion HP; subst; constructor;easy.
Qed.

Lemma forall_ForallEnv {A} (ρ : env A) (P : A -> Prop) :
  (forall a : A, P a) -> ForallEnv P ρ.
Proof.
  induction ρ;intros HP;constructor;auto.
Qed.

Lemma ForallEnv_impl:
  forall (A : Type) (P Q : A -> Prop),
    (forall a : A, P a -> Q a) -> forall ρ, ForallEnv P ρ -> ForallEnv Q ρ.
Proof.
  intros.
  Admitted.

Lemma eval_expr_i_val_ok  n ρ Σ e v :
  ForallEnv val_ok ρ ->
  expr_eval_i n Σ ρ e = Ok v ->
  val_ok v.
Admitted.

Lemma from_vConstr_not_lambda :
  forall (Σ : global_env) (i : Ast.inductive) (n0 : Ast.name) (na : name) (t0 b : term) l,
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
    lookup_i_norec (exprs ρ) n =
    Some (eFix fixname1 var1 ty11 ty21 b1)).
Proof.
  intros H.
  destruct e;try easy.
  right. cbn in H.
  replace (n-0) with n in * by lia.
  destruct ((lookup_i_norec (exprs ρ) n)) eqn:Hlookup;tryfalse.
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

(* This should be a property of env_map *)
Lemma lookup_i_norec_from_val ρ n e :
  lookup_i_norec (exprs ρ) n = Some e ->
  exists v, from_val_i v = e /\ lookup_i_norec ρ n = Some v.
Proof.
  Admitted.

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

(* Since [mkApps] a smart constructor, it should be semantically equivalent to ordinary [tApp] *)
Lemma mkApps_sound Σ Γ e l t :
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
    apply lookup_i_norec_from_val in HH.
    destruct HH as [v1 HH]. destruct HH as [HH1 HH2].
    apply from_val_fix in HH1.
    specialize (lookups_eq HH2 He) as Heq.
    destruct_ex_named. destruct Heq;destruct_ex_named;tryfalse.
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
    apply lookup_i_norec_from_val in HH.
    destruct HH as [v1 HH]. destruct HH as [HH1 HH2].
    apply from_val_fix in HH1.
    specialize (lookups_eq HH2 He) as Heq.
    destruct_ex_named. destruct Heq;destruct_ex_named;tryfalse.
Qed.


Theorem expr_to_term_sound (n : nat) ρ Σ1 Σ2 (Γ:=[]) (e1 e2 : expr) (t : term) (v : val) :
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
      assert (Hn0 : n0 < size ρ \/ size ρ <= n0) by lia.
      destruct Hn0 as [Hlt | Hge].
      * destruct (inst_env_i_in _ _ Hlt) as [v2 HH].
        destruct HH as [H1 H2].
        assert (v = v2) by congruence. subst.
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
      cbn in He.
      destruct (expr_eval_general n false Σ1 ρ e1_1) eqn:He1;tryfalse.
      rewrite <- Henv in HT.
      unfold inst_env_i,subst_env_i in Henv. simpl in Henv.
      simpl in *. inversion_clear HT.
      rewrite <- Henv in Hc.
      simpl in Hc.
      apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
      specialize (IHn _ _ _ _ _ Hρ_ok H He1 eq_refl Hce1) as IH.
      rewrite IH in H0.
      assert (Hv0_ok : val_ok v0) by (eapply eval_expr_i_val_ok;eauto).
      (* An important bit of the proof is to show how substitution of the environment into an expression
         interacts with the substitution of MetaCoq *)
      rewrite subst_term_subst_env with (nm:=n0) in H0 by auto.

      assert (Hρ_ok1 : ForallEnv val_ok (ρ # [n0 ~> v0])).
      { constructor. eapply eval_expr_i_val_ok;eauto. assumption. }
      eapply IHn;eauto. apply subst_env_compose_1.
      apply ForallEnv_map.
      eapply ForallEnv_impl with (fun v => val_ok v).
      { intros; apply from_value_closed;assumption. }
      assumption.
      apply subst_env_iclosed_n. simpl. assumption.
      constructor. apply from_value_closed;assumption.
      constructor.
    + (* eApp *)
      autounfold with facts in *. simpl in He.
      pose proof HT as HT1.
      rewrite <- Henv in HT.
      destruct (expr_eval_general n false Σ1 ρ e1_1) eqn:He1;tryfalse.
      2 :
        { try (destruct (expr_eval_general n false Σ1 ρ e1_2) eqn:He2);tryfalse. }
      change (T⟦(eApp e1_1 e1_2.[exprs ρ])⟧Σ1) with
             (mkApps (T⟦e1_1.[exprs ρ]⟧Σ1) [T⟦e1_2.[exprs ρ]⟧Σ1]) in HT.
      specialize (mkApps_sound _ _ _ _ _ HT) as HT'. clear HT.
      rewrite <- Henv in Hc.
      simpl in Hc.
      apply Bool.andb_true_iff in Hc. destruct Hc as [Hce1 Hce2].
      assert (Hneq : [T⟦ inst_env_i ρ e1_2 ⟧ Σ1] <> []) by easy.
      destruct_ex_named.
      (* apply Wcbv_app_inv in HT'. *)
      destruct v0;destruct (expr_eval_general n false Σ1 ρ e1_2) eqn:He2;tryfalse.
      * (* application evaluates to a constructor *)
        inversion_clear He.
        (* there are four possibilities for the application with Wcbv
           of MetaCoq and only one of these should be possible *)
        inversion HT';subst.
        ** exfalso; now eapply from_vConstr_not_lambda.
        ** exfalso;symmetry in H; now eapply fix_not_constr.
        ** exfalso;now eapply expr_to_term_not_ind.
        ** (* the only "real" case *)
           specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH.
           simpl in IH.
           inversion H4;subst. inversion H6;subst. inversion H4;subst.
           assert (l = []).
           { destruct l using rev_ind. reflexivity.
             simpl_vars_to_apps in IH.
             destruct (T⟦ vars_to_apps _ _ ⟧ _);tryfalse. }
           subst.
           assert (H : y = T⟦ from_val_i v0 ⟧ Σ1) by easy. subst.
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
          inversion HT';subst.
          *** (* the only "real" case *)
              specialize (IHn _ _ _ _ _ Hρ_ok H4 He2 eq_refl Hce2) as IH.
              simpl in H5.
              rewrite IH in H5.
              assert (Hv0_ok : val_ok v0)
                by (eapply eval_expr_i_val_ok;eauto).
              assert (Hlam_ok : val_ok (vClos e n0 cmLam t0 t1 e0))
                by (eapply eval_expr_i_val_ok;eauto).
              inversion Hlam_ok;subst.
              assert (He_ok1 : ForallEnv val_ok (e # [n0 ~> v0]))
                     by now constructor.
              specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH'.
              inversion IH'; subst. clear IH'.
              assert
                (ForallEnv (fun e1 : expr => iclosed_n 0 e1 = true) (exprs e)).
              { apply ForallEnv_map. unfold compose.
                 apply ForallEnv_impl with
                   (P := fun x => val_ok x).
                 intros. inversion He_ok1. subst.
                 now apply from_value_closed. assumption. }
              assert (iclosed_n 1 (e0 .[ exprs e] 1) = true).
              { apply subst_env_iclosed_n.
                * simpl. rewrite map_env_size_norec. assumption.
                * assumption. }
              rewrite subst_term_subst_env with (nm:=n0) in H5 by auto.
              eapply IHn;eauto. now apply subst_env_compose_1.
              apply subst_env_iclosed_n. simpl. assumption.
              constructor. apply from_value_closed;assumption.
              constructor.
          *** exfalso;eapply fix_not_lambda;eauto.
          *** exfalso;now eapply expr_to_term_not_ind.
          *** exfalso;specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH;inversion IH.
        ** (* the closure corresponds to fix *)
          simpl in *.
          destruct (expr_eval_general n false Σ1 (e # [n0 ~> v0]) e0) eqn:Hee1;tryfalse.
          inversion He;subst.
          inversion HT';subst.
          *** exfalso;specialize (IHn _ _ _ _ _ Hρ_ok H2 He1 eq_refl Hce1) as IH;inversion IH.
          *** (* the only "real" case *)
            symmetry in H.
            specialize (tFix_eq_inv _ _ _ _ H) as HH.
            destruct_ex_named.
            apply inst_env_eFix_eq_inv in HH.
            destruct HH.
            **** destruct_ex_named. subst. destruct n;tryfalse. simpl in He1.
                 inversion He1. subst. clear He1.
                 simpl in H. inversion H. subst.
                 clear H. inversion H1. subst. clear H1.
                 rewrite type_to_term_subst in H5. inversion H2. subst. clear H2.
                 inversion H6. subst. clear H6.
                 simpl in H5.
                 specialize (IHn _ _ _ _ _ Hρ_ok H1 He2 eq_refl Hce2) as IH.
                 subst.

                 inversion H5. subst. clear H5.
                 simpl in H8.
                 inversion H4. subst. clear H4.
                 remember
                   (tFix
                      [{|
                          dname := nNamed n1;
                          dtype := tProd nAnon (type_to_term t0) (type_to_term t1);
                          dbody := tLambda (nNamed n0) (type_to_term t0)
                                           (T⟦ e0 .[ exprs ρ] 2 ⟧ Σ1);
                          rarg := 0 |}] 0) as tfix.
                 assert (tfix = T⟦ eFix n1 n0 t0 t1 (e0.[ exprs ρ] 2) ⟧ Σ1)
                   by assumption.

                 change (eFix n1 n0 t0 t1 (e0 .[ exprs ρ] 2)) with
                        (from_val_i (vClos ρ n0 (cmFix n1) t0 t1 e0)) in H.
                 rewrite H in H8.
                 rewrite subst_term_subst_env_rec with (nm:=n1) in H8;
                   eauto.
                 assert (Ha' : a' = T⟦ from_val_i v0 ⟧ Σ1).
                 { admit. (*from H1 and H7 *) }
                 assert (val_ok v0) by (eapply eval_expr_i_val_ok;eauto).
                 rewrite Ha' in H8.
                 rewrite subst_term_subst_env_rec with (nm:=n0) in H8;
                   eauto.
                 assert (env_ok (enRec n1 n0 e0 t0 t1 ρ # [n0 ~> v0])).
                 { constructor; try constructor; assumption. }

                 eapply IHn with (ρ:=enRec n1 n0 e0 t0 t1 ρ # [n0 ~> v0]);eauto.
                 rewrite <- subst_env_compose_1. rewrite <- subst_env_compose_2.
                 simpl. simpl in Hce1.
                 (* f_equal. simpl. f_equal. *)
Admitted.
