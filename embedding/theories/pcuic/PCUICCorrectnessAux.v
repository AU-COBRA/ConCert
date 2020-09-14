(** * Auxillary lemmas for the soundness proof. *)
From MetaCoq.Template Require Import MCList utils.

Require Import PeanoNat.

From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping PCUICClosed  PCUICLiftSubst PCUICWcbvEval.

Require Import String List Basics.

From ConCert.Embedding Require Import CustomTactics Misc MyEnv EnvSubst Ast EvalE PCUICFacts PCUICTranslate Wf.


Notation "'eval' ( n , Σ , ρ , e )"  := (expr_eval_i Σ n ρ e) (at level 100).

Notation "M { j := N }" := (subst (N :: nil) j M) (at level 10, right associativity).

Import ListNotations Lia ssrbool.
Open Scope list_scope.

Import NamelessSubst.

Local Set Keyed Unification.

(* [Bool.trans_eq_bool] kills performance, so we remove it *)
Remove Hints Bool.trans_eq_bool.

Module P := PCUICAst.
Module PcbvCurr := PCUICWcbvEval.

Notation "Σ |- t1 ⇓ t2 " := (PcbvCurr.eval Σ t1 t2) (at level 50).

Tactic Notation "simpl_vars_to_apps" "in" ident(H) :=
  simpl in H;try rewrite map_app in H; simpl in H;
  rewrite vars_to_apps_unfold in H;simpl in H.

Tactic Notation "simpl_vars_to_apps" :=
  simpl;try rewrite map_app; simpl; rewrite vars_to_apps_unfold;simpl.


Section WcbvEvalProp.

  Lemma tInd_atom ind i u :
    PcbvCurr.atom (tInd (mkInd ind i) u).
  Proof. reflexivity. Qed.

  Lemma tInd_value_head Σ ind i u :
    PcbvCurr.value_head Σ (tInd (mkInd ind i) u).
  Proof. reflexivity. Qed.

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
    now rewrite <- mkApps_nested.
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

  Hint Resolve mkApps_tRel_false : facts.

End WcbvEvalProp.


Definition is_app (e : expr) : bool :=
  match e with
  | eApp _ _ => true
  | _ => false
  end.


Lemma mkApps_vars_to_apps l: forall (Σ : global_env) e,
    P.mkApps (t⟦e⟧Σ) (map (expr_to_term Σ) l) =
    t⟦ vars_to_apps e l ⟧ Σ.
Proof.
  induction l;intros.
  + reflexivity.
  + simpl. now rewrite <- IHl.
Qed.

Lemma mkApps_vars_to_apps_constr :
  forall (Σ1 : global_env) (i0 : Ast.inductive) (n1 : BasicAst.ident) (l0 : list val) ci,
    resolve_constr Σ1 i0 n1 = Some ci ->
    mkApps (tConstruct (BasicAst.mkInd (kername_of_string i0) 0) (ci.1.2) []) (map (fun x => t⟦of_val_i x⟧ Σ1) l0) =
    t⟦ vars_to_apps (eConstr i0 n1) (map of_val_i l0) ⟧ Σ1.
Proof.
  intros Σ1 i0 n1 l0 ci Hci.
  rewrite <- mkApps_vars_to_apps.
  simpl. rewrite Hci. apply f_equal. rewrite map_map. reflexivity.
Qed.

Lemma Wcbv_value_vars_to_apps Σ1 Σ2 :
  forall (i : inductive) n (l : list val) ci,
    resolve_constr Σ1 i n = Some ci ->
    All (fun v : val => PcbvCurr.value Σ2 (t⟦ of_val_i v ⟧ Σ1)) l ->
    PcbvCurr.value Σ2 (t⟦ vars_to_apps (eConstr i n) (map of_val_i l) ⟧ Σ1).
Proof.
  intros i n l ci Hres Hfa.
  erewrite <- mkApps_vars_to_apps_constr;eauto.
  eapply PcbvCurr.value_app;auto. now apply All_map.
Qed.

Open Scope bool.

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
  | vTyClos ρ nm e => forallb (ge_val_ok Σ ∘ snd) ρ
  | vTy ty => true
  end.

Hint Constructors PcbvCurr.value : hints.

Lemma decompose_inductive_mkApps ty ind args :
  decompose_inductive ty = Some (ind, args) ->
  type_to_term ty = mkApps (tInd (mkInd (kername_of_string ind) 0) []) (map type_to_term args).
Proof.
  revert args ind.
  induction ty;intros args ind Hdi;inversion Hdi;subst.
  + easy.
  + simpl in *. destruct (decompose_inductive ty1) eqn:Heq;tryfalse.
    destruct p. inversion Hdi. subst.
    rewrite map_app.
    cbn.
    rewrite mkApps_unfold. now f_equal.
Qed.

Lemma decompose_inductive_value:
  forall (Σ : PCUICAst.global_env) (t1 : type) (args : list type) ind,
    PcbvCurr.value Σ (type_to_term t1) ->
    decompose_inductive t1 = Some (ind, args) ->
    All (PcbvCurr.value Σ) (map type_to_term args).
Proof.
  intros Σ t1.
  induction t1;intros args ind Hv Hdi;tryfalse.
  + inversion Hdi;subst. constructor.
  + simpl in *.
    destruct (decompose_inductive t1_1) eqn:HH;tryfalse.
    destruct p as [ind' tys]. inversion Hdi. subst.
    erewrite decompose_inductive_mkApps in Hv by eauto.
    rewrite <- mkApps_unfold in Hv.
    remember (tInd _ _) as tind.
    assert (Hna : ~~ isApp tind) by (subst;auto).
    specialize (PcbvCurr.value_mkApps_inv _ _ _ Hna Hv).
    intros W. destruct W.
    * destruct s.
      ** destruct p as [H1 ?]. destruct tys;simpl;tryfalse.
      ** destruct p as [H1 H2]. now rewrite map_app.
    * destruct p as [H1 H2]. subst;inversion H1.
Qed.

Lemma type_value_term_value Σ ty :
  iclosed_ty 0 ty ->
  ty_val ty ->
  PcbvCurr.value Σ (type_to_term ty).
Proof.
  intros Hc Hty. induction Hty.
  + simpl. constructor. apply tInd_atom.
  + simpl. now constructor.
  + simpl. now constructor.
  + simpl in *. inv_andb Hc.
    erewrite decompose_inductive_mkApps by eauto.
    rewrite <- mkApps_unfold.
    eapply PcbvCurr.value_app.
    * apply tInd_value_head.
    * apply All_app_inv;eauto.
      eapply decompose_inductive_value with (t1:=ty1);eauto.
  + constructor;eauto.
Qed.

Hint Constructors ty_val : hints.

Lemma env_ok_lookup_ty_val ty i Σ ρ :
  env_ok Σ ρ ->
  lookup_i ρ i = Some (vTy ty) ->
  ty_val ty.
Proof.
  intros.
  assert (Hok : val_ok Σ (vTy ty)) by now eapply All_lookup_i.
  inversion Hok;subst;easy.
Qed.

Lemma env_ok_lookup_closed_ty ty i Σ ρ :
  env_ok Σ ρ ->
  lookup_i ρ i = Some (vTy ty) ->
  iclosed_ty 0 ty.
Proof.
  intros.
  assert (Hok : val_ok Σ (vTy ty)) by now eapply All_lookup_i.
  inversion Hok;subst;easy.
Qed.

Lemma eval_ty_closed Σ ty ty_v ρ n :
  env_ok Σ ρ  ->
  eval_type_i n ρ ty = Some ty_v -> iclosed_ty n ty_v.
Proof.
  revert ty_v ρ n.
  induction ty;intros ??? Hok He.
  + simpl in *. inversion He. now subst.
  + simpl in *.
    destruct (eval_type_i (S n) _ _) eqn:Hty;tryfalse.
    inversion He;subst. now simpl.
  + simpl in *.
    destruct (eval_type_i _ _ ty2) eqn:Hty2;tryfalse.
    destruct (eval_type_i _ _ ty1) eqn:Hty1;tryfalse.
    destruct (decompose_inductive _) eqn:Hind;tryfalse.
    inversion He;subst;clear He. simpl.
    split_andb.
    eapply IHty1;intuition;eauto.
    eapply IHty2;intuition;eauto.
  + tryfalse.
  + simpl in *. destruct (n0 <=? n) eqn:Hn0;tryfalse.
    destruct (lookup_i ρ (n - n0)) eqn:Hlook;tryfalse. destruct v;tryfalse.
    inversion He. subst. eapply iclosed_ty_0;now eapply env_ok_lookup_closed_ty.
  + simpl in *.
    destruct (eval_type_i _ _ ty2) eqn:Hty2;tryfalse.
    destruct (eval_type_i _ _ ty1) eqn:Hty1;tryfalse.
    inversion He;subst.
    simpl;split_andb.
    eapply IHty1;intuition;eauto.
    eapply IHty2;intuition;eauto.
Qed.

Lemma type_eval_value Σ ρ ty ty_v n :
  env_ok Σ ρ ->
  eval_type_i n ρ ty = Some ty_v ->
  ty_val ty_v.
Proof.
  intros Hok He.
  revert dependent ty_v. revert n.
  induction ty;intros.
  + simpl in *. inversion He;eauto with hints.
  + simpl in *.
    destruct (eval_type_i (S n) _ _) eqn:Hty;tryfalse.
    inversion He;subst. now constructor.
  + simpl in *.
    simpl in *.
    destruct (eval_type_i _ _ ty2) eqn:Hty2;tryfalse.
    destruct (eval_type_i _ _ ty1) eqn:Hty1;tryfalse.
    destruct (decompose_inductive _) eqn:Hind;tryfalse.
    inversion He;subst;clear He. simpl.
    destruct p as [ind0 args].
    econstructor;eauto.
  + tryfalse.
  + simpl in *. destruct (n0 <=? n);tryfalse.
    destruct (lookup_i ρ (n - n0)) eqn:Hlook;tryfalse. destruct v;tryfalse.
    inversion He. subst. now eapply env_ok_lookup_ty_val.
  + simpl in *.
    destruct (eval_type_i _ _ ty2) eqn:Hty2;tryfalse.
    destruct (eval_type_i _ _ ty1) eqn:Hty1;tryfalse.
    inversion He;subst. now constructor.
Qed.


Lemma type_to_term_eval_value :
  forall Σ1 Σ2 (ty ty_v : type) ρ,
    env_ok Σ2 ρ  ->
    eval_type_i 0 ρ ty = Some ty_v ->
    PcbvCurr.value Σ1 (type_to_term ty_v).
Proof.
  intros.
  eapply type_value_term_value;eauto with hints.
  eapply eval_ty_closed;eauto.
  eapply type_eval_value;eauto.
Qed.

Lemma Wcvb_type_to_term_eval :
  forall (Σ1 : PCUICAst.global_env) Σ2 (ty ty_v : type) ρ,
    env_ok Σ2 ρ ->
    AllEnv (iclosed_n 0) (exprs ρ)  ->
    eval_type_i 0 ρ ty = Some ty_v ->
    Σ1 |- type_to_term ty_v ⇓ type_to_term ty_v.
Proof.
  intros.
  eapply PcbvCurr.value_final.
  eapply type_to_term_eval_value;eauto.
Qed.

Lemma Wcbv_of_value_value v Σ1 Σ2 :
  val_ok Σ1 v ->
  PcbvCurr.value Σ2 (t⟦ of_val_i v⟧Σ1).
Proof.
  intros Hok.
  induction v using val_elim_full.
  + simpl in *.
    inversion Hok;subst.
    eapply Wcbv_value_vars_to_apps;eauto.
    now eapply All_impl_inner.
  + destruct cm. constructor;auto.
    simpl. now constructor.
  + simpl in *. constructor;auto.
  + simpl in *.
    inversion Hok;subst. now eapply type_value_term_value.
Qed.

Lemma lift_1_closed n t :
  closedn n t ->
  closedn (S n) ((lift0 1) t) = true.
Proof.
  replace (S n) with (n+1) by lia.
  now apply closedn_lift with (k:=n) (n:=1).
Qed.


Hint Resolve lift_1_closed : hints.

Lemma type_to_term_closed ty n :
  iclosed_ty n ty ->
  closedn n (type_to_term ty) = true.
Proof.
  revert n.
  induction ty;intros n0 H;simpl in *;
    try (inv_andb H; split_andb);auto with hints.
Qed.


Hint Resolve type_to_term_closed : hints.

Lemma type_to_term_subst Σ ty k e (nm : string) :
  ty_env_ok k [(nm,e)] ty ->
  iclosed_n 0 e ->
  iclosed_ty (1+k) ty ->
  (type_to_term ty) {k:=t⟦e⟧Σ} = type_to_term (subst_env_i_ty k ([(nm,e)]) ty).
Proof.
  revert k e.
  induction ty;intros k e0 Hok Hce Hct;simpl in *;try inv_andb Hct; try inv_andb Hok;
    auto with hints;intuition.
  + destruct (k <=? n);auto.
    destruct (n - k) eqn:Hnk.
    * cbn in *. destruct e0;tryfalse;cbn in *.
         now rewrite lift_closed by auto with hints.
    * cbn in *. unfold is_true in *; leb_ltb_to_prop. lia.
  + f_equal;auto.
    rewrite <- IHty2 by auto.
    rewrite commut_lift_subst_rec by lia.
    now replace (S k) with (k+1) by lia.
Qed.

Lemma type_to_term_eval Σ ty k e (nm : string) v:
  iclosed_ty k ty ->
  eval_type_i k ([(nm,e)]) ty = Some v ->
  (type_to_term ty) {k:=t⟦of_val_i e⟧Σ} = type_to_term v.
Proof.
  revert k e v. induction ty;intros k e0 v Hc H;simpl in *;inversion H;subst;auto;clear H.
  + destruct (eval_type_i _ _ _) eqn:Heq;tryfalse. inversion H1;subst.
    simpl. f_equal;eauto.
  + destruct (eval_type_i _ _ ty2) eqn:Heq2;tryfalse.
    destruct (eval_type_i _ _ ty1) eqn:Heq1;tryfalse.
    destruct (decompose_inductive t0) eqn:Hde;tryfalse.
    inversion H1;subst;clear H1. inv_andb Hc.
    simpl. f_equal;eauto.
  + destruct (k <=? n) eqn:Hkn.
    * destruct (n - k) eqn:Hnk;simpl in *;tryfalse.
      unfold is_true in *;leb_ltb_to_prop. lia.
    * inversion H1;subst;clear H1;auto.
  + destruct (eval_type_i _ _ ty2) eqn:Heq2;tryfalse.
    destruct (eval_type_i _ _ ty1) eqn:Heq1;tryfalse.
    inversion H1;subst;clear H1.
    inv_andb Hc. simpl. rewrite commut_lift_subst. repeat f_equal;eauto.
Qed.

Hint Resolve -> length_zero_iff_nil : hints.
Hint Resolve <- length_zero_iff_nil : hints.
Hint Resolve type_to_term_subst : hints.
Hint Resolve type_to_term_closed : hints.

Hint Unfold compose : hints.

Lemma closedn_pat_to_lam tys e0 n ty_params :
  All ((closedn (n+#|ty_params|)) ∘ snd) tys ->
  All (closedn n) ty_params ->
  closedn (#|tys| + n) e0 ->
  closedn n (pat_to_lam e0 ty_params tys).
Proof.
  revert n ty_params.
  induction tys;intros n params Htys Hty_params Hc.
  + easy.
  + destruct a as [nm ty].
    inversion Htys;subst;clear Htys.
    simpl. split_andb.
    * apply closedn_subst0.
      ** now apply All_forallb.
      ** easy.
    * eapply IHtys;eauto.
      ** eapply (All_impl X). intros. cbn. rewrite map_length. unfold compose in *.
         eapply (closed_upwards (k:=(n + #|params|)));eauto.
      ** eapply All_map. eapply (All_impl Hty_params);auto with hints.
      ** now replace (#|tys| + S n) with (S #|tys| + n) by lia.
Qed.

Fixpoint inc_subst (ts : list (ident * term)) n (u : term) : list (ident * term) :=
  match ts with
  | [] => []
  | (nm, t0) :: ts0 => (nm, t0 {n:=u}) :: inc_subst ts0 (1+n) u
  end.

Lemma subst_pat_to_lam t u n tys params :
  (pat_to_lam t params tys) {n:=u} =
  pat_to_lam (t {#|tys|+n := u}) (map (subst1 u n) params) (inc_subst tys (#|params|+n) u).
Proof.
  simpl.
  revert dependent n. revert params.
  induction tys;intros params n.
  + simpl. reflexivity.
  + destruct a; simpl.
    f_equal.
    * rewrite distr_subst. f_equal.
    * remember (map (lift0 1) params) as params'.
      replace (#|params|) with #|params'| by (subst;apply map_length).
      replace (S (#|tys| + n)) with (#|tys|+S n) by lia.
      rewrite IHtys. f_equal.
      subst; repeat rewrite map_map. eapply map_ext.
      ** intros t1. rewrite commut_lift_subst_rec.
         now replace (S n) with (n+1) by lia. lia.
      ** subst. f_equal. lia.
Qed.

Fixpoint nsubst (ts : list term) (n : nat) (t :term) :=
  match ts with
  | [] => t
  | t0 :: ts0 => nsubst ts0 (n-1) (subst [t0] n t)
  end.

Lemma nsubst_lam xs b nm ty :
  closedn 0 ty ->
  nsubst xs (#|xs| - 1) (tLambda nm ty b) = (tLambda nm ty (nsubst xs #|xs| b)).
Proof.
  revert b nm ty.
  induction xs;intros;auto.
  simpl.
  assert (closedn (#|xs|) ty) by (eapply closed_upwards;eauto;lia).
  replace (#|xs| - 0) with #|xs| in * by lia.
  rewrite subst_closedn by auto. easy.
Qed.

Parameter a0 : term.
Parameter a1 : term.
Parameter a2 : term.
Parameter t : term.

Eval simpl in nsubst [a0;a1;a2] 2 t.

Definition lpat_to_lam : term -> list term -> list (BasicTC.ident * term) -> term
  := fix rec body ty_params tys :=
       match tys with
         [] => body
       | (n,ty) :: tys' =>
         (* NOTE: we need to substitute the parameters into the type
         of each lambda representing a pattern binder. Since each
         lambda introduces a binder, we need also to lift free
         variables in [ty_params] *)
         let lam_type := subst (map (lift0 #|tys'|) ty_params) 0 ty in
         rec (tLambda (BasicTC.nNamed n) lam_type body) ty_params tys'
       end.


Lemma map_lift0 xs : map (lift0 0) xs = xs.
Proof.
  induction xs;auto.
  simpl. now rewrite lift0_p.
Qed.

Lemma simpl_lift_map xs n m p : map ((lift n p) ∘ (lift m p)) xs  = map (lift (n+m) p) xs.
Proof.
  induction xs;auto.
  simpl. unfold compose.
  rewrite simpl_lift by lia.
  f_equal;eauto.
Qed.

Lemma pat_to_lam_unfold b tys n ty params :
  lpat_to_lam b params (tys ++ [(n,ty)]) =
  tLambda (BasicTC.nNamed n) (subst0 params ty) (lpat_to_lam b (map (lift0 1) params) tys).
Proof.
  revert b params.
  induction tys;intros.
  + simpl.
    now rewrite map_lift0.
  + destruct a; simpl in *.
    rewrite <- IHtys.
    rewrite map_map. rewrite simpl_lift_map. rewrite app_length.
    reflexivity.
Qed.

Lemma pat_to_lam_rev tys b params :
  pat_to_lam b params tys = lpat_to_lam b params (rev tys).
Proof.
  revert params.
  induction tys;intros.
  + easy.
  + simpl. destruct a;simpl. rewrite IHtys.
    now rewrite pat_to_lam_unfold.
Qed.

(* TODO : use this lemma in all places where this inversion is needed *)
Lemma eval_lam_inv Σ nm1 nm2 ty1 ty2 b1 b2:
  Σ |- tLambda nm1 ty1 b1 ⇓ tLambda nm2 ty2 b2 -> nm1 = nm2 /\ ty1 = ty2 /\ b1 = b2.
Proof.
  intros H.
  inversion H.
  + now subst.
Qed.

Fixpoint nsubst_alt (ts : list term) (t : term) {struct ts} : term :=
  match ts with
  | [] => t
  | t0 :: ts0 => (nsubst_alt ts0 (t {0 := t0}))
  end.

Lemma closed_upwards0 n t :
  closed t -> closedn n t.
Proof.
  intros;eapply closed_upwards;eauto;lia.
Qed.

Hint Resolve closed_upwards0 subst_closedn : hints.

Lemma nsubst_app ts t0 t1 :
  closed t0 ->
  nsubst (ts ++ [t0]) (#|ts|) t1 = nsubst ts (#|ts| - 1) (t1 {0:=t0}).
Proof.
  revert t0 t1.
  induction ts;intros.
  + simpl. easy.
  + simpl. replace (#|ts| - 0) with #|ts| by lia. rewrite IHts by assumption.
    rewrite distr_subst. simpl. replace (t0 {#|ts| := a}) with t0 by (symmetry;eauto with hints).
    reflexivity.
Qed.

Lemma subst_closed_map ts1 ts2 k :
  forallb (closedn k) ts2 ->
  map (subst ts1 k) ts2 = ts2.
Proof.
  intros H. revert dependent k. revert ts1.
  induction ts2;intros;auto.
  simpl in *. inv_andb H. f_equal;eauto with hints.
Qed.


Ltac destr_args args := let args0 := fresh "args0" in
                        destruct args as [ | ? args0];
                        tryfalse;try destruct args0;tryfalse.

Notation "P <--> Q" := (Logic.BiImpl P Q) (at level 100).

(* NOTE: this solves the "evaluation in one go" issue in [eCase]*)
Lemma pat_to_lam_app_par l params args t v Σ  :
  All (PcbvCurr.value Σ) args ->
  forallb (closedn 0) args ->
  #|l| = #|args| ->
  Σ |- subst (rev args) 0 t ⇓ v ->
  Σ |- mkApps (lpat_to_lam t params l) args ⇓ v .
Proof.
  - revert dependent args. revert t v params.
    induction l; intros t0 v params args Hval Hc Heq He.
    + destr_args args. cbn in *.
      now rewrite subst_empty in *.
      (* now repeat rewrite app_nil_r in *. *)
    + destruct a;simpl in *.
      destruct args as [ | a1 args1] using MCList.rev_ind;tryfalse;clear IHargs1.
      apply All_app in Hval. destruct Hval as [Hargs Ha].
      inversion Ha;subst;clear Ha.
      rewrite forallb_app in Hc. inv_andb Hc. simpl in *.
      inv_andb H0.
      assert (#|l| = #|args1|).
      { rewrite app_length in Heq. simpl in Heq. lia. }
      clear Heq.
      rewrite mkApps_unfold in *.
      rewrite rev_unit in *. cbn in He.
      assert (Σ |- a1 ⇓ a1) by (eapply PcbvCurr.value_final;eauto).
      eapply PcbvCurr.eval_beta;eauto with hints.
      eapply IHl;eauto with hints. simpl. econstructor;simpl;eauto.
      unfold subst1.
      rewrite PCUICCSubst.closed_subst by auto.
      now rewrite <- subst_app_simpl.
Qed.

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

Lemma genv_ok_constrs_ok Σ ind cs nparam:
  genv_ok Σ ->
  resolve_inductive Σ ind = Some (nparam, cs) ->
  forallb (constr_ok nparam) cs.
Proof.
  intros Hgeok Hr. unfold resolve_inductive in *.
  destruct (lookup_global Σ ind) eqn:Hlg;tryfalse.
  destruct g;tryfalse. inversion Hr;subst;clear Hr.
  revert dependent cs.
  induction Σ;intros;tryfalse.
  cbn in *. destruct a. cbn in *.
  destruct (e0 =? ind);now inv_andb Hgeok.
Qed.

Lemma constrs_ok_in s c (cs : list constr) nparam :
  In (s,c) cs ->
  forallb (constr_ok nparam) cs ->
  forallb (iclosed_ty nparam) (map snd c).
Proof.
  intros Hin Hfa.
  assert (constr_ok nparam (s,c)) by (eapply forallb_In;eauto).
  easy.
Qed.

Lemma forallb_type_to_term_closed ts n :
  forallb (iclosed_ty n) ts ->
  forallb (closedn n) (map type_to_term ts).
Proof.
  revert n.
  induction ts;intros;auto.
  cbn in *. inv_andb H. split_andb;eauto with hints.
  eapply IHts;eauto.
Qed.


Hint Resolve forallb_type_to_term_closed.

Lemma expr_closed_term_closed e n Σ:
  genv_ok Σ ->
  iclosed_n n e = true -> closedn n (t⟦e⟧Σ) = true.
Proof.
  revert n.
  induction e using expr_ind_case;intros n1 Hgeok Hc;auto.
  + (* eLambda*)
    simpl in *. rewrite Bool.andb_true_iff.
    inv_andb Hc.
    split;auto with hints.
  + (* eTyLam *)
    simpl in *. destruct Hc. auto.
  + (* eLetIn *)
    simpl in *. repeat rewrite Bool.andb_true_iff in *.
    destruct Hc as [[? ?] ?]. repeat split;simpl;eauto with hints.
  + (* eApp *)
    simpl in Hc. repeat rewrite Bool.andb_true_iff in *.
    cbn -[mkApps]. eauto with hints.
    apply <- closed_mkApps. destruct Hc. easy.
  + (* eConstr *)
    simpl in *. destruct (resolve_constr Σ i n); auto.
  + (* eCase *)
    destruct p. simpl in *. repeat rewrite Bool.andb_true_iff in *.
    destruct Hc as [[[? ?] ?] ?].
    simpl.
    destruct (resolve_inductive Σ i) eqn:Hres;auto.
    destruct ((_ =? _)%nat) eqn:Hnparams.
    simpl.
    repeat split_andb;eauto with hints.
      * eapply closedn_mkApps;eauto.
      * rewrite forallb_map. unfold Basics.compose,test_snd,trans_branch.
        apply forallb_Forall. apply Forall_forall. intros x Hin.
        destruct x as [nm tys]. unfold fun_prod,id in *. simpl.
        destruct (find (fun x => _)) as [ p0 | ] eqn:Hnm;simpl;auto.
        destruct p0 as [pt e1]. cbn. rewrite map_length.
        destruct (Nat.eqb #|pVars pt| #|tys|) eqn:Hlen;auto.
        apply find_some in Hnm. destruct Hnm as [Hin' Heqs].
        rewrite in_map_iff in Hin'.
        destruct Hin' as [x Htmp]. destruct x as [pt1 e2].
        destruct Htmp as [He1 Hin'']. inversion He1;subst;clear He1.
        rewrite Nat.eqb_eq in Hnparams. subst. destruct p as [np cs]. simpl in *.
        assert (Hcs : forallb (constr_ok np) cs) by now eapply genv_ok_constrs_ok.
        assert (Htys :forallb (iclosed_ty np) (map snd tys)) by now eapply constrs_ok_in.
        unfold resolve_inductive in *. destruct (lookup_global _ _);tryfalse. destruct g.
        inversion Hres;subst. simpl.
        apply closedn_pat_to_lam. rewrite map_map.
        rewrite rev_length, map_length.
        remember (map _ tys) as map_tys.
        eapply All_map_inv with (P:=fun x => closedn (n1 + #|l0|) x). rewrite Nat.eqb_eq in Hlen.
        rewrite map_combine_snd by (subst;rewrite map_length;auto).
        simpl in *. subst. apply All_map. unfold compose.
        apply forallb_All in Htys. apply All_map_inv in Htys.
        eapply All_impl. eapply Htys. intros. eapply type_to_term_closed.
        rewrite Nat.add_comm. now eapply iclosed_ty_m_n.
        apply All_rev. apply forallb_All;eauto with hints.
        rewrite combine_length. repeat rewrite map_length.
        replace (min #|pVars pt| #|tys|) with #|pVars pt| by (rewrite Nat.eqb_eq in Hlen;auto;lia).
        specialize (forallb_In _ _ _ Hin'' H3) as Hfa. simpl in Hfa.
        specialize (Forall_In _ _ _ Hin'' H) as Hfa'. simpl in Hfa'. easy.
      * trivial.
  + simpl in *.
    rewrite Bool.andb_true_r in *. unfold test_def. simpl.
    repeat rewrite Bool.andb_true_iff in *.
    repeat split;eauto with hints;
      try apply type_to_term_closed;intuition.
  + simpl in *. eauto with hints.
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
Hint Unfold snd env_ok AllEnv compose : hints.

(* Hint Resolve <- closed_exprs_len_iff : hints. *)
(* Hint Resolve -> closed_exprs_len_iff : hints. *)

Hint Resolve 1 subst_env_iclosed_n_inv subst_env_iclosed_0_inv: hints.
Hint Resolve 1 subst_env_iclosed_n subst_env_iclosed_0 : hints.

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

Lemma forallb_snd {A B} (p : B -> bool) (l1 : list A) (l2 : list B) :
  forallb p l2 -> forallb (fun x => p (snd x)) (combine l1 l2).
Proof.
  revert l1.
  induction l2;intros;destruct l1;auto.
  simpl in *;inv_andb H. split_andb;eauto. eapply IHl2;eauto.
Qed.

Lemma inc_subst_closed ts t n :
  forallb (closedn n) (map snd ts) ->
  inc_subst ts n t = ts.
Proof.
  revert t n.
  induction ts;intros t n H.
  + reflexivity.
  + simpl in *. inv_andb H. destruct a. repeat f_equal; eauto with hints.
    eapply IHts;eauto. unfold is_true; rewrite forallb_forall in *.
    intros. eapply (closed_upwards (k:=n)); eauto with hints.
Qed.

Lemma type_to_term_map :
  forall (e0 : expr) (Σ : global_env) (n : nat) (nm : string) (args : list type),
    iclosed_n 0 e0 ->
    forallb (iclosed_ty (1+n)) args ->
    forallb (ty_env_ok n [(nm, e0)]) args ->
    map (fun x : type => (type_to_term x) {n := t⟦ e0 ⟧ Σ}) args =
    map (fun x : type => type_to_term (subst_env_i_ty n [(nm, e0)] x)) args.
Proof.
  intros e0 Σ n1 nm args Hc Hca Hok.
  induction args.
  + easy.
  + simpl in *. inv_andb Hca. inv_andb Hok. f_equal.
    * apply type_to_term_subst;eauto.
    * eauto.
Qed.

Lemma subst_term_subst_env_rec e e0:
  forall Σ n nm,
  genv_ok Σ ->
  ty_expr_env_ok (nil # [nm ~> e0]) n e ->
  iclosed_n (1+n) e = true ->
  iclosed_n 0 e0 = true ->
  (t⟦e⟧ Σ) {n:=t⟦e0⟧ Σ} =
  (t⟦e.[nil # [nm ~> e0]]n⟧ Σ).
Proof.
  induction e using expr_ind_case;intros Σ n1 nm Hgeok Hok Hc Hce0.
  + (* eRel *)
    cbn.
    destruct (Nat.compare n1 n) eqn:Hn.
    * assert (n1 = n) by auto with facts.
      subst. simpl in *.
      assert (Hn0: Nat.leb n n = true) by auto with facts.
      rewrite Hn0. replace (n - n) with 0 by lia. simpl.
      assert (closed (t⟦ e0 ⟧ Σ) = true) by now apply expr_closed_term_closed.
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
    cbn in *. unfold subst1.
    inv_andb Hc. inv_andb Hok.
    erewrite <- type_to_term_subst with (nm:=nm);eauto with hints.
    f_equal. eapply IHe;eauto.
  + (* eTyLam *)
    cbn in *;f_equal;auto.
  + (* eLetIn *)
    cbn in *.
    unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
    rewrite type_to_term_subst with (nm:=nm);intuition;eauto with hints.
  + (* eApp *)
    change ((t⟦ eApp e1 e2 ⟧ Σ)) with ((mkApps (t⟦e1⟧Σ) [t⟦e2⟧Σ])) in *.
    cbn -[mkApps] in *. unfold is_true in *.
    repeat rewrite  Bool.andb_true_iff in *. destruct Hc as [Hce1 Hce2].
    rewrite subst_mkApps.
    change (tApp t⟦e1.[[(nm, e0)]] n1⟧Σ t⟦e2.[[(nm, e0)]] n1⟧ Σ) with
        (mkApps t⟦e1.[[(nm, e0)]] n1⟧Σ [t⟦e2.[[(nm, e0)]] n1⟧ Σ]).
    f_equal.
    eapply IHe1;intuition.
    simpl;f_equal;eapply IHe2;intuition.
  + (* eConstr *)
    simpl. destruct (resolve_constr Σ i n);auto.
  + (* eConst *)
    reflexivity.
  + (* eCase *)
    cbn in *. destruct p as [ind tys]. unfold is_true in *;simpl in *.
    repeat rewrite Bool.andb_true_iff in *. destruct Hc as [Hce1 Hce2].
    destruct (resolve_inductive Σ ind) eqn:Hres;auto.
    rewrite map_length. destruct (_ =? _)%nat eqn:Hnparams.
      cbn.
      repeat f_equal.
    * rewrite map_map.
       erewrite <- type_to_term_map with (Σ := Σ) by intuition.
       rewrite subst_mkApps. now rewrite map_map.
    * erewrite <- type_to_term_subst with (Σ := Σ) by intuition.
         apply commut_lift_subst.
    * eapply IHe; intuition.
    * rewrite_all map_map. simpl.
      unfold on_snd. destruct p as [p cs];simpl in *.
      apply map_ext_in.
      intros ctor Hin. destruct ctor as [s l0] eqn:Hconsr. unfold on_snd,trans_branch.
      unfold fun_prod,id. cbn. destruct (find _ _) eqn:Hfnd;simpl.
      ** eapply find_map with
             (p2 := (fun x => pName (fst x) =? s))
             (f:= fun x => ((fst x), (snd x){#|pVars (fst x)|+n1 := t⟦ e0 ⟧ Σ})) in Hfnd.
         rewrite map_map in Hfnd. simpl in Hfnd. unfold fun_prod,id. simpl.
         assert ( Hmap :
                    (map (fun x => (id (fst x), (t⟦snd x⟧ Σ) {#|pVars (fst x)|+n1 := t⟦e0⟧ Σ})) l) =
                    (map (fun x => (fst x, t⟦(snd x) .[[(nm,e0)]](#|pVars (fst x)| + n1) ⟧ Σ)) l)).
         { eapply forall_map_spec'. apply H. intros a Hin' Ha. f_equal.
           destruct Hok as [[[? ?] ?] Hty_ok].
           assert (iclosed_n (#|pVars (fst a)| + S n1) (snd a) = true) by
               now eapply forallb_forall with (x:=a) in Hce2.
           assert (ty_expr_env_ok [(nm, e0)] (#|pVars a.1| + n1) a.2 = true) by
               now eapply forallb_forall with (x:=a) in Hty_ok.
           apply Ha;auto with hints.
           replace (S (#|pVars (fst a)| + n1)) with
               (#|pVars (fst a)| + S n1) by lia.
           assumption. }
         rewrite <- Hmap. unfold id in *. rewrite Hfnd. simpl.
         rewrite map_length.
         destruct (Nat.eqb #|pVars (fst p0)| #|l0|) eqn:Hlen;simpl;auto.
         f_equal. unfold id.  rewrite subst_pat_to_lam.
         repeat f_equal.
         *** rewrite PeanoNat.Nat.eqb_eq in Hlen.
             rewrite combine_length. repeat rewrite map_length.
             rewrite Hlen. apply PeanoNat.Nat.min_id.
         *** rewrite map_rev. repeat rewrite map_map.
             destruct Hok as [[[? ?] ?] Hty_ok].
             destruct Hce1 as [[? ?] ?].
             f_equal. eapply type_to_term_map; eauto with hints.
         *** remember (combine _ _) as ls. rewrite rev_length, map_length.
                  assert (forallb (iclosed_ty (#|tys| + n1)) (map snd l0)).
                  { assert (forallb (constr_ok p) cs) by now eapply genv_ok_constrs_ok.
                    assert (forallb (iclosed_ty p) (map snd l0)) by now eapply constrs_ok_in.
                    rewrite Nat.eqb_eq in Hnparams. subst.
                    eapply forallb_impl_inner. eapply H1. intros. now eapply iclosed_ty_m_n. }
                  eapply inc_subst_closed. subst.
                  rewrite forallb_map. eapply forallb_snd;eauto with hints.
         *** intros. destruct a;easy.
      ** change (fun x : pat * term => pName (fst x) =? s) with
                                ((fun x : pat => pName x =? s) ∘ fst (B:=term)) in *.
         erewrite find_none_fst with (l1:=(map (fun x : pat × expr => (x.1, t⟦ x.2 ⟧ Σ)) l));eauto.
         now repeat rewrite map_map.
    * reflexivity.
  + (* eFix *)
    cbn in *. unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
    unfold map_def. simpl. repeat f_equal;intuition.
    rewrite commut_lift_subst. intuition. rewrite commut_lift_subst. intuition.
  + (* eTy *) simpl in *. eauto with hints.
Qed.

Lemma subst_term_subst_env e :
  forall v Σ nm,
    let ρ := nil # [nm ~> of_val_i v] in
    genv_ok Σ ->
    ty_expr_env_ok ρ 0 e ->
    val_ok Σ v ->
    iclosed_n 1 e = true ->
    (t⟦e⟧ Σ) {0:=t⟦ of_val_i v ⟧ Σ} =
    (t⟦e.[ρ]⟧ Σ).
Proof.
  simpl;intros.
  assert (iclosed_n 0 (of_val_i v) = true) by now eapply of_value_closed.
  now apply subst_term_subst_env_rec.
Qed.

Lemma subst_env_ty_closed_n_eq n m ty ρ :
  iclosed_ty n ty ->
  subst_env_i_ty (m + n) ρ ty = ty.
Proof.
  revert n m ρ.
  induction ty;intros;simpl in *;unfold is_true in *;repeat rewrite Bool.andb_true_iff in *;intuition;eauto.
  + f_equal. now replace (S (m + n)) with (m + S n) by lia.
  + destruct (Nat.leb (m + n0)) eqn:Hmn1; leb_ltb_to_prop;try lia;easy.
Qed.

Hint Resolve subst_env_ty_closed_n_eq : hints.

Lemma map_subst_env_ty_closed n m ρ l0 :
  forallb (iclosed_ty n) l0 ->
  map (subst_env_i_ty (m + n) ρ) l0 = l0.
Proof.
  intros H. revert dependent n. revert m ρ. induction l0;intros m ρ n Hc;simpl;auto.
  simpl in *. inv_andb Hc. f_equal; eauto with hints.
Qed.

Lemma subst_env_i_closed_n_eq :
  forall (e : expr) (n m : nat) (ρ : env expr),
    iclosed_n n e = true ->
    e.[ρ](m+n) = e.
Proof.
  intros e.
  induction e using expr_ind_case;intros n1 m1 ρ Hc;simpl in *;
    repeat rewrite Bool.andb_true_iff in *;eauto with hints.
  + simpl in *. destruct (Nat.leb (m1 + n1)) eqn:Hmn1; leb_ltb_to_prop;try lia;easy.
  + simpl in *. f_equal. eapply subst_env_ty_closed_n_eq;intuition.
    now replace (S (m1 + n1)) with (m1 + S n1) by lia.
  + simpl in *. f_equal. replace (S (m1 + n1)) with (m1 + S n1) by lia. easy.
  + simpl in *. f_equal;replace (S (m1 + n1)) with (m1 + S n1) by lia;intuition;eauto with hints.
  + simpl in *. f_equal;replace (S (m1 + n1)) with (m1 + S n1) by lia;easy.
  + simpl in *. destruct p.
    assert (map (fun x : pat × expr => (x.1, x.2 .[ ρ] (#|pVars x.1| + (m1 + n1)))) l = l).
    { transitivity (map id l).
      eapply forall_map_spec';eauto.
      simpl. intros x Hin Hx. destruct x. unfold id. f_equal. simpl in *.
      replace (#|pVars p| + (m1 + n1)) with (m1 + (#|pVars p| + n1)) by lia.
      apply Hx. intuition. rewrite forallb_forall in *.
      rewrite Forall_forall in *.
      change e0 with (snd (p,e0)).
      change p with (fst (p,e0)). easy.
      apply map_id. }
    assert (map (subst_env_i_ty (m1 + n1) ρ) l0 = l0) by now eapply map_subst_env_ty_closed.
    repeat f_equal;intuition;eauto with hints.
  + simpl in *. f_equal;intuition. now replace (S (S (m1 + n1))) with (m1 + S (S n1)) by lia.
  + f_equal;auto with hints.
Qed.

Lemma subst_env_i_closed_eq :
  forall (e : expr) (n : nat) (ρ : env expr),
    iclosed_n 0 e = true ->
    e.[ρ]n = e.
Proof.
  intros;eapply subst_env_i_closed_n_eq with (m:=0);eauto.
  now apply iclosed_n_0.
Qed.

Lemma subst_env_ty_compose_1 k ρ nm e' ty :
  All (fun x => iclosed_n 0 (snd x) = true) ρ ->
  iclosed_n 0 e' = true ->
  subst_env_i_ty k (ρ # [nm ~> e']) ty = subst_env_i_ty k [(nm, e')] (subst_env_i_ty (S k) ρ ty).
Proof.
  revert k ρ nm e'.
  induction ty;intros ? ? ? ? Hfa Hc;simpl;try now f_equal.
  destruct n.
  * reflexivity.
  * simpl. destruct (k <=? n) eqn:Hkn.
    ** unfold lookup_ty. simpl. leb_ltb_to_prop. assert (k <= S n) by lia.
       prop_to_leb_ltb. rewrite H.
       leb_ltb_to_prop.
       assert (Hneq : S n - k <> 0) by lia.
       rewrite <- PeanoNat.Nat.eqb_neq in Hneq. rewrite Hneq.
       replace (S n - k - 1) with (n - k) by lia.
       replace (S n - S k) with (n - k) by lia.
       destruct (lookup_i ρ (n-k)) eqn:Hl.
       *** simpl.
           assert (iclosed_n 0 e).
           { eapply (All_lookup_i _ _ _ (fun x => iclosed_n 0 x) Hfa Hl). }
           destruct (expr_to_ty e) eqn:He.
           **** assert (iclosed_ty 0 t0).
                { destruct e;tryfalse. now inversion He;subst. }
                symmetry. eapply subst_env_ty_closed_n_eq with (m:=0). now eapply iclosed_ty_0.
           **** simpl. unfold lookup_ty in *. simpl. prop_to_leb_ltb. rewrite H.
                destruct k;auto;tryfalse.
                rewrite Nat.eqb_neq in *. assert (n-k<>0) by lia.
                destruct (n - k =? 0)%nat eqn:HH;tryfalse;auto. rewrite Nat.eqb_eq in *.
                leb_ltb_to_prop. lia.
       *** remember (S n) as m. simpl.
           prop_to_leb_ltb. rewrite H. unfold lookup_ty in *. simpl. now rewrite Hneq.
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
Qed.

Hint Resolve subst_env_ty_compose_1.

Lemma subst_env_compose_1 :
  forall (nm : Ast.ename) (e e1: expr) k (ρ : env expr),
    All (fun x => iclosed_n 0 (snd x) = true) ρ ->
    iclosed_n 0 e1 = true ->
    e.[ρ # [nm ~> e1]]k =
    (e.[ρ](1+k)).[nil # [nm ~> e1]]k.
Proof.
  intros nm.
  unfold inst_env_i,subst_env_i in *. simpl in *.
  induction e using expr_ind_case;intros e' k ρ Hfc Hc;
    simpl in *; repeat rewrite Bool.andb_true_iff in *;try f_equal;auto with hints.
  + simpl. destruct n.
    * reflexivity.
    * simpl;destruct (Nat.leb k n) eqn:Hkn.
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
             eapply (All_lookup_i _ _ _ (fun x => iclosed_n 0 x) Hfc Hl).
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
  + destruct p. simpl. rewrite map_map. f_equal;eauto. f_equal.
    eapply map_ext. intros;eapply subst_env_ty_compose_1;eauto.
    rewrite map_map. simpl.
    eapply forall_map_spec;eauto.
    eapply Forall_impl;eauto.
    intros a Ha. simpl in *. f_equal.
    replace (#|pVars (fst a)| + S k) with (S (#|pVars (fst a)| + k)) by lia.
    now apply Ha.
Qed.

Lemma subst_env_swap_app :
  forall (e: expr) (ρ1 ρ2 : env expr) n,
    All (fun x => iclosed_n 0 (snd x) = true) ρ1 ->
    All (fun x => iclosed_n 0 (snd x) = true) ρ2 ->
    (e.[ρ1](n+#|ρ2|)).[ρ2]n = e.[ρ2++ρ1]n.
Proof.
  induction ρ2.
  + intros. simpl. symmetry. rewrite <- subst_env_i_empty with (k:=n).
    f_equal. lia.
  + intros. simpl. destruct a.
    inversion H0. subst. clear H0.
    assert (All (fun x => iclosed_n 0 (snd x) = true) (ρ2++ρ1))
      by now apply All_app_inv.
    rewrite subst_env_compose_1 with (ρ := ρ2 ++ ρ1) by auto.
    rewrite subst_env_compose_1 with (k:=n) by auto.
    simpl.
    rewrite <-IHρ2;eauto.
    replace (n + S #|ρ2|) with (S n + #|ρ2|) by lia. reflexivity.
Qed.

(* TODO: this should be an instance of a more general lemma, and
   we will restate this in terms of parallel substitutions *)
Lemma subst_env_compose_2 :
  forall (nm1 nm2 : ename) (e e1 e2: expr) (ρ : env expr),
    All (fun x => iclosed_n 0 (snd x) = true) ρ ->
    iclosed_n 0 e1 = true ->
    iclosed_n 0 e2 = true ->
    e.[ρ # [nm1 ~> e1] # [nm2 ~> e2]] =
    (e.[ρ]2).[nil # [nm1 ~> e1] # [nm2 ~> e2]].
Proof.
  intros. change ((nm2, e2) :: (nm1, e1) :: ρ) with ([(nm2, e2);(nm1, e1)] ++ ρ).
  symmetry. eapply subst_env_swap_app;eauto.
Qed.

Remove Hints iclosed_n_geq: hints.
Remove Hints Bool.absurd_eq_true.

Open Scope nat.

Lemma lookup_i_app {A} (l1 l2 : env A) i :
  #|l1| <= i ->
  lookup_i (l1 ++ l2) i = lookup_i l2 (i - #|l1|).
Proof.
  revert l2 i.
  induction l1;intros.
  + simpl. now replace (i-0) with i by lia.
  + simpl. destruct a. simpl in *.
    destruct i.
    * exfalso;lia.
    * simpl. now replace (i-0) with i by lia.
Qed.

Lemma ty_env_ok_app_rec :
  forall (ty : type) n (ρ1 ρ2 : list (string × expr)),
    ty_env_ok n (ρ1 ++ ρ2) ty ->
    ty_env_ok (n+#|ρ1|) ρ2 ty.
Proof.
  induction ty;intros;auto.
  + simpl in *. now replace (S (n + #|ρ1|)) with (S n + #|ρ1|) by lia.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition.
  + cbn -[lookup_i] in *. destruct (n0 + #|ρ1| <=? n) eqn:Hn.
    * assert (Hleb : n0 <=? n = true) by (leb_ltb_to_prop; lia).
      rewrite Hleb in *. replace (n - (n0 + #|ρ1|)) with ((n - n0) - #|ρ1|) by lia.
      rewrite lookup_i_app in H by (leb_ltb_to_prop; lia). easy.
    * destruct (n0 <=? n) eqn:Hn0;auto.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition.
Qed.

Hint Resolve ty_env_ok_app_rec : hints.
Hint Resolve subst_env_compose_1 : hints.

Hint Extern 2 (iclosed_n _ (snd _) = _) => simpl : hints.
Hint Extern 2 (_ .[_] = _)=> simpl;eapply subst_env_compose_1 with (k:=0) : hints.
Hint Extern 2 (iclosed_n ?n _ = _)=> (match n with
                                    | O => fail
                                    | S _ => eapply iclosed_n_0
                                     end) : hints.

Lemma ty_expr_env_ok_app_rec :
  forall (e : expr) n (ρ1 ρ2 : list (string × expr)),
    ty_expr_env_ok (ρ1 ++ ρ2) n e ->
    ty_expr_env_ok ρ2 (n + #|ρ1|) e.
Proof.
  induction e using expr_ind_case;intros ? ? ? Hok;simpl in *;unfold is_true in *;
    repeat rewrite Bool.andb_true_iff in *;eauto with hints.
  + replace (S (n0 + #|ρ1|)) with (S n0 + #|ρ1|) by lia.
    intuition.
    now apply ty_env_ok_app_rec.
  + now replace (S (n0 + #|ρ1|)) with (S n0 + #|ρ1|) by lia.
  + intuition.
    now apply ty_env_ok_app_rec.
    now replace (S (n0 + #|ρ1|)) with (S n0 + #|ρ1|) by lia.
  + intuition.
  + intuition.
    eapply forallb_impl_inner;intros;eauto; now apply ty_env_ok_app_rec.
    now apply ty_env_ok_app_rec.
    cbn. apply forallb_Forall. apply forallb_Forall in H1.
    eapply Forall_impl_inner. apply H. simpl in *.
    eapply Forall_impl. 2 : { apply H1. } intros.
    now replace (#|pVars a.1| + (n + #|ρ1|)) with (#|pVars a.1| + n + #|ρ1|) by lia.
  + intuition.
    now apply ty_env_ok_app_rec. now apply ty_env_ok_app_rec.
    now replace (S (S (n1 + #|ρ1|))) with (S (S n1) + #|ρ1|) by lia.
  + now apply ty_env_ok_app_rec.
Qed.

Lemma iclosed_ty_expr_env_ok :
  forall (n : nat) (ρ : env expr) e,
    iclosed_n n e -> ty_expr_env_ok ρ n e.
Proof.
  intros. revert dependent n. revert ρ.
  induction e using expr_elim_case;intros ?? Hc;eauto.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition. eapply iclosed_ty_env_ok;eauto.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition. eapply iclosed_ty_env_ok;eauto.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition;eauto with hints.
    eapply forallb_impl_inner;intros;eauto; now apply iclosed_ty_env_ok.
    now apply iclosed_ty_env_ok.
    apply All_forallb. apply forallb_All in H1.
    eapply All_impl_inner. apply H. simpl in *.
    eapply All_impl. apply H1. intros.
    simpl in *. easy.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition;now apply iclosed_ty_env_ok.
  + now apply iclosed_ty_env_ok.
Qed.

Lemma ty_env_ok_subst_env k ρ1 ρ2 (ty : type) :
  ty_env_ok k (ρ1 ++ ρ2) ty ->
  AllEnv (iclosed_n 0) ρ2 ->
  ty_env_ok k ρ1 (subst_env_i_ty (k+#|ρ1|) ρ2 ty).
Proof.
  revert k ρ1 ρ2.
  induction ty;intros k ρ1 ρ2 Hok Hall;auto.
  + simpl in *. replace (S (k + #|ρ1|)) with (S k + #|ρ1|) by lia.
    eapply IHty;eauto.
  + simpl in *. unfold is_true in *; repeat rewrite Bool.andb_true_iff in *;intuition.
  + cbn -[lookup_i] in *. destruct (k + #|ρ1| <=? n) eqn:Hn.
    * assert (Hleb : k <=? n = true) by (leb_ltb_to_prop; lia).
      rewrite Hleb in *. replace (n - (k + #|ρ1|)) with ((n - k) - #|ρ1|) by lia.
      assert (#|ρ1| <= n - k) by (leb_ltb_to_prop;lia).
      rewrite lookup_i_app in Hok by assumption.
      unfold lookup_ty.
      destruct (lookup_i ρ2 (n - k - #|ρ1|)) eqn:Hlook.
      ** destruct e;tryfalse. simpl in *.
         eapply All_lookup_i in Hall;eauto.
         eapply iclosed_ty_env_ok.
         now eapply iclosed_ty_0.
      ** simpl. destruct (k<=? n);auto. rewrite lookup_i_length_false;auto.
         leb_ltb_to_prop;auto.
    * simpl in *;destruct (k <=? n) eqn:Hn0;auto.
      rewrite lookup_i_nth_error in *. rewrite nth_error_app1 in Hok by (leb_ltb_to_prop;lia).
      destruct (nth_error ρ1 (n - k)) eqn:Hnth;auto.
  + simpl in *. unfold is_true in *; repeat rewrite Bool.andb_true_iff in *;intuition.
Qed.

Lemma ty_expr_env_ok_subst_env k ρ1 ρ2 e :
  ty_expr_env_ok (ρ1 ++ ρ2) k e ->
  AllEnv (iclosed_n 0) ρ2 ->
  ty_expr_env_ok ρ1 k (e.[ρ2](k+#|ρ1|)).
Proof.
  revert k ρ1 ρ2.
  induction e using expr_elim_case;intros;eauto with hints.
  + simpl in *.
    destruct (k + #|ρ1| <=? n) eqn:Hkn;eauto.
    destruct (lookup_i ρ2 (n - (k + #|ρ1|))) eqn:Hl;auto.
    eapply All_lookup_i in X;eauto. simpl.
    eapply iclosed_ty_expr_env_ok.
    now eapply iclosed_n_0.
  + simpl in *. inv_andb H. split_andb.
    now eapply ty_env_ok_subst_env.
    replace (S (k + #|ρ1|)) with (S k + #|ρ1|) by lia.
    eapply IHe;eauto.
  + simpl in *. eapply IHe;eauto.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition. eapply ty_env_ok_subst_env;eauto.
  + simpl in *. unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition.
  + simpl in *. destruct p. simpl in *.
    unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition;eauto with hints.
    * rewrite forallb_map. eapply forallb_impl_inner;eauto.
      intros. eapply ty_env_ok_subst_env;eauto.
    * eapply ty_env_ok_subst_env;eauto.
    * apply All_forallb. apply All_map.
      intros. unfold compose. simpl in *.
      eapply forallb_All in H2.
      eapply (All_impl_inner _ _ _ H2).
      eapply All_impl. apply H. intros. simpl in *.
      replace (#|pVars x.1| + (k + #|ρ1|)) with (#|pVars x.1| + k + #|ρ1|) by lia.
      eapply H0;eauto.
  + simpl in *.
    unfold is_true in *. repeat rewrite Bool.andb_true_iff in *.
    intuition;eapply ty_env_ok_subst_env;eauto.
  + eapply ty_env_ok_subst_env;eauto.
Qed.

Hint Resolve ty_expr_env_ok_app_rec : hints.

(** ** Environment substitution commutes with PCUIC substitution (In the paper: Lemma 1.) *)
Lemma subst_term_subst_env_par_rec :
  forall Σ (l : env expr) e k,
  genv_ok Σ ->
  ty_expr_env_ok l k e ->
  iclosed_n (k+#|l|) e = true ->
  All (fun x : string * expr => iclosed_n 0 (snd x) = true) l ->
  subst (map (fun x => expr_to_term Σ (snd x)) l) k (t⟦e⟧ Σ) = (t⟦e.[l]k⟧ Σ).
Proof.
  intros until l.
  induction l using MCList.rev_ind;intros e k Hgeok Hok Hc Hall.
  + simpl in *. unfold subst_env_i.
    rewrite <- subst_env_i_empty. rewrite subst_empty.
    reflexivity.
  + unfold subst_env_i. destruct x as [nm e0]. simpl in *.
    apply All_app in Hall as [Hl He0]. inversion He0;subst;clear He0. simpl in *.
    unfold subst_env_i. rewrite map_app. simpl.
    rewrite subst_app_simpl. rewrite map_length. simpl.
    rewrite app_length in *. simpl in *.
    replace (#|l| + 1) with (1 + #|l|) in Hc by lia.
    replace (k + (1 + #|l|)) with (1+ k + #|l|) in Hc by lia.
    rewrite subst_term_subst_env_rec with (e:=e)(nm:=nm) by eauto with hints.
    rewrite <- subst_env_swap_app with (n:=k) by eauto.
    simpl. replace (1 + k + #|l|) with (k + #|l| + 1) in * by lia.
    eapply IHl;eauto with hints.
    eapply ty_expr_env_ok_subst_env;eauto with hints.
Qed.

Lemma subst_term_subst_env_par :
  forall Σ (l : env expr) e,
  genv_ok Σ ->
  ty_expr_env_ok l 0 e ->
  iclosed_n #|l| e = true ->
  All (fun x : string * expr => iclosed_n 0 (snd x) = true) l ->
  subst (map (fun x => expr_to_term Σ (snd x)) l) 0 (t⟦e⟧ Σ) = (t⟦e.[l]⟧ Σ).
Proof.
  intros. eapply subst_term_subst_env_par_rec;eauto.
Qed.

Import Basics.
Open Scope program_scope.

Open Scope string.

Lemma pat_match_succeeds {A : Type } cn arity (vals : list A) brs e
      assig n :
    match_pat cn n arity vals brs = Ok (assig, e) ->
    { p | find (fun x => pName (fst x) =? cn) brs = Some (p,e)
         /\ n+#|arity| = n+#|p.(pVars)| /\ #|vals| = n+#|p.(pVars)|
         /\ assig = combine p.(pVars) (skipn n vals)}.
Proof.
  intros Hpm.
  unfold match_pat in Hpm. simpl in Hpm.
  destruct (find (fun x => pName (fst x) =? cn) brs) eqn:Hfnd;tryfalse.
  destruct p as [p' e0]. simpl in *.
  destruct (Nat.eqb #|vals| (n+#|pVars p'|)) eqn:Hlength;tryfalse.
  destruct (Nat.eqb #|vals| (n+#|arity|)) eqn:Hlength';tryfalse.
  simpl in *.
  inversion Hpm. subst. clear Hpm.
  exists p'. rewrite PeanoNat.Nat.eqb_eq in *.
  repeat split;auto. now rewrite Hlength in *.
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

Lemma All_snd_combine {A B} (l1 : list A) (l2 : list B)
      (p : B -> Type) : All p l2 -> All (p ∘ snd) (combine l1 l2).
Proof.
  revert l1.
  induction l2; intros ns H.
  + destruct ns;simpl;constructor.
  + inversion H. subst. destruct ns;unfold compose;simpl. constructor.
    constructor; unfold compose;simpl;auto.
Qed.


Lemma All_env_ok (ρ : env val) (l : list val) (ns : list ename) Σ :
  All (val_ok Σ) l -> env_ok Σ (combine ns l).
Proof.
  apply All_snd_combine.
Qed.

Hint Constructors All.

Lemma eval_ge_val_ok n ρ Σ e v :
  AllEnv (ge_val_ok Σ) ρ ->
  expr_eval_i Σ n ρ e = Ok v ->
  ge_val_ok Σ v.
Proof.
  revert dependent ρ. revert dependent v. revert dependent e.
  induction n;intros e v ρ Hok He;tryfalse.
  destruct e;unfold expr_eval_i in *;simpl in *;inversion He;tryfalse.
  + destruct (lookup_i ρ n0) eqn:Hlook;simpl in *;inversion He;subst.
    now eapply All_lookup_i with (e:=v).
  + destruct (eval_type_i 0 ρ t0);tryfalse. simpl in *. inversion H0.
    simpl. destruct (valid_env _ _ _);tryfalse.
    inversion He. now apply All_forallb.
  + simpl in *. destruct (valid_env _ _ _);tryfalse. inversion He. now apply All_forallb.
  + destruct (expr_eval_general _ _ _ _ e2) eqn:He1;tryfalse.
    destruct (eval_type_i _ _ _);tryfalse.
    assert (ge_val_ok Σ v0) by now eapply IHn.
    eapply IHn with (e:=e3) (ρ:=(e1, v0) :: ρ);eauto with hints.
  + destruct (expr_eval_general _ _ _ _ e1) eqn:He1;tryfalse.
      2 : { try (destruct  (expr_eval_general _ _ _ _ e2) eqn:He2);tryfalse. }
    destruct v0;try destruct c;
        destruct  (expr_eval_general _ _ _ _ e2) eqn:He2;tryfalse.
    * inversion He;subst;clear He. simpl.
      assert (ge_val_ok Σ (vConstr i e l)) by eauto.
      assert (ge_val_ok Σ v0) by eauto.
      simpl in *. destruct (resolve_constr Σ i e);eauto.
      simpl in *. rewrite forallb_app. split_andb;try split_andb;eauto.
    * (* destruct (expr_eval_general n _ _ _ e0) eqn:He0;tryfalse. *)
      (* inversion He;subst. *)
      assert (ge_val_ok Σ (vClos e _ cmLam t0 t1 _)) by eauto.
      assert (ge_val_ok Σ v0) by eauto.
      simpl in *.
      eapply IHn with (ρ:=(e0, v0) :: e);eauto with hints.
      apply forallb_All. simpl. now split_andb.
    * destruct v0;tryfalse.
      remember (e # [e4 ~> _] # [ e0 ~> _]) as ρ'.
      eapply IHn with (e:=e3) (ρ:=ρ'); try eapply He0;eauto.
      assert (Hok_fix : ge_val_ok Σ (vClos e _ (cmFix _) t0 t1 _)) by eauto.
      simpl in Hok_fix. apply forallb_Forall in Hok_fix.
      subst. unfold AllEnv,compose. apply Forall_All.
      eauto with hints.
    * assert (ge_val_ok Σ (vTyClos e e0 e3)) by eauto.
      assert (ge_val_ok Σ v0) by eauto.
      simpl in *.
      eapply IHn with (ρ:=(e0, v0) :: e);eauto with hints.
      apply forallb_All. simpl. now split_andb.
    * destruct (expr_eval_general _ _ _ _ e2) eqn:He2;tryfalse.
  + destruct (resolve_constr Σ i e) eqn:Hres;tryfalse. inversion He.
    simpl. now rewrite Hres.
  + destruct p as [ind e1].
    destruct (forallb _ l);tryfalse.
    destruct (eval_type_i _ _ t0);tryfalse;simpl in *.
    destruct (monad_utils.monad_map) eqn:Hmm;tryfalse.
    destruct (expr_eval_general _ _ _ _ e) eqn:He';tryfalse.
    destruct v0;tryfalse.
    destruct (string_dec _ _);tryfalse;subst.
    destruct (resolve_constr Σ i e0) eqn:Hres;tryfalse.
    destruct p as [n_i tys]. destruct n_i.
    destruct ((n0 =? #|e1|)%nat);tryfalse.
    destruct (match_pat e0 _ tys _ _) eqn:Hpm;tryfalse.
    destruct p as [assign e2].
    apply pat_match_succeeds in Hpm. destruct Hpm as [pt Htmp].
    destructs Htmp. subst.
    assert (Hok_constr : ge_val_ok Σ (vConstr i _ l1))
      by now eapply IHn with (e:=e).
    simpl in Hok_constr. destruct (resolve_constr Σ i e0) eqn:Hres';tryfalse.
    assert (Hok_l2 :
              AllEnv (fun x => ge_val_ok Σ x = true) (rev (combine (pVars pt) (skipn n0 l1)))).
    { apply All_rev. simpl in Hok_constr. apply forallb_Forall in Hok_constr. simpl in *.
      apply All_snd_combine. apply Forall_All. now apply Forall_skipn. }
    eapply IHn with (ρ := (rev (combine (pVars pt) ((skipn _ l1))) ++ ρ)%list);eauto.
    apply All_app_inv;eauto.
  + destruct (valid_env _ _ _);tryfalse.
    destruct (eval_type_i 0 ρ t0);tryfalse;simpl in *.
    destruct (eval_type_i 0 ρ t1);tryfalse;simpl in *.
    inversion H0. simpl.
    inversion He. now apply All_forallb.
  + destruct (eval_type_i 0 ρ t0);tryfalse;simpl in *.
    now inversion He.
Qed.

Open Scope list.
Lemma env_ok_concat Σ ρ1 ρ2 : env_ok Σ ρ1 -> env_ok Σ ρ2 -> env_ok Σ (ρ1 ++ ρ2).
Proof.
  intros Hok1 Hok2.
  apply All_app_inv;auto.
Qed.

Lemma rev_env_ok ρ Σ : env_ok Σ ρ -> env_ok Σ (rev ρ).
Proof.
  intros Hok. now apply All_rev.
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
  induction v using val_elim_full;intros Hok.
  + simpl. inversion Hok;subst;clear Hok.
    destruct (resolve_constr Σ i n) eqn:Hres;tryfalse.
    inversion H0;subst. simpl in *.
    apply All_forallb. eapply All_impl_inner;eauto.
  + simpl. apply All_forallb.
    inversion Hok;subst;clear Hok;eapply All_impl_inner;eauto.
  + simpl in *. inversion Hok;subst.
    eapply All_forallb. eapply All_impl_inner. apply X0. unfold compose.
    eapply All_impl. apply X.
    intros;unfold compose in *;cbn in *. easy.
  + now inversion Hok;subst.
Qed.

Lemma env_ok_ForallEnv_ge_val_ok ρ Σ :
  env_ok Σ ρ -> AllEnv (ge_val_ok Σ) ρ.
Proof.
  induction ρ.
  + intros. constructor.
  + intros Hok. inversion Hok;subst.
    constructor.
    * now apply val_ok_ge_val_ok.
    * now eapply IHρ.
Qed.

Hint Resolve eval_ty_closed type_eval_value.

Lemma Forall_monad_map_some {A B} {f} {xs : list A} {ys : list B} :
  monad_utils.monad_map f xs = Ok ys -> Forall (fun x => exists v, f x = Ok v) xs.
Proof.
  revert ys.
  induction xs;intros;simpl in *;auto.
  destruct (f _) eqn:Hf;tryfalse. destruct (monad_utils.monad_map _ _) eqn:Hmm;tryfalse.
  constructor;eauto.
Qed.

Lemma eval_ty_env_ok :
  forall (ty : type) (ρ : env val) (n : nat) (ty_v : type),
    eval_type_i n ρ ty = Some ty_v -> ty_env_ok n (exprs ρ) ty = true.
Proof.
  induction ty;intros.
  + easy.
  + simpl in *. destruct (eval_type_i (S n) ρ ty) eqn:Hty;tryfalse. inversion H. subst.
    eauto.
  + simpl in *.
    destruct (eval_type_i n ρ ty2) eqn:Hty2;tryfalse.
    destruct (eval_type_i n ρ ty1) eqn:Hty1;tryfalse.
    split_andb;eauto.
  + tryfalse.
  + simpl in *.
    destruct (n0 <=? n) eqn:Hn0;auto.
    rewrite lookup_i_nth_error in H. rewrite lookup_i_nth_error.
    rewrite nth_error_map.
    destruct (nth_error ρ (n - n0));simpl in *;auto. destruct (p.2);tryfalse.
    inversion H. reflexivity.
  + simpl in *.
    destruct (eval_type_i n ρ ty2) eqn:Hty2;tryfalse.
    destruct (eval_type_i n ρ ty1) eqn:Hty1;tryfalse.
    split_andb;eauto.
Qed.


Lemma eval_ty_expr_env_ok :
  forall (n : nat) (Σ : global_env) (e : expr) (ρ : env val) (v0 : val),
    iclosed_n #|ρ| e = true ->
    (eval (n, Σ, ρ, e)) = Ok v0 -> ty_expr_env_ok (exprs ρ) 0 e.
Proof.
  induction n;intros Σ e ρ v0 Hc He;tryfalse.
  + destruct e;eauto.
    * simpl in *. destruct (eval_type_i 0 _ t0) eqn:Ht0;simpl in *;tryfalse.
      inversion He;subst;clear He. split_andb.
      ** now eapply eval_ty_env_ok.
      ** unfold is_true; repeat rewrite Bool.andb_true_iff in *.
         destruct (valid_env ρ 1 e0) eqn:Hve0;tryfalse.
         now eapply valid_env_ty_expr_env_ok.
    * simpl in *. destruct (valid_env _ _ _) eqn:Hve0;tryfalse. inversion He;subst;clear He.
      now eapply valid_env_ty_expr_env_ok.
    * simpl in *.
      destruct (eval (n, Σ, ρ, e2)) eqn:He2;tryfalse.
      destruct (eval_type_i 0 ρ t0) eqn:Hty;tryfalse;simpl in *.
      unfold is_true; repeat rewrite Bool.andb_true_iff in *.
      assert (ty_expr_env_ok (exprs (ρ # [e1 ~> v])) 0 e3 = true) by
             (destruct Hc as [[? ?] ?];repeat split;eauto with hints; eapply IHn;eauto ).
      simpl in H. destruct Hc as [[? ?] ?].
      repeat split.
      ** eapply IHn;eauto.
      ** eapply eval_ty_env_ok;eauto.
      ** now eapply ty_expr_env_ok_app_rec with (n:=0) (ρ1:=[(e1,of_val_i v)]).
    * simpl in *. inv_andb Hc.
      destruct (eval (n, Σ, ρ, e2)) eqn:He2;tryfalse.
      destruct (eval (n, Σ, ρ, e1)) eqn:He1;tryfalse.
      destruct v1;inversion He;subst;tryfalse;split_andb; eapply IHn;eauto.
    * simpl in *.
      destruct p.
      destruct (forallb (fun x : pat × expr => valid_env ρ #|pVars x.1| x.2) l) eqn:Hl;tryfalse.
      destruct (eval_type_i _ _ t0) eqn:Ht0;tryfalse;simpl in *.
      destruct (monad_utils.monad_map _ _) eqn:Hind;tryfalse.
      unfold is_true in *;
        repeat rewrite  Bool.andb_true_iff in *.
      destruct (eval (n, Σ, ρ, e)) eqn:He';tryfalse.
      destruct v;tryfalse.
      destruct (string_dec _ _);tryfalse.
      destruct (resolve_constr Σ _ _);tryfalse.
      destruct p. destruct p.
      destruct ((_ =? _)%nat);tryfalse.
      destruct (match_pat e0 _ _ _ _) eqn:Hp;tryfalse.
      destruct p. repeat split.
      ** eapply Forall_forallb;eauto. eapply (Forall_monad_map_some Hind);eauto.
         intros x H;simpl in *. destruct H. apply option_to_res_ok in H.
         now eapply eval_ty_env_ok.
      ** now eapply eval_ty_env_ok.
      ** destruct Hc as [[??]?];eapply IHn;eauto.
      ** intuition.
         eapply (forallb_impl_inner Hl);intros;eauto. simpl in *.
         replace (_ + 0) with #|pVars x.1| by lia.
         now apply valid_env_ty_expr_env_ok.
    * simpl in *.
      destruct (valid_env ρ 2 e1) eqn:Hve1;tryfalse.
      destruct (eval_type_i 0 ρ t0) eqn:Ht0;tryfalse.
      destruct (eval_type_i 0 ρ t1) eqn:Ht1;tryfalse.
      cbn in *. inversion He.
      unfold is_true in *;
        repeat rewrite  Bool.andb_true_iff in *. intuition.
      now eapply eval_ty_env_ok. now eapply eval_ty_env_ok.
      now eapply valid_env_ty_expr_env_ok.
    * simpl in *.
      destruct (eval_type_i 0 ρ t0) eqn:Ht0;tryfalse.
      now eapply eval_ty_env_ok.
Qed.

Hint Resolve eval_ty_expr_env_ok eval_ty_env_ok : hints.

(** ** Evaluation gives well-formed values (In the paper: Lemma 2) *)
Lemma eval_val_ok n ρ Σ e v :
  ty_expr_env_ok (exprs ρ) 0 e ->
  env_ok Σ ρ ->
  iclosed_n #|ρ| e ->
  expr_eval_i Σ n ρ e = Ok v ->
  val_ok Σ v.
Proof.
  revert dependent ρ. revert dependent v. revert dependent e.
  induction n;intros e v ρ Hty_ok Hok Hc He;tryfalse.
  destruct e.
  + unfold expr_eval_i in *. simpl in *.
    destruct (lookup_i_length _ _ Hc) as [x Hsome].
    rewrite Hsome in He. simpl in *. inversion He;subst;clear He.
    now eapply All_lookup_i.
  + tryfalse.
  + unfold expr_eval_i in *. simpl. simpl in He.
    destruct (eval_type_i 0 ρ t0) eqn:He_ty;tryfalse. simpl in *.
    destruct (valid_env ρ 1 e0);tryfalse.
    inversion He.
    inv_andb Hc. inv_andb Hty_ok.
    constructor;eauto with hints;subst.
  + unfold expr_eval_i in *. simpl. simpl in He,Hc.
    destruct (valid_env _ _ _) eqn:Hve;tryfalse. inversion He;subst. constructor;eauto.
  + unfold expr_eval_i in *. simpl. simpl in He,Hc.
    destruct (expr_eval_general _ _ _ _ e2) eqn:He1;tryfalse.
    destruct (eval_type_i 0 ρ t0) eqn:He_ty;tryfalse. simpl in *.
    unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
    destruct Hc as [[??]?].
    destruct Hty_ok as [[??]?].
    assert (env_ok Σ ((e1, v0) :: ρ)) by (eauto 6 with hints).
    assert (ty_expr_env_ok (exprs (ρ # [e1 ~> v0])) 0 e3) by
        (eapply eval_ty_expr_env_ok;eauto with hints).
    eapply IHn with (ρ:=ρ # [e1 ~> v0]);eauto with hints.
  + simpl in Hc. inv_andb Hc.
    autounfold with facts in *. simpl in He.
    destruct (expr_eval_general _ _ _ _ e2) eqn:He2;tryfalse.
    destruct (expr_eval_general _ _ _ _ e1) eqn:He1;tryfalse.
    destruct v1;try destruct c;tryfalse.
    * inversion_clear He.
      assert (Hge_ok : ge_val_ok Σ (vConstr i _ l)) by
          (eapply eval_ge_val_ok;[now apply env_ok_ForallEnv_ge_val_ok | eauto]).
      assert (Hok_constr : val_ok Σ (vConstr i e l)) by eauto with hints.
      simpl in Hge_ok. destruct (resolve_constr Σ i _) eqn:Hres;tryfalse.
      inversion Hok_constr. subst. clear Hok_constr.
      econstructor;eauto. apply All_app_inv;eauto with hints.
    * simpl in *. unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
      assert (Hok_v0 : val_ok Σ v0) by now eapply IHn.
      assert (Hok_lam : val_ok Σ (vClos e _ cmLam t0 t1 _)) by now eapply IHn with (e:=e1).
      inversion Hok_lam. subst. clear Hok_lam.
      eapply IHn with (e:=e3) (ρ:=(e0, v0) :: e);eauto with hints.
      eapply eval_ty_expr_env_ok;eauto.
    * destruct v0;tryfalse.
      assert (Hok_fix : val_ok Σ (vClos e _ (cmFix _) t0 t1 _)) by
          (eapply IHn with (ρ:=ρ) (e:=e1);eauto with hints).
      inversion Hok_fix;subst.
      eapply IHn with (ρ:=((_, vConstr i _ l) :: (_, vClos e _ (cmFix _) t0 t1 _) :: e));
        eauto 8 with hints.
    * simpl in *. unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
      assert (Hok_v0 : val_ok Σ v0) by now eapply IHn.
      assert (Hok_lam : val_ok Σ ((vTyClos _ _ _))) by now eapply IHn with (e:=e1).
      inversion Hok_lam. subst. clear Hok_lam.
      eapply IHn with (e:=e3) (ρ:=(_, v0) :: e);eauto with hints.
      eapply eval_ty_expr_env_ok;eauto.
  + unfold expr_eval_i in *. simpl in *.
    destruct (resolve_constr _ _ _) eqn:Hres;inversion He;tryfalse;eauto with hints.
  + tryfalse.
  + unfold expr_eval_i in *. simpl. simpl in He.
    simpl in Hc. unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
    destruct p as [ind e1].
    destruct (forallb (fun x : pat × expr => valid_env _ _ _) l) eqn:Hl;tryfalse.
    destruct (eval_type_i _ _ _) eqn:Hety;tryfalse. simpl in *.
    destruct (monad_utils.monad_map) eqn:Hmm;tryfalse.
    destruct (expr_eval_general _ _ _ _ e) eqn:He';tryfalse.
    destruct v0;tryfalse. destruct (string_dec ind i);tryfalse;subst.
    destruct (resolve_constr _ _ _) eqn:Hres;tryfalse.
    destruct p as [nn tys]. destruct nn as [n1 n2].
    destruct ((n1 =? #|e1|)%nat) eqn:Hnparams;tryfalse.
    destruct (match_pat _ _ _ _) eqn:Hpm;tryfalse.
    destruct p as [assign e2].
    apply pat_match_succeeds in Hpm. destruct Hpm as [pt Htmp].
    destructs Htmp. subst. destruct Hc as [[[??]?]?].
    assert (ty_expr_env_ok (exprs ρ) 0 e = true) by now eapply eval_ty_expr_env_ok.
    assert (Hok_constr : val_ok Σ (vConstr i e0 l1)) by (eapply IHn with (ρ:=ρ)(e:=e);eauto).
    inversion Hok_constr;subst;clear Hok_constr.

    assert (Hok_l2 : env_ok Σ (rev (combine (pVars pt) (skipn n1 l1)))).
    { apply rev_env_ok;apply All_env_ok;eauto;eapply All_skipn;eauto. }

    assert (iclosed_n #|rev (combine (pVars pt) (skipn n1 l1)) ++ ρ| e2 = true).
    { rewrite app_length. rewrite rev_length,combine_length,skipn_length.
      replace (min #|pVars pt| (#|l1| - n1)) with #|pVars pt| by lia.
      now specialize (find_forallb _ H H5) as Hc. }
    eapply IHn with (ρ := (rev (combine (pVars pt) (skipn n1 l1)) ++ ρ));eauto.
    eapply eval_ty_expr_env_ok with (ρ := (rev (combine (pVars pt) (skipn n1 l1)) ++ ρ));eauto.
    apply env_ok_concat;auto.
  + unfold expr_eval_i in *. simpl in *.
    unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
    destruct (valid_env _ _ _);tryfalse.
    destruct (eval_type_i _ _ t0) eqn:Hty0;tryfalse;simpl in *.
    destruct (eval_type_i _ _ t1) eqn:Hty1;tryfalse;simpl in *.
    destruct Hc as [[??]?].
    destruct Hty_ok as [[??]?].
    inversion He; eauto 6 with hints.
  + simpl in *.
    destruct (eval_type_i _ _ t0) eqn:Hty0;tryfalse;simpl in *. inversion He;subst.
    eauto with hints.
Qed.


Lemma from_vConstr_not_lambda :
  forall (Σ : global_env) (i : Ast.inductive) (n0 : ename) (na : BasicAst.name) (t0 b : term) l,
    tLambda na t0 b = t⟦ of_val_i (vConstr i n0 l) ⟧ Σ -> False.
Proof.
  intros Σ i n0 na t0 b l H.
  induction l using MCList.rev_ind.
  + simpl in H. destruct (resolve_constr Σ i n0);tryfalse.
  + simpl_vars_to_apps in H.
    destruct (t⟦ vars_to_apps (eConstr i n0) (map of_val_i l) ⟧ Σ);tryfalse.
Qed.


Lemma tFix_eq_inv f l Σ e :
  t⟦e⟧Σ = tFix f l -> exists fixname var ty1 ty2 b, e = eFix fixname var ty1 ty2 b.
Proof.
  destruct e;intros H1;try easy.
  + simpl in *. now destruct (resolve_constr Σ i _).
  + simpl in *. destruct p as [ty1 i1];tryfalse.
    destruct (resolve_inductive Σ _);tryfalse.
    destruct ((_ =? _)%nat);tryfalse.
  + simpl in *. inversion H1. repeat eexists;eauto.
  + simpl in *. inversion H1. destruct t0;tryfalse.
Qed.

Lemma fix_not_constr_of_val {Σ mf m i nm vs} :
  tFix mf m = t⟦of_val_i (vConstr i nm vs)⟧Σ -> False.
Proof.
  intros H.
  simpl in *.
  induction vs using MCList.rev_ind.
  + simpl in *. destruct (resolve_constr Σ i nm);tryfalse.
  + simpl in *. simpl_vars_to_apps in H; tryfalse.
Qed.

Lemma fix_not_lambda_of_val {e e1 ty1 ty2 Σ mf n idx} :
  tFix mf idx = t⟦ of_val_i (vClos e n cmLam ty1 ty2 e1) ⟧ Σ -> False.
Proof.
  intros H. simpl in *. inversion H.
Qed.

Lemma lambda_not_fix_of_val {e e1 ty ty1 ty2 Σ nm nm0 nm1 b } :
  tLambda nm ty b = t⟦ of_val_i (vClos e nm0 (cmFix nm1) ty1 ty2 e1) ⟧ Σ -> False.
Proof.
  intros H. simpl in *. inversion H.
Qed.

Lemma forall_Forall {A : Type} (P : A -> Prop) (l : list A) :
  (forall a, P a) -> Forall P l.
Proof.
  intros H.
  induction l;constructor;auto.
Qed.

Hint Resolve eval_val_ok of_value_closed : hints.

Lemma closed_exprs n (ρ : env val) Σ :
  env_ok Σ ρ ->
  All (fun x => iclosed_n n (snd x) = true) (exprs ρ).
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

Lemma mkApps_atom_inv l1 l2 t1 t2 :
  PcbvCurr.atom t1 ->
  PcbvCurr.atom t2 ->
  mkApps t1 l1 = mkApps t2 l2 ->
  l1 = l2 /\ t1 = t2.
Proof.
  intros H1 H2 Hmk.
  revert dependent t1.
  revert dependent t2.
  revert dependent l2.
  induction l1 using MCList.rev_ind;intros;destruct l2 using MCList.rev_ind.
  + inversion Hmk. easy.
  + simpl in *. subst. rewrite mkApps_unfold in *;tryfalse.
  + simpl in *. subst. rewrite mkApps_unfold in *;tryfalse.
  + simpl in *. repeat rewrite mkApps_unfold in *.
    inversion Hmk. specialize (IHl1 _ _ H2 _ H1 H0). intuition;auto.
Qed.

Lemma mkApps_constr_inv ind l1 l2 n1 n2 u1 u2:
  mkApps (tConstruct ind n1 u1) l1 = mkApps (tConstruct ind n2 u2) l2 ->
  l1 = l2 /\ n1 = n2 /\ u1 = u2.
Proof.
  intros H.
  assert (l1=l2 /\ tConstruct ind n1 u1 = (tConstruct ind n2 u2)) by now apply mkApps_atom_inv.
  now intuition.
Qed.

Lemma nth_error_map_exists {A B} (f : A -> B) (l : list A) n p:
  nth_error (map f l) n = Some p ->
  exists p0 : A, p = f p0.
Proof.
  intros H.
  revert dependent l.
  induction n;simpl in *;intros l H;destruct l eqn:H1;inversion H;eauto.
Qed.

Hint Resolve env_ok_concat All_env_ok rev_env_ok : hints.

Lemma of_val_closed_0 e ρ :
  All (fun e0 : string * expr => iclosed_n 0 (snd e0) = true) (exprs ρ) ->
  iclosed_n 0 (e.[exprs ρ]) = true -> iclosed_n #|ρ| e.
Proof.
  intros H ?.
  replace #|ρ| with (#|exprs ρ|) by now apply map_length.
  eauto with hints.
Qed.

Hint Resolve map_length of_val_closed_0 val_ok_ge_val_ok rev_length
  subst_env_compose_1 subst_env_compose_2 : hints.

Hint Constructors PcbvCurr.value : hints.

Open Scope string.

Lemma mkApps_nonempty_neq args t f :
  #|args| > 0 ->
  PcbvCurr.atom t ->
  mkApps f args = t -> False.
Proof.
  intros Hargs Hatom.
  destruct args using MCList.rev_ind.
  + simpl in *;lia.
  + rewrite mkApps_unfold. now destruct t.
Qed.

Lemma closed_exprs_len_r2l : forall (e : expr) (n : nat) (ρ : env val),
    iclosed_n (n + #|ρ|) e = true -> iclosed_n (n + #|exprs ρ|) e = true.
Proof.
  intros. now apply closed_exprs_len_iff.
Qed.

Hint Resolve 0 closed_exprs_len_r2l : hints.

Hint Extern 1 (iclosed_n (#|_|) _ = _) =>
eapply closed_exprs_len_iff with (n:=0) : hints.

Definition not_stuck : term -> bool :=
  fun t => let (f, args) := decompose_app t in
         negb (PcbvCurr.isStuckFix f args).

Hint Constructors PcbvCurr.eval : hints.

Hint Resolve PcbvCurr.value_final : hints.

Lemma vars_to_apps_constr_not_lambda ind cn l Σ:
  ~~ isLambda (t⟦vars_to_apps (eConstr ind cn) l⟧Σ).
Proof.
  destruct l using MCList.rev_ind.
  + simpl. now destruct (resolve_constr Σ ind cn).
  + simpl. now simpl_vars_to_apps.
Qed.

Lemma vars_to_apps_constr_not_fix_app ind cn l Σ:
  ~~ PcbvCurr.isFixApp (t⟦vars_to_apps (eConstr ind cn) l⟧Σ).
Proof.
  destruct l using MCList.rev_ind.
  + simpl. now destruct (resolve_constr Σ ind cn).
  + simpl. rewrite <- mkApps_vars_to_apps.
    unfold PcbvCurr.isFixApp.
    now rewrite decompose_app_mkApps;simpl;destruct (resolve_constr Σ ind cn).
Qed.

Lemma vars_to_apps_constr_not_arity ind cn l Σ:
  ~~ PcbvCurr.isArityHead (t⟦vars_to_apps (eConstr ind cn) l⟧Σ).
Proof.
  destruct l using MCList.rev_ind.
  + simpl. now destruct (resolve_constr Σ ind cn).
  + simpl. now simpl_vars_to_apps.
Qed.

Hint Resolve vars_to_apps_iclosed_n vars_to_apps_constr_not_lambda
     vars_to_apps_constr_not_fix_app vars_to_apps_constr_not_arity : hints.

Lemma negb_and_to_orb a b :
  (~~ a) /\ (~~ b) -> ~~ (a || b).
Proof.
  intros H. unfold is_true in *.
  destruct a,b;intuition;auto.
Qed.

Hint Resolve negb_and_to_orb : hints.

Hint Constructors All2 : hints.

Lemma All_value_of_val:
  forall (Σ1 : global_env) (Σ2 : PCUICAst.global_env)
    (l : list val),
    All (val_ok Σ1) l -> All (fun v : val => PcbvCurr.value Σ2 (t⟦ of_val_i v ⟧ Σ1)) l.
Proof.
  intros Σ1 Σ2 l X.
  eapply All_impl. apply X.
  intros. eapply Wcbv_of_value_value;eauto with hints.
Qed.

Lemma All_expr_iclosed_of_val:
  forall (Σ1 : global_env) (l0 : list val),
    All (val_ok Σ1) l0 -> All (fun x : val => iclosed_n 0 (of_val_i x)) l0.
Proof.
  intros Σ1 l0 X.
  eapply All_impl. apply X. eauto with hints.
Qed.


Lemma All_term_closed_of_val:
  forall (Σ1 : global_env) (l0 : list val),
    genv_ok Σ1 ->
    All (val_ok Σ1) l0 -> All (fun x : val => closed (t⟦ of_val_i x ⟧ Σ1)) l0.
Proof.
  intros Σ1 l0 Hgeok X.
  eapply All_impl. apply X.
  intros. eapply expr_closed_term_closed;eauto with hints.
Qed.

Lemma eval_type_i_subst_env ty : forall n ρ ty_v,
  eval_type_i n ρ ty = Some ty_v ->
  subst_env_i_ty n (exprs ρ) ty = ty_v.
Proof.
  induction ty;intros ??? He.
  + simpl in *. now inversion He.
  + simpl in *. destruct (eval_type_i _ _ _) eqn:Heq;tryfalse. inversion He;subst.
    f_equal;eauto.
  + simpl in *.
    destruct (eval_type_i n ρ ty2) eqn:Hty2;tryfalse.
    destruct (eval_type_i n ρ ty1) eqn:Hty1;tryfalse.
    destruct (decompose_inductive _);tryfalse. inversion He;subst.
    f_equal;auto.
  + tryfalse.
  + simpl in *.
    destruct (n0 <=? n) eqn:Hn0.
    rewrite lookup_i_nth_error in He. unfold lookup_ty. rewrite lookup_i_nth_error.
    rewrite nth_error_map.
    destruct (nth_error ρ (n - n0));simpl in *;auto. destruct (p.2);tryfalse.
    inversion He. reflexivity. tryfalse. now inversion He.
  + simpl in *.
    destruct (eval_type_i n ρ ty2) eqn:Hty2;tryfalse.
    destruct (eval_type_i n ρ ty1) eqn:Hty1;tryfalse.
    inversion He;subst.
    f_equal;auto.
Qed.

Open Scope list.

Lemma subst_env_i_ty_closed_eq n ρ ty :
  iclosed_ty n ty ->
  subst_env_i_ty n ρ ty = ty.
Proof.
  revert n ρ.
  induction ty;intros;
    unfold is_true in *;simpl in *;
    repeat rewrite  Bool.andb_true_iff in *;intuition;
      try (now f_equal).
  assert (Hn0 : n0 <=? n = false) by (leb_ltb_to_prop;lia).
  now rewrite Hn0.
Qed.

Lemma subst_env_i_ty_closed_0_eq n ρ ty :
  iclosed_ty 0 ty ->
  subst_env_i_ty n ρ ty = ty.
Proof.
  intros. eapply subst_env_i_ty_closed_eq.
  now eapply iclosed_ty_0.
Qed.

Hint Resolve eval_ty_expr_env_ok subst_env_i_ty_closed_0_eq : hints.

Lemma subst_term_subst_env_2 :
  forall (Σ : global_env) (e e1 e2 : expr) (nm1 nm2 : ename) (k : nat),
    let l := [(nm1,e1);(nm2,e2)] in
    genv_ok Σ ->
    ty_expr_env_ok l 0 e ->
    iclosed_n #|l| e = true ->
    All (fun x : string × expr => iclosed_n 0 x.2 = true) l ->
    subst0 ([t⟦e1⟧Σ;t⟦e2⟧Σ]) (t⟦e⟧Σ) = t⟦e.[l]⟧ Σ.
Proof.
  intros.
  change ([t⟦ e1 ⟧Σ; t⟦ e2 ⟧Σ]) with (map (fun x => t⟦ x.2 ⟧Σ) [(nm1,e1); (nm2,e2)]).
  eapply subst_term_subst_env_par;eauto.
Qed.
