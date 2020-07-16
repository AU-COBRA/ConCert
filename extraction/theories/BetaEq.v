From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import WcbvEvalAux.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import Morphisms.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import RelationClasses.
From Coq Require Import Relation_Operators.
From Coq Require Import Operators_Properties.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Import EAstUtils.

Fixpoint count_uses (n : nat) (t : term) : nat :=
  match t with
  | tBox => 0
  | tRel i => if n =? i then 1 else 0
  | tVar _ => 0
  | tEvar _ ts => fold_right plus 0 (map (count_uses n) ts)
  | tLambda _ body => count_uses (S n) body
  | tLetIn _ val body => count_uses n val + count_uses (S n) body
  | tApp hd arg => count_uses n hd + count_uses n arg
  | tConst _ => 0
  | tConstruct _ _ => 0
  | tCase _ discr brs => count_uses n discr + fold_right plus 0 (map (count_uses n ∘ snd) brs)
  | tProj _ t => count_uses n t
  | tFix defs _ => fold_right plus 0 (map (count_uses (#|defs| + n) ∘ dbody) defs)
  | tCoFix defs _ => fold_right plus 0 (map (count_uses (#|defs| + n) ∘ dbody) defs)
  end.

Definition affinely_used (n : nat) (t : term) : bool :=
  count_uses n t <=? 1.

Fixpoint num_subterms (t : term) : nat :=
  S match t with
    | tBox => 0
    | tRel i => 0
    | tVar _ => 0
    | tEvar _ ts => fold_right plus 0 (map num_subterms ts)
    | tLambda _ body => num_subterms body
    | tLetIn _ val body => num_subterms val + num_subterms body
    | tApp hd arg => num_subterms hd + num_subterms arg
    | tConst _ => 0
    | tConstruct _ _ => 0
    | tCase _ discr brs => num_subterms discr + fold_right plus 0 (map (num_subterms ∘ snd) brs)
    | tProj _ t => num_subterms t
    | tFix defs _ => fold_right plus 0 (map (num_subterms ∘ dbody) defs)
    | tCoFix defs _ => fold_right plus 0 (map (num_subterms ∘ dbody) defs)
    end.

Lemma num_subterms_positive t :
  num_subterms t > 0.
Proof. destruct t; cbn; lia. Qed.

Lemma num_subterms_lift n k t :
  num_subterms (lift n k t) = num_subterms t.
Proof.
  induction t in k, t |- * using term_forall_list_ind; cbn.
  - easy.
  - now destruct (_ <=? _).
  - easy.
  - f_equal.
    induction H; [easy|].
    cbn in *.
    now rewrite H.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - easy.
  - easy.
  - rewrite IHt.
    do 2 f_equal.
    induction X; [easy|].
    cbn in *.
    now rewrite p0.
  - now rewrite IHt.
  - f_equal.
    induction H in k, m, H |- *; [easy|].
    cbn in *.
    rewrite H.
    rewrite <- Nat.add_succ_r.
    now rewrite IHForall.
  - f_equal.
    induction H in k, m, H |- *; [easy|].
    cbn in *.
    rewrite H.
    rewrite <- Nat.add_succ_r.
    now rewrite IHForall.
Qed.

Lemma num_subterms_subst s k t :
  num_subterms (t{k := s}) = num_subterms t + (num_subterms s - 1) * count_uses k t.
Proof.
  induction t in t, k |- * using term_forall_list_ind; cbn in *.
  - lia.
  - rewrite Nat.leb_compare, Nat.eqb_compare.
    destruct (Nat.compare_spec k n).
    + subst.
      rewrite Nat.sub_diag.
      cbn.
      rewrite num_subterms_lift.
      pose proof (num_subterms_positive s).
      lia.
    + rewrite (proj2 (nth_error_None _ _)) by (now cbn).
      cbn.
      lia.
    + cbn.
      lia.
  - lia.
  - f_equal.
    induction H; cbn in *; [lia|].
    fold (subst1 s k x).
    now rewrite H, IHForall.
  - fold (subst1 s (S k) t).
    now rewrite IHt.
  - fold (subst1 s k t1) (subst1 s (S k) t2).
    now rewrite IHt1, IHt2.
  - fold (subst1 s k t1) (subst1 s k t2).
    now rewrite IHt1, IHt2.
  - lia.
  - lia.
  - fold (subst1 s k t).
    rewrite IHt.
    f_equal.
    rewrite <- Nat.add_assoc.
    symmetry; rewrite <- Nat.add_assoc; symmetry.
    f_equal.
    rewrite Nat.mul_add_distr_l, Nat.add_assoc.
    symmetry; rewrite <- Nat.add_assoc, Nat.add_comm; symmetry.
    rewrite <- Nat.add_assoc.
    f_equal.
    induction X in k, l, X |- *; cbn in *; [lia|].
    fold (subst1 s k x.2).
    now rewrite p0, IHX.
  - fold (subst1 s k t).
    now rewrite IHt.
  - f_equal.
    induction H in k, m, H |- *; cbn in *; [lia|].
    rewrite <- Nat.add_succ_r.
    fold (subst1 s (#|l| + S k) (dbody x)).
    now rewrite H, IHForall.
  - f_equal.
    induction H in k, m, H |- *; cbn in *; [lia|].
    rewrite <- Nat.add_succ_r.
    fold (subst1 s (#|l| + S k) (dbody x)).
    now rewrite H, IHForall.
Qed.

Definition inspect {A} (a : A) : { a' : A | a = a' } :=
  exist a eq_refl.

Definition map_in {A B} : forall (l : list A) (f : forall a, In a l -> B), list B.
Proof.
  fix map_in 1.
  intros l f.
  destruct l as [|a l]; [exact []|].
  refine (_ :: map_in l _).
  - apply (f a).
    left.
    reflexivity.
  - intros a' ina'.
    apply (f a').
    right.
    assumption.
Defined.

Inductive normalize_view : term -> Type :=
| nv_box : normalize_view tBox
| nv_rel i : normalize_view (tRel i)
| nv_var id : normalize_view (tVar id)
| nv_evar n ts : normalize_view (tEvar n ts)
| nv_lambda na body : normalize_view (tLambda na body)
| nv_let_in na val body : normalize_view (tLetIn na val body)
| nv_app hd arg : normalize_view (tApp hd arg)
| nv_app_lam na body arg : normalize_view (tApp (tLambda na body) arg)
| nv_const kn : normalize_view (tConst kn)
| nv_construct ind c : normalize_view (tConstruct ind c)
| nv_case ind discr brs : normalize_view (tCase ind discr brs)
| nv_proj p t : normalize_view (tProj p t)
| nv_fix defs i : normalize_view (tFix defs i)
| nv_cofix defs i : normalize_view (tCoFix defs i).

Set Equations Transparent.
Equations normalize_viewc (t : term) : normalize_view t :=
normalize_viewc tBox := nv_box;
normalize_viewc (tRel i) := nv_rel i;
normalize_viewc (tVar id) := nv_var id;
normalize_viewc (tEvar n ts) := nv_evar n ts;
normalize_viewc (tLambda na body) := nv_lambda na body;
normalize_viewc (tLetIn na val body) := nv_let_in na val body;
normalize_viewc (tApp (tLambda na body) arg) := nv_app_lam na body arg;
normalize_viewc (tApp hd arg) := nv_app hd arg;
normalize_viewc (tConst kn) := nv_const kn;
normalize_viewc (tConstruct ind c) := nv_construct ind c;
normalize_viewc (tCase ind discr brs) := nv_case ind discr brs;
normalize_viewc (tProj p t) := nv_proj p t;
normalize_viewc (tFix defs i) := nv_fix defs i;
normalize_viewc (tCoFix defs i) := nv_cofix defs i.
Unset Equations Transparent.

Lemma num_subterms_le_sum_In t l :
  In t l ->
  num_subterms t <= fold_right plus 0 (map num_subterms l).
Proof.
  induction l; intros isin; [easy|].
  cbn in *.
  destruct isin as [->|isin].
  - lia.
  - specialize (IHl isin).
    lia.
Qed.

(*
Set Equations Transparent.
Equations is_lam_sig (t : term) : option ({ '(na, body) | t = tLambda na body }) :=
is_lam_sig (tLambda na body) := Some (exist (na, body) eq_refl);
is_lam_sig _ := None.
Unset Equations Transparent.
*)

Definition affine_lam_body (t : term) : option term :=
  match t with
  | tLambda na body => if affinely_used 0 body then
                         Some body
                       else
                         None
  | _ => None
  end.

Lemma sum_le_by_element {A} (f : A -> nat) (l : list A) (g : forall a, In a l -> A) :
  (forall a isin, f (g a isin) <= f a) ->
  fold_right plus 0 (map f (map_in l g)) <=
  fold_right plus 0 (map f l).
Proof.
  intros le.
  induction l as [|a l IH]; [easy|].
  cbn in *.
  apply Nat.add_le_mono.
  - apply le.
  - apply IH.
    intros a' isin.
    apply le.
Qed.

Lemma affine_lam_body_Some_inv (t body : term) :
  affine_lam_body t = Some body ->
  exists na,
    t = tLambda na body /\ count_uses 0 body <= 1.
Proof.
  intros aff.
  unfold affine_lam_body, affinely_used in *.
  destruct t; try congruence.
  destruct (_ <=? _) eqn:le; [|congruence].
  noconf aff.
  now propify.
Qed.

Ltac solve_normalize :=
  match goal with
  | [normalize: forall x : term, _ |- _] =>
    repeat destruct (normalize _ _);
    try apply Nat.lt_succ_r;
    cbn in *;
    rewrite ?num_subterms_subst in *;
    try lia
  end.

Inductive affine_lam_body_view : term -> Type :=
| is_affine_lam_body na body : affinely_used 0 body -> affine_lam_body_view (tLambda na body)
| affine_lam_body_view_other t :
    (forall na body, t = tLambda na body -> affinely_used 0 body = false) ->
    affine_lam_body_view t.

Set Equations Transparent.
Equations affine_lam_body_viewc (t : term) : affine_lam_body_view t :=
affine_lam_body_viewc (tLambda na body) with inspect (affinely_used 0 body) := {
  | exist true h := is_affine_lam_body na body h;
  | exist false _ := affine_lam_body_view_other (tLambda na body) _
  };
affine_lam_body_viewc t := affine_lam_body_view_other t _.
Unset Equations Transparent.

Equations normalize' (t : term) : {t' : term | num_subterms t' <= num_subterms t}
  by wf (num_subterms t) lt :=
normalize' tBox := exist tBox _;
normalize' (tRel i) := exist (tRel i) _;
normalize' (tVar id) := exist (tVar id) _;
normalize' (tEvar n ts) :=
  exist (tEvar n (map_in ts (fun t isin => proj1_sig (normalize' t)))) _;
normalize' (tLambda na body) := exist (tLambda na (proj1_sig (normalize' body))) _;
normalize' (tLetIn na val body) :=
  exist (tLetIn na (proj1_sig (normalize' val)) (proj1_sig (normalize' body))) _;
normalize' (tApp hd arg) with normalize' hd := {
  | exist nhd le with affine_lam_body_viewc nhd := {
    | is_affine_lam_body _ body affin := exist (proj1_sig (normalize' (body{0 := arg}))) _;
    | affine_lam_body_view_other nhd _ := exist (tApp nhd (proj1_sig (normalize' arg))) _
    }
  };
normalize' (tConst kn) := exist (tConst kn) _;
normalize' (tConstruct ind c) := exist (tConstruct ind c) _;
normalize' (tCase ind discr brs) :=
  exist
    (tCase
       ind
       (proj1_sig (normalize' discr))
       (map_in brs (fun p isin => (p.1, proj1_sig (normalize' p.2)))))
    _;
normalize' (tProj p t) := exist (tProj p (proj1_sig (normalize' t))) _;
normalize' (tFix defs i) :=
  exist
    (tFix (map_in defs (fun d isin =>
                          {| dname := dname d;
                             dbody := proj1_sig (normalize' (dbody d));
                             rarg := rarg d |})) i)
    _;
normalize' (tCoFix defs i) :=
  exist
    (tCoFix (map_in defs (fun d isin =>
                            {| dname := dname d;
                               dbody := proj1_sig (normalize' (dbody d));
                               rarg := rarg d |})) i)
    _.
Next Obligation.
  solve_normalize.
  now apply num_subterms_le_sum_In.
Qed.
Next Obligation.
  solve_normalize.
  apply sum_le_by_element.
  intros.
  now destruct (normalize' _ _).
Qed.
Next Obligation. solve_normalize. Qed.
Next Obligation. solve_normalize. Qed.
Next Obligation. solve_normalize. Qed.
Next Obligation. solve_normalize. Qed.
Next Obligation. solve_normalize. Qed.
Next Obligation.
  solve_normalize.
  unfold affinely_used in affin; propify.
  destruct (count_uses _ _) as [|[]]; lia.
Defined.
Next Obligation.
  solve_normalize.
  unfold affinely_used in affin; propify.
  destruct (count_uses _ _) as [|[]]; lia.
Qed.
Next Obligation. solve_normalize. Defined.
Next Obligation. solve_normalize. Qed.
Next Obligation. solve_normalize. Qed.
Next Obligation.
  solve_normalize.
  apply (in_map snd) in isin.
  rewrite <- map_map.
  pose proof (num_subterms_le_sum_In _ _ isin).
  cbn in *.
  lia.
Qed.
Next Obligation.
  solve_normalize.
  apply Nat.add_le_mono; [easy|].
  apply sum_le_by_element.
  intros.
  now destruct a, (normalize' _ _).
Qed.
Next Obligation. solve_normalize. Qed.
Next Obligation.
  solve_normalize.
  apply (in_map dbody) in isin.
  rewrite <- map_map.
  now apply num_subterms_le_sum_In.
Qed.
Next Obligation.
  solve_normalize.
  apply sum_le_by_element.
  intros [] ?.
  cbn.
  now destruct (normalize' _ _).
Qed.
Next Obligation.
  solve_normalize.
  apply (in_map dbody) in isin.
  rewrite <- map_map.
  now apply num_subterms_le_sum_In.
Qed.
Next Obligation.
  solve_normalize.
  apply sum_le_by_element.
  intros [] ?.
  cbn.
  now destruct (normalize' _ _).
Qed.

Definition normalize (t : term) : term :=
  proj1_sig (normalize' t).

Lemma normalize_unfold t :
  normalize t = proj1_sig (normalize' t).
Proof. reflexivity. Qed.

Lemma num_subterms_normalize t :
  num_subterms (normalize t) <= num_subterms t.
Proof.
  unfold normalize.
  now destruct (normalize' t).
Qed.

Lemma map_in_map {A B} (l : list A) (f : forall a, In a l -> B) (g : A -> B) :
  (forall a isin, f a isin = g a) ->
  map_in l f = map g l.
Proof.
  intros ext.
  induction l as [|a l IH]; [easy|].
  cbn.
  rewrite ext, IH; [easy|].
  intros; apply ext.
Qed.

Lemma normalize_tBox : normalize tBox = tBox.
Proof. reflexivity. Qed.

Lemma normalize_tRel i : normalize (tRel i) = tRel i.
Proof. reflexivity. Qed.

Lemma normalize_tVar id : normalize (tVar id) = tVar id.
Proof. reflexivity. Qed.

Lemma normalize_tEvar n ts :
  normalize (tEvar n ts) = tEvar n (map normalize ts).
Proof.
  unfold normalize.
  simp normalize'.
  cbn.
  f_equal.
  now apply map_in_map.
Qed.

Lemma normalize_tLambda na body :
  normalize (tLambda na body) = tLambda na (normalize body).
Proof. now unfold normalize; simp normalize'. Qed.

Lemma normalize_tLetIn na val body :
  normalize (tLetIn na val body) = tLetIn na (normalize val) (normalize body).
Proof. now unfold normalize; simp normalize'. Qed.

Lemma normalize_tApp hd arg :
  normalize (tApp hd arg) =
  match affine_lam_body (normalize hd) with
  | Some body => normalize (body{0 := arg})
  | None => tApp (normalize hd) (normalize arg)
  end.
Proof.
  unfold normalize.
  simp normalize'.
  destruct (normalize' hd).
  cbn.
  destruct x; try easy.
  destruct (affine_lam_body_viewc (tLambda n x)) eqn:abody.
  - cbn.
    clear abody.
    now destruct (affinely_used 0 body).
  - destruct t; try easy.
    cbn.
    clear abody.
    specialize (e _ _ eq_refl).
    now rewrite e.
Qed.

Lemma normalize_tConst kn : normalize (tConst kn) = tConst kn.
Proof. reflexivity. Qed.

Lemma normalize_tConstruct ind c : normalize (tConstruct ind c) = tConstruct ind c.
Proof. reflexivity. Qed.

Lemma normalize_tCase ind discr brs :
  normalize (tCase ind discr brs) =
  tCase ind (normalize discr) (map (on_snd normalize) brs).
Proof.
  unfold normalize.
  simp normalize'.
  cbn.
  f_equal.
  now apply map_in_map.
Qed.

Lemma normalize_tProj p t :
  normalize (tProj p t) = tProj p (normalize t).
Proof. now unfold normalize; simp normalize'. Qed.

Lemma normalize_tFix defs i :
  normalize (tFix defs i) =
  tFix (map (map_def normalize) defs) i.
Proof.
  unfold normalize.
  simp normalize'.
  cbn.
  f_equal.
  now apply map_in_map.
Qed.

Lemma normalize_tCoFix defs i :
  normalize (tCoFix defs i) =
  tCoFix (map (map_def normalize) defs) i.
Proof.
  unfold normalize.
  simp normalize'.
  cbn.
  f_equal.
  now apply map_in_map.
Qed.

Hint Rewrite
     normalize_tBox
     normalize_tRel
     normalize_tVar
     normalize_tEvar
     normalize_tLambda
     normalize_tLetIn
     normalize_tApp
     normalize_tConst
     normalize_tConstruct
     normalize_tCase
     normalize_tProj
     normalize_tFix
     normalize_tCoFix : normalize.

Lemma normalize_normalize t :
  normalize (normalize t) = normalize t.
Proof.
  unfold normalize at 2.
  funelim (normalize' t); cbn in *; simp normalize.
  - easy.
  - easy.
  - easy.
  - f_equal.
    induction l; [easy|].
    cbn.
    rewrite H by (now left).
    f_equal.
    rewrite IHl.
    + easy.
    + intros t intl.
      apply H.
      now right.
    + intros.
      apply H0.
      cbn.
      lia.
  - now rewrite H.
  - now rewrite H, H0.
  - easy.
  - easy.
  - rewrite H.
    f_equal.
    clear -H0 H1.
    induction l0; [easy|].
    cbn.
    rewrite H0 by (now left).
    f_equal.
    apply IHl0.
    + intros; apply H0; now right.
    + intros; apply H1; cbn; lia.
  - now rewrite H.
  - f_equal.
    induction m; [easy|].
    unfold map_def.
    cbn.
    f_equal; [f_equal; now apply H; left|].
    apply IHm.
    + intros; apply H; now right.
    + intros; apply H0; cbn; lia.
  - f_equal.
    induction m0; [easy|].
    unfold map_def.
    cbn.
    f_equal; [f_equal; now apply H; left|].
    apply IHm0.
    + intros; apply H; now right.
    + intros; apply H0; cbn; lia.
  - rewrite H.
    unfold normalize at 2.
    rewrite Heq0.
    cbn.
    propify.
    now rewrite i.
  - replace t with (normalize t2); last first.
    { unfold normalize.
      now rewrite Heq0. }
    fold (normalize t2) in Hind.
    rewrite Hind.
    unfold normalize at 1 5.
    rewrite Heq0.
    cbn.
    rewrite H.
    destruct t; try easy.
    clear -e.
    specialize (e _ _ eq_refl).
    cbn.
    now rewrite e.
Qed.

Lemma normalize_mkApps_normalize_hd hd args :
  normalize (mkApps (normalize hd) args) =
  normalize (mkApps hd args).
Proof.
  induction args using List.rev_ind in hd, args |- *.
  - cbn.
    apply normalize_normalize.
  - rewrite !mkApps_app.
    cbn.
    rewrite !normalize_tApp.
    now rewrite IHargs.
Qed.

Lemma normalize_mkApps hd args :
  isLambda (normalize hd) = false ->
  normalize (mkApps hd args) =
  mkApps (normalize hd) (map normalize args).
Proof.
  intros not_lam.
  induction args in hd, args, not_lam |- *; [easy|].
  cbn in *.
  rewrite IHargs.
  - rewrite normalize_tApp.
    now destruct (normalize hd).
  - rewrite normalize_tApp.
    cbn.
    now destruct (normalize hd).
Qed.

Lemma value_normalize_tBox v :
  value v ->
  normalize v = tBox ->
  v = tBox.
Proof.
  intros val norm.
  destruct val.
  - now destruct t.
  - rewrite normalize_mkApps in norm by (now destruct t).
    destruct t; try easy; simp normalize in norm; solve_discr.
  - destruct f; try easy.
    rewrite normalize_mkApps in norm by easy.
    simp normalize in norm.
    solve_discr.
Qed.

Lemma value_normalize_tLambda v na body :
  value v ->
  normalize v = tLambda na body ->
  exists body',
    v = tLambda na body' /\
    normalize body' = body.
Proof.
  intros val norm.
  destruct val.
  - destruct t; try easy.
    rewrite normalize_tLambda in norm.
    noconf norm.
    now eexists.
  - rewrite normalize_mkApps in norm by (now destruct t).
    destruct t; try easy; simp normalize in norm; solve_discr.
  - destruct f; try easy.
    rewrite normalize_mkApps in norm by easy.
    simp normalize in norm; solve_discr.
Qed.

(*
Lemma count_uses_lift k n k' t :
  k' < k ->
  count_uses k (lift n k' t) = count_uses (k + k') t.
Proof.
  intros le.
  induction t using term_forall_list_ind in t, k, le |- *; cbn in *; auto.
  - destruct (_ <=? _) eqn:?, (_ =? _) eqn:?; propify;
      cbn; destruct (_ =? _) eqn:?; propify; try lia.
    + rewrite <- Heqb0 in Heqb.
      lia.

      cbn; destruct (_ =? _) eqn:?; propify; try lia.
*)

Lemma count_uses_lift_other k k' n t :
  k < k' ->
  count_uses k (lift n k' t) = count_uses k t.
Proof.
  intros lt.
  induction t using term_forall_list_ind in t, k, k', lt |- *; cbn in *.
  - easy.
  - repeat
      (try destruct (_ <=? _) eqn:?; propify;
       try destruct (_ =? _) eqn:?; propify;
       cbn in *);
       lia.
  - easy.
  - induction H; [easy|].
    cbn in *.
    rewrite H by easy.
    lia.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - easy.
  - easy.
  - rewrite IHt by easy.
    f_equal.
    induction X; [easy|].
    cbn.
    rewrite p0 by easy.
    lia.
  - now rewrite IHt.
  - rewrite map_length.
    induction H in H, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite H by lia.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHForall.
  - rewrite map_length.
    induction H in H, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite H by lia.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHForall.
Qed.

Lemma count_uses_lift_all k k' n t :
  k <= k' ->
  k' < n + k ->
  count_uses k' (lift n k t) = 0.
Proof.
  intros l1 l2.
  induction t using term_forall_list_ind in t, n, k, k', l1, l2 |- *; cbn in *; auto.
  - destruct (_ <=? _) eqn:?; propify; cbn;
      destruct (_ =? _) eqn:?; propify; lia.
  - induction H; [easy|].
    cbn in *.
    now rewrite H.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - rewrite IHt by easy.
    cbn.
    clear IHt.
    induction X; [easy|].
    cbn.
    now rewrite p0.
  - rewrite map_length.
    induction H in H, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite H by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    now apply IHForall.
  - rewrite map_length.
    induction H in H, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite H by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    now apply IHForall.
Qed.

Lemma count_uses_subst_other k k' s t :
  k < k' ->
  count_uses k (subst s k' t) = count_uses k t.
Proof.
  intros lt.
  induction t in t, k, k', lt |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _) eqn:?, (_ =? _) eqn:?; propify; subst.
    + lia.
    + destruct (nth_error _ _) eqn:nth.
      * now apply count_uses_lift_all.
      * cbn.
        destruct (_ =? _) eqn:?; propify; [|easy].
        apply nth_error_None in nth.
        lia.
    + cbn.
      now rewrite Nat.eqb_refl.
    + cbn.
      destruct (_ =? _) eqn:?; propify; lia.
  - induction H; [easy|].
    cbn in *.
    now rewrite H.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - rewrite IHt by easy; cbn; clear IHt.
    f_equal.
    induction X; [easy|].
    cbn.
    now rewrite p0.
  - rewrite map_length.
    induction H in H, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite H by easy.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHForall.
  - rewrite map_length.
    induction H in H, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite H by easy.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHForall.
Qed.

Inductive ared1 : term -> term -> Prop :=
| ared_beta na body arg :
    affinely_used 0 body ->
    ared1 (tApp (tLambda na body) arg) (body{0 := arg})
| ared_evar n ts ts' :
    OnOne2 ared1 ts ts' ->
    ared1 (tEvar n ts) (tEvar n ts')
| ared_lambda na body body' :
    ared1 body body' ->
    ared1 (tLambda na body) (tLambda na body')
| ared_let_in_l na val val' body :
    ared1 val val' ->
    ared1 (tLetIn na val body) (tLetIn na val' body)
| ared_let_in_r na val body body' :
    ared1 body body' ->
    ared1 (tLetIn na val body) (tLetIn na val body')
| ared_app_l hd hd' arg :
    ared1 hd hd' ->
    ared1 (tApp hd arg) (tApp hd' arg)
| ared_app_r hd arg arg' :
    ared1 arg arg' ->
    ared1 (tApp hd arg) (tApp hd arg')
| ared_case_discr ind discr discr' brs :
    ared1 discr discr' ->
    ared1 (tCase ind discr brs) (tCase ind discr' brs)
| ared_case_brs ind discr brs brs' :
    OnOne2 (fun br br' => br.1 = br'.1 /\ ared1 br.2 br'.2) brs brs' ->
    ared1 (tCase ind discr brs) (tCase ind discr brs')
| ared_proj p t t' :
    ared1 t t' ->
    ared1 (tProj p t) (tProj p t')
| ared_fix defs defs' i :
    OnOne2 (fun d d' => dname d = dname d' /\
                        ared1 (dbody d) (dbody d') /\
                        rarg d = rarg d') defs defs' ->
    ared1 (tFix defs i) (tFix defs' i)
| ared_cofix defs defs' i :
    OnOne2 (fun d d' => dname d = dname d' /\
                        ared1 (dbody d) (dbody d') /\
                        rarg d = rarg d') defs defs' ->
    ared1 (tCoFix defs i) (tCoFix defs' i).

Derive Signature for ared1.

Lemma ared1_ind_all
      (P : term -> term -> Prop)
      (Hbeta : forall (na : name) (body arg : term),
          affinely_used 0 body ->
          P (tApp (tLambda na body) arg) (body {0 := arg}))
      (Hevar : forall (n : nat) (ts ts' : list term),
          OnOne2 (fun t t' => ared1 t t' /\ P t t') ts ts' ->
          P (tEvar n ts) (tEvar n ts'))
      (Hlam : forall (na : name) (body body' : term),
          ared1 body body' ->
          P body body' ->
          P (tLambda na body) (tLambda na body'))
      (Hletinl : forall (na : name) (val val' body : term),
          ared1 val val' ->
          P val val' ->
          P (tLetIn na val body) (tLetIn na val' body))
      (Hletinr : forall (na : name) (val body body' : term),
          ared1 body body' ->
          P body body' ->
          P (tLetIn na val body) (tLetIn na val body'))
      (Happl : forall hd hd' arg : term,
          ared1 hd hd' ->
          P hd hd' ->
          P (tApp hd arg) (tApp hd' arg))
      (Happr : forall hd arg arg' : term,
          ared1 arg arg' ->
          P arg arg' ->
          P (tApp hd arg) (tApp hd arg'))
      (Hcasediscr : forall (ind : inductive × nat) (discr discr' : term) (brs : list (nat × term)),
          ared1 discr discr' ->
          P discr discr' ->
          P (tCase ind discr brs) (tCase ind discr' brs))
      (Hcasebrs : forall (ind : inductive × nat) (discr : term) (brs brs' : list (nat × term)),
          OnOne2 (fun br br' => br.1 = br'.1 /\ ared1 br.2 br'.2 /\ P br.2 br'.2) brs brs' ->
          P (tCase ind discr brs) (tCase ind discr brs'))
      (Hproj : forall (p : projection) (t t' : term),
          ared1 t t' ->
          P t t' ->
          P (tProj p t) (tProj p t'))
      (Hfix : forall (defs defs' : list (def term)) (i : nat),
          OnOne2
            (fun d d' => dname d = dname d' /\
                         ared1 (dbody d) (dbody d') /\
                         P (dbody d) (dbody d') /\
                         rarg d = rarg d') defs defs' ->
          P (tFix defs i) (tFix defs' i))
      (Hcofix : forall (defs defs' : list (def term)) (i : nat),
          OnOne2
            (fun d d' => dname d = dname d' /\
                         ared1 (dbody d) (dbody d') /\
                         P (dbody d) (dbody d') /\
                         rarg d = rarg d') defs defs' ->
          P (tCoFix defs i) (tCoFix defs' i)) :
  forall t t' , ared1 t t' -> P t t'.
Proof.
  fix ind 3.
  destruct 1;
    try solve[
          match goal with
          | [H: _ |- _] =>
            match type of H with
            | forall t t', ared1 t t' -> _ => fail 1
            | _ => eapply H
            end; eauto
          end].
  - apply Hevar.
    clear -H ind.
    revert ts ts' H.
    fix f 3.
    destruct 1.
    + constructor.
      split; [|apply ind]; assumption.
    + constructor.
      apply f.
      assumption.
  - apply Hcasebrs.
    clear -H ind.
    revert brs brs' H.
    fix f 3.
    destruct 1.
    + constructor.
      destruct a.
      (repeat split); [| |apply ind]; assumption.
    + constructor.
      apply f.
      assumption.
  - apply Hfix.
    clear -H ind.
    revert defs defs' H.
    fix f 3.
    destruct 1.
    + constructor.
      destruct a as (? & ? & ?).
      (repeat split); [| |apply ind|]; assumption.
    + constructor.
      apply f.
      assumption.
  - apply Hcofix.
    clear -H ind.
    revert defs defs' H.
    fix f 3.
    destruct 1.
    + constructor.
      destruct a as (? & ? & ?).
      (repeat split); [| |apply ind|]; assumption.
    + constructor.
      apply f.
      assumption.
Defined.

Inductive ared : term -> term -> Prop :=
| ared_refl x : ared x x
| ared_trans1 x y z : ared x y -> ared1 y z -> ared x z.

Lemma ared_alt t t' :
  ared t t' <-> clos_refl_trans _ ared1 t t'.
Proof.
  split; intros r.
  - apply clos_rt_rtn1_iff.
    now induction r; econstructor.
  - apply clos_rt_rtn1_iff in r.
    now induction r; econstructor.
Qed.

Lemma ared_trans x y z :
  ared x y ->
  ared y z ->
  ared x z.
Proof.
  rewrite !ared_alt.
  intros.
  now eapply rt_trans.
Qed.

Instance Reflexive_ared : Reflexive ared.
Proof. intros x. apply ared_refl. Qed.

Instance Transitive_ared : Transitive ared.
Proof.
  intros x y z.
  apply ared_trans.
Qed.

Lemma ared_step x y :
  ared1 x y ->
  ared x y.
Proof.
  intros.
  now eapply ared_trans1; [apply ared_refl|].
Qed.

Definition normal t : Prop :=
  forall r, ared1 t r -> False.

Derive Signature for OnOne2.
Derive NoConfusionHom for term.

Lemma normal_normalize t : normal (normalize t).
Proof.
  enough (forall ns, num_subterms t <= ns -> normal (normalize t)).
  { now apply (H (num_subterms t)). }
  intros ns le.
  induction ns as [|ns IH] in ns, t, le |- *; [now destruct t|].
  destruct t; repeat (cbn in *; simp normalize); intros ? r; try solve [depelim r].
  - depelim r.
    induction l in l, le, ts', H |- *; [easy|].
    cbn in *.
    depelim H.
    + now eapply (IH a).
    + now eapply IHl.
  - depelim r.
    now eapply (IH t).
  - depelim r.
    + now eapply (IH t1).
    + now eapply (IH t2).
  - destruct (affine_lam_body _) eqn:aff.
    + apply affine_lam_body_Some_inv in aff as (? & ? & ?).
      eapply (IH (t{0 := t2})); [|easy].
      rewrite num_subterms_subst.
      apply (f_equal num_subterms) in H.
      cbn in *.
      pose proof (num_subterms_normalize t1).
      now destruct (count_uses 0 t) as [|[]].
    + inversion r; subst; clear r.
      * rewrite <- H in aff.
        cbn in *.
        now rewrite H2 in aff.
      * now eapply (IH t1).
      * now eapply (IH t2).
  - depelim r.
    + now eapply (IH t).
    + induction l in l, le, brs', H |- *; [easy|].
      cbn in *.
      depelim H.
      * now eapply (IH a.2).
      * now eapply IHl.
  - depelim r.
    now eapply (IH t).
  - depelim r.
    induction m in m, le, defs', H |- *; [easy|].
    cbn in *.
    depelim H.
    + now eapply (IH (dbody a)).
    + now eapply IHm.
  - depelim r.
    induction m in m, le, defs', H |- *; [easy|].
    cbn in *.
    depelim H.
    + now eapply (IH (dbody a)).
    + now eapply IHm.
Qed.

Lemma OnOne2_split {A} (P : A -> A -> Type) l l' :
  OnOne2 P l l' ->
  ∑ pref a a' suf,
    l = pref ++ [a] ++ suf ×
    l' = pref ++ [a'] ++ suf ×
    P a a'.
Proof.
  intros oo.
  induction oo.
  - exists [], hd, hd', tl.
    now repeat split.
  - destruct IHoo as (pref & a & a' & suf & -> & -> & p).
    exists (hd :: pref), a, a', suf.
    now repeat split.
Qed.

Inductive rtrans_clos {A} (R : A -> A -> Type) (x : A) : A -> Type :=
| rtrans_clos_refl : rtrans_clos R x x
| rtrans_clos_trans :
    forall y z,
      rtrans_clos R x y ->
      R y z ->
      rtrans_clos R x z.

Lemma All2_many_OnOne2 :
  forall A (R : A -> A -> Type) l l',
    All2 R l l' ->
    rtrans_clos (OnOne2 R) l l'.
Proof.
  intros A R l l' h.
  induction h.
  - constructor.
  - econstructor ; revgoals.
    + constructor. eassumption.
    + clear - IHh. rename IHh into h.
      induction h.
      * constructor.
      * econstructor.
        -- eassumption.
        -- econstructor. assumption.
Qed.

Lemma ared_evar_one n l l' :
  OnOne2 ared l l' ->
  ared (tEvar n l) (tEvar n l').
Proof.
  intros oo.
  apply OnOne2_split in oo as (pref & t & t' & suf & -> & -> & r).
  induction r.
  - apply ared_refl.
  - eapply ared_trans1; [eassumption|].
    constructor.
    apply OnOne2_app.
    now constructor.
Qed.

Lemma ared_evar_all n l l' :
  All2 ared l l' ->
  ared (tEvar n l) (tEvar n l').
Proof.
  intros all.
  apply All2_many_OnOne2 in all.
  induction all; [apply ared_refl|].
  eapply ared_trans; [eassumption|].
  now apply ared_evar_one.
Qed.

Lemma ared_case_brs_one ind discr brs brs' :
  OnOne2 (fun br br' => br.1 = br'.1 × ared br.2 br'.2) brs brs' ->
  ared (tCase ind discr brs) (tCase ind discr brs').
Proof.
  intros oo.
  apply OnOne2_split in oo as (pref & t & t' & suf & -> & -> & fst & r).
  destruct t, t'; cbn in *; subst.
  depind r.
  - apply ared_refl.
  - eapply ared_trans1; [eassumption|].
    constructor.
    apply OnOne2_app.
    now constructor.
Qed.

Lemma ared_case_brs_all ind discr brs brs' :
  All2 (fun br br' => br.1 = br'.1 × ared br.2 br'.2) brs brs' ->
  ared (tCase ind discr brs) (tCase ind discr brs').
Proof.
  intros all.
  apply All2_many_OnOne2 in all.
  induction all; [apply ared_refl|].
  eapply ared_trans; [eassumption|].
  now apply ared_case_brs_one.
Qed.

Lemma ared_fix_one defs defs' i :
  OnOne2 (fun d d' => dname d = dname d' × ared (dbody d) (dbody d') × rarg d = rarg d')
         defs defs' ->
  ared (tFix defs i) (tFix defs' i).
Proof.
  intros oo.
  apply OnOne2_split in oo as (pref & t & t' & suf & -> & -> & ? & r & ?).
  destruct t, t'; cbn in *; subst.
  depind r.
  - apply ared_refl.
  - eapply ared_trans1; [eassumption|].
    constructor.
    apply OnOne2_app.
    now constructor.
Qed.

Lemma ared_fix_all defs defs' i :
  All2 (fun d d' => dname d = dname d' × ared (dbody d) (dbody d') × rarg d = rarg d')
         defs defs' ->
  ared (tFix defs i) (tFix defs' i).
Proof.
  intros all.
  apply All2_many_OnOne2 in all.
  induction all; [apply ared_refl|].
  eapply ared_trans; [eassumption|].
  now apply ared_fix_one.
Qed.

Lemma ared_cofix_one defs defs' i :
  OnOne2 (fun d d' => dname d = dname d' × ared (dbody d) (dbody d') × rarg d = rarg d')
         defs defs' ->
  ared (tCoFix defs i) (tCoFix defs' i).
Proof.
  intros oo.
  apply OnOne2_split in oo as (pref & t & t' & suf & -> & -> & ? & r & ?).
  destruct t, t'; cbn in *; subst.
  depind r.
  - apply ared_refl.
  - eapply ared_trans1; [eassumption|].
    constructor.
    apply OnOne2_app.
    now constructor.
Qed.

Lemma ared_cofix_all defs defs' i :
  All2 (fun d d' => dname d = dname d' × ared (dbody d) (dbody d') × rarg d = rarg d')
         defs defs' ->
  ared (tCoFix defs i) (tCoFix defs' i).
Proof.
  intros all.
  apply All2_many_OnOne2 in all.
  induction all; [apply ared_refl|].
  eapply ared_trans; [eassumption|].
  now apply ared_cofix_one.
Qed.

Lemma ared_to_normalize t : ared t (normalize t).
Proof.
  unfold normalize.
  funelim (normalize' t); cbn in *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (map_in_map _ _ normalize) by (now intros).
    apply ared_evar_all.
    induction l; [constructor|].
    cbn.
    constructor.
    + now apply H; left.
    + apply IHl.
      * now intros; apply H; right.
      * now intros; apply H0; cbn.
  - induction H; [reflexivity|].
    etransitivity; [now apply IHared|].
    now apply ared_step; constructor.
  - transitivity (tLetIn n2 (normalize t0) t1).
    + clear H0.
      fold (normalize t0) in H.
      induction H; [reflexivity|].
      etransitivity; [now apply IHared|].
      now apply ared_step; constructor.
    + fold (normalize t1) in *.
      fold (normalize t0) in *.
      induction H0; [reflexivity|].
      etransitivity; [now apply IHared|].
      now apply ared_step; constructor.
  - reflexivity.
  - reflexivity.
  - rewrite (map_in_map _ _ (on_snd normalize)) by (now intros).
    transitivity (tCase p (normalize t4) l0).
    + fold (normalize t4) in H.
      induction H; [reflexivity|].
      etransitivity; [now apply IHared|].
      now apply ared_step; constructor.
    + apply ared_case_brs_all.
      induction l0; [constructor|].
      cbn in *.
      constructor.
      * split; [reflexivity|].
        now apply H0; left.
      * apply IHl0.
        -- now intros; apply H0; right.
        -- now intros; apply H1; cbn.
  - induction H; [reflexivity|].
    etransitivity.
    + now apply IHared.
    + apply ared_step.
      now constructor.
  - apply ared_fix_all.
    induction m; [constructor|].
    cbn in *.
    constructor.
    + split; [reflexivity|].
      split; [|reflexivity].
      now apply H; left.
    + apply IHm.
      * now intros; apply H; right.
      * now intros; apply H0; cbn.
  - apply ared_cofix_all.
    induction m0; [constructor|].
    cbn in *.
    constructor.
    + split; [reflexivity|].
      split; [|reflexivity].
      now apply H; left.
    + apply IHm0.
      * now intros; apply H; right.
      * now intros; apply H0; cbn.
  - transitivity (tApp (normalize t2) t3).
    + fold (normalize t2) in *.
      induction Hind; [reflexivity|].
      etransitivity; [now eapply IHHind|].
      now apply ared_step; constructor.
    + unfold normalize.
      rewrite Heq0.
      cbn.
      transitivity (body{0 := t3}); [now apply ared_step, ared_beta|].
      apply H0.
      rewrite num_subterms_subst.
      unfold affinely_used in i.
      clear Heq.
      now destruct (count_uses 0 body) as [|[]].
  - transitivity (tApp (normalize t2) t3).
    + fold (normalize t2) in Hind.
      induction Hind; [reflexivity|].
      etransitivity; [now eapply IHHind|].
      now apply ared_step; constructor.
    + unfold normalize.
      rewrite Heq0.
      cbn.
      fold (normalize t3) in *.
      induction H; [reflexivity|].
      etransitivity; [now eapply IHared|].
      now apply ared_step; constructor.
Qed.

Lemma substitution_ared1 s k t t' :
  ared1 t t' ->
  ared1 (subst s k t) (subst s k t').
Proof.
  intros r.
  induction r in r, t, t', k |- * using ared1_ind_all; cbn in *; auto using ared1.
  - unfold subst1.
    rewrite distr_subst.
    apply ared_beta.
    unfold affinely_used in *.
    now rewrite count_uses_subst_other.
  - constructor.
    induction H; constructor; auto.
    intuition.
  - constructor.
    induction H; constructor; auto.
    intuition.
  - constructor.
    induction H in H, defs, defs', k |- *; cbn.
    + constructor.
      intuition.
    + rewrite (OnOne2_length H) in *.
      constructor.
      rewrite <- !Nat.add_succ_r.
      apply IHOnOne2.
  - constructor.
    induction H in H, defs, defs', k |- *; cbn.
    + constructor.
      intuition.
    + rewrite (OnOne2_length H) in *.
      constructor.
      rewrite <- !Nat.add_succ_r.
      apply IHOnOne2.
Qed.

Lemma ared_diamond t t1 t2 :
  ared1 t t1 ->
  ared1 t t2 ->
  exists t', ared t1 t' /\ ared t2 t'.
Proof.
  intros r1 r2.
  induction r1 in t, t1, t2, r1, r2 |- * using ared1_ind_all.
  - depelim r2.
    + eexists; split; reflexivity.
    + depelim r2.
      exists (body'{0 := arg}).
      split.
      * now apply ared_step, substitution_ared1.
      * apply ared_step, ared_beta.
        admit.
    + exists (body{0 := arg'}).
      split; [admit|].
      now apply ared_step, ared_beta.
  - depelim r2.
    admit.
  - depelim r2.
    admit.
    all: admit.
Admitted.

Lemma confluence {t t1 t2} :
  ared t t1 ->
  ared t t2 ->
  exists t', ared t1 t' /\ ared t2 t'.
Proof.
  rewrite !ared_alt, !clos_rt_rt1n_iff.
  intros r1 r2.
  induction r1 in t, t1, t2, r1, r2 |- *.
  - exists t2.
    now rewrite <- clos_rt_rt1n_iff, <- ared_alt in r2.
  - destruct r2.
    + exists z.
      split; [reflexivity|].
      rewrite <- clos_rt_rt1n_iff, <- ared_alt in r1.
      transitivity y; [|easy].
      now apply ared_step.
    + rewrite <- clos_rt_rt1n_iff, <- ared_alt in r1, r2.
      pose proof (ared_diamond _ _ _ H H0) as (t' & ? & ?).
      apply ared_alt, clos_rt_rt1n, IHr1 in H1 as r2'.
      apply
      apply IHr1 in
      exists t'.
      split.
      * transi
  Admitted.

Lemma ared_normal t t' :
  normal t ->
  ared t t' ->
  t' = t.
Proof.
  rewrite ared_alt.
  intros norm r.
  apply clos_rt_rt1n_iff in r.
  induction r; [easy|].
  now apply norm in H.
Qed.
