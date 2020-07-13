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

Definition lam_body (t : term) : option term :=
  match t with
  | tLambda na body => Some body
  | _ => None
  end.

Equations? normalize (t : term) : term
  by wf (num_subterms t) lt :=
normalize tBox := tBox;
normalize (tRel i) := tRel i;
normalize (tVar id) := tVar id;
normalize (tEvar n ts) := tEvar n (map_in ts (fun t isin => normalize t));
normalize (tLambda na body) := tLambda na (normalize body);
normalize (tLetIn na val body) := tLetIn na (normalize val) (normalize body);
normalize (tApp hd arg) with lam_body (normalize hd) := {
  | Some body with inspect (affinely_used 0 body) := {
    | exist true affin := body{0 := normalize arg};
    | exist false _ := tApp (normalize hd) (normalize arg)
    };
  | None := tApp (normalize hd) (normalize arg)
    (*
  | Some (exist (na, body) eq) with inspect (affinely_used 0 body) := {
    | exist true affin := body{0 := normalize arg};
    | exist false _ := tApp (normalize hd) (normalize arg)
    };
  | None := tApp (normalize hd) (normalize arg) *)
  };
normalize (tConst kn) := tConst kn;
normalize (tConstruct ind c) := tConstruct ind c;
normalize (tCase ind discr brs) :=
  tCase ind (normalize discr) (map_in brs (fun '(ar, t) isin => (ar, normalize t)));
normalize (tProj p t) := tProj p (normalize t);
normalize (tFix defs i) :=
  tFix (map_in defs (fun d isin =>
                       {| dname := dname d;
                          dbody := normalize (dbody d);
                          rarg := rarg d |})) i;
normalize (tCoFix defs i) :=
  tCoFix (map_in defs (fun d isin =>
                         {| dname := dname d;
                            dbody := normalize (dbody d);
                            rarg := rarg d |})) i.
Proof.
  all: try abstract lia.
  - now apply Nat.lt_succ_r, num_subterms_le_sum_In.
  - apply (in_map snd) in isin.
    rewrite <- map_map.
    apply Nat.lt_succ_r.
    pose proof (num_subterms_le_sum_In _ _ isin).
    cbn in *.
    lia.
  - apply (in_map dbody) in isin.
    apply Nat.lt_succ_r.
    rewrite <- map_map.
    now apply num_subterms_le_sum_In.
  - apply (in_map dbody) in isin.
    apply Nat.lt_succ_r.
    rewrite <- map_map.
    now apply num_subterms_le_sum_In.
Qed.

(*
Equations? normalize (t : term) : term by wf (num_subterms t) lt :=
normalize t with normalize_viewc t := {
  | nv_box := tBox;
  | nv_rel i := tRel i;
  | nv_var id := tVar id;
  | nv_evar n ts := tEvar n (map_in ts (fun t isin => normalize t));
  | nv_lambda na body := tLambda na (normalize body);
  | nv_let_in na val body := tLetIn na (normalize val) (normalize body);
  | nv_app_lam na body arg with inspect (affinely_used 0 body) := {
    | exist true affin := normalize (body{0 := arg});
    | exist false _ := tApp (tLambda na (normalize body)) (normalize arg)
    };
  | nv_app hd arg := tApp (normalize hd) (normalize arg);
  | nv_const kn := tConst kn;
  | nv_construct ind c := tConstruct ind c;
  | nv_case ind discr brs := tCase
                               ind
                               (normalize discr)
                               (map_in brs (fun '(ar, t) isin => (ar, normalize t)));
  | nv_proj p t := tProj p (normalize t);
  | nv_fix defs i :=
    tFix (map_in defs (fun d isin =>
                         {| dname := dname d;
                            dbody := normalize (dbody d);
                            rarg := rarg d |})) i;
  | nv_cofix defs i :=
    tCoFix (map_in defs (fun d isin =>
                           {| dname := dname d;
                              dbody := normalize (dbody d);
                              rarg := rarg d |})) i
  }.
Proof.
  all: try abstract lia.
  - now apply Nat.lt_succ_r, num_subterms_le_sum_In.
  - rewrite num_subterms_subst.
    unfold affinely_used in affin.
    propify.
    destruct (count_uses 0 body) as [|[]]; abstract lia.
  - apply (in_map snd) in isin.
    rewrite <- map_map.
    apply Nat.lt_succ_r.
    pose proof (num_subterms_le_sum_In _ _ isin).
    cbn in *.
    abstract lia.
  - apply (in_map dbody) in isin.
    apply Nat.lt_succ_r.
    rewrite <- map_map.
    now apply num_subterms_le_sum_In.
  - apply (in_map dbody) in isin.
    apply Nat.lt_succ_r.
    rewrite <- map_map.
    now apply num_subterms_le_sum_In.
Qed.
*)

Lemma normalize_tBox :
  normalize tBox = tBox.
Proof. reflexivity. Qed.

Hint Rewrite normalize_tBox : normalize.

Lemma normalize_tLambda na body :
  normalize (tLambda na body) = tLambda na (normalize body).
Proof. now simp normalize. Qed.

Hint Rewrite normalize_tLambda : normalize.

Lemma normalize_tLetIn na val body :
  normalize (tLetIn na val body) = tLetIn na (normalize val) (normalize body).
Proof. now simp normalize. Qed.

Hint Rewrite normalize_tLetIn : normalize.

Definition subst_body_affine (t a : term) :=
  match t with
  | tLambda na body => if affinely_used 0 body then
                         Some (body{0 := normalize a})
                       else
                         None
  | _ => None
  end.

Lemma normalize_tApp hd arg :
  normalize (tApp hd arg) =
  match subst_body_affine (normalize hd) arg with
  | Some body => body
  | None => tApp (normalize hd) (normalize arg)
  end.
Proof.
  simp normalize.
  destruct (normalize hd) eqn:hdeq; cbn; rewrite ?hdeq; try easy.
  now destruct (affinely_used _ _).
Qed.

Hint Rewrite normalize_tApp : normalize.

Lemma normalize_mkApps hd args :
  isLambda (normalize hd) = false ->
  normalize (mkApps hd args) =
  mkApps (normalize hd) (map normalize args).
Proof.
  intros not_lam.
  induction args in hd, args, not_lam |- *; [easy|].
  cbn in *.
  rewrite IHargs.
  rewrite normalize_tApp.
  now destruct (normalize hd).

  rewrite normalize_tApp.
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
