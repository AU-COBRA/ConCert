From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import WcbvEvalType.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import Eqdep_dec.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import EInversion.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Template Require Import utils.

Import ListNotations.
Set Equations Transparent.

Lemma eval_tApp_head Σ hd arg v :
  Σ ⊢ tApp hd arg ▷ v ->
  ∑ hdv, Σ ⊢ hd ▷ hdv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma eval_tApp_arg Σ hd arg v :
  Σ ⊢ tApp hd arg ▷ v ->
  ∑ argv, Σ ⊢ arg ▷ argv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma eval_mkApps_head Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  ∑ hdv, Σ ⊢ hd ▷ hdv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  specialize (IHargs _ _ ev) as (? & ?).
  now apply eval_tApp_head in e.
Qed.

Lemma eval_mkApps_args Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  ∑ argsv, All2 (eval Σ) args argsv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  apply eval_mkApps_head in ev as ev_hd.
  destruct ev_hd as (hdv & ev_hd).
  specialize (IHargs _ _ ev) as (argsv & all).
  apply eval_tApp_arg in ev_hd as (argv & ev_arg).
  exists (argv :: argsv).
  now constructor.
Qed.

Lemma eval_tApp_heads Σ hd hd' hdv arg v :
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ tApp hd arg ▷ v ->
  Σ ⊢ tApp hd' arg ▷ v.
Proof.
  intros ev_hd ev_hd' ev_app.
  depind ev_app.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_box.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_beta.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix_value.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_app_cong.
  - easy.
Qed.

Derive Signature for eval.
Derive NoConfusionHom for term.

Lemma eval_tLetIn_inv Σ na val body res :
  Σ ⊢ tLetIn na val body ▷ res ->
  ∑ val_res,
    Σ ⊢ val ▷ val_res ×
    Σ ⊢ csubst val_res 0 body ▷ res.
Proof. intros ev; depelim ev; easy. Qed.

Lemma eval_tLambda_inv Σ na body v :
  Σ ⊢ tLambda na body ▷ v ->
  v = tLambda na body.
Proof. now intros ev; depelim ev. Qed.

Lemma eval_tApp_tLambda_inv Σ na body a v :
  Σ ⊢ tApp (tLambda na body) a ▷ v ->
  ∑ av,
    Σ ⊢ a ▷ av ×
    Σ ⊢ csubst av 0 body ▷ v.
Proof.
  intros ev.
  depelim ev.
  - now apply eval_tLambda_inv in ev1.
  - apply eval_tLambda_inv in ev1.
    inversion ev1; subst; clear ev1.
    easy.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - now apply eval_tLambda_inv in ev1 as ->.
  - easy.
Qed.

Lemma eval_mkApps_heads Σ hd hd' hdv args v :
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ mkApps hd args ▷ v ->
  Σ ⊢ mkApps hd' args ▷ v.
Proof.
  revert hd hd' hdv v.
  induction args as [|a args]; intros hd hd' hdv v ev_hd ev_hd' ev.
  - cbn in *.
    now rewrite (eval_deterministic ev ev_hd) in *.
  - cbn in *.
    apply eval_mkApps_head in ev as ev_app_hd.
    destruct ev_app_hd as (app_hdv & ev_app_hd).
    eapply IHargs.
    2: {
      eapply eval_tApp_heads; [| |exact ev_app_hd].
      all: easy.
    }
    + easy.
    + easy.
Qed.

Definition env_closed (Σ : EAst.global_declarations) : bool :=
  forallb (decl_closed ∘ snd) Σ.

Lemma closed_constant Σ kn cst body :
  env_closed Σ ->
  ETyping.declared_constant Σ kn cst ->
  EAst.cst_body cst = Some body ->
  closed body.
Proof.
  intros env_clos decl_const body_eq.
  unfold ETyping.declared_constant in decl_const.
  rewrite lookup_env_find in decl_const.
  destruct (find _ _) eqn:find; [|easy].
  apply find_some in find.
  eapply forallb_forall in env_clos; [|exact (proj1 find)].
  destruct p.
  cbn in *.
  noconf decl_const.
  cbn in *.
  now rewrite body_eq in env_clos.
Qed.

Lemma closed_unfold_fix mfix idx narg fn :
  closed (tFix mfix idx) ->
  ETyping.unfold_fix mfix idx = Some (narg, fn) ->
  closed fn.
Proof.
  cbn.
  intros clos_fix fix_eq.
  rewrite Nat.add_0_r in *.
  unfold ETyping.unfold_fix in *.
  destruct (nth_error mfix idx) eqn:Heq; [|easy].
  noconf fix_eq.
  eapply closedn_subst0.
  - clear Heq.
    unfold ETyping.fix_subst.
    generalize #|mfix|.
    induction n as [|n IH]; [easy|].
    constructor.
    + cbn.
      now rewrite Nat.add_0_r.
    + easy.
  - apply nth_error_In in Heq.
    apply forallb_Forall in clos_fix.
    rewrite Forall_forall in clos_fix.
    now rewrite ETyping.fix_subst_length.
Qed.

Lemma closed_unfold_cofix mfix idx narg fn :
  closed (tFix mfix idx) ->
  ETyping.unfold_cofix mfix idx = Some (narg, fn) ->
  closed fn.
Proof.
  cbn.
  intros clos_fix fix_eq.
  rewrite Nat.add_0_r in *.
  unfold ETyping.unfold_cofix in *.
  destruct (nth_error mfix idx) eqn:Heq; [|easy].
  noconf fix_eq.
  eapply closedn_subst0.
  - clear Heq.
    unfold ETyping.cofix_subst.
    generalize #|mfix|.
    induction n as [|n IH]; [easy|].
    constructor.
    + cbn.
      now rewrite Nat.add_0_r.
    + easy.
  - apply nth_error_In in Heq.
    apply forallb_Forall in clos_fix.
    rewrite Forall_forall in clos_fix.
    now rewrite ETyping.cofix_subst_length.
Qed.

Lemma all_closed Σ args args' :
  Forall (closedn 0) args ->
  All2 (eval Σ) args args' ->
  Forall2 (fun t v => closed t -> closed v) args args' ->
  Forall (closedn 0) args'.
Proof.
  intros args_clos args_eval impl_clos.
  induction args_eval; [easy|].
  depelim args_clos.
  depelim impl_clos.
  easy.
Qed.

Lemma closed_iota_red pars c args brs :
  Forall (fun a => closed a) args ->
  Forall (fun t => closed t.2) brs ->
  closed (ETyping.iota_red pars c args brs).
Proof.
  intros clos_args clos_brs.
  unfold ETyping.iota_red.
  apply closed_mkApps.
  - rewrite nth_nth_error.
    destruct (nth_error _ _) eqn:nth; [|easy].
    now eapply nth_error_forall in nth; [|eassumption].
  - now apply Forall_skipn.
Qed.

Lemma closed_cunfold_fix defs n narg f :
  cunfold_fix defs n = Some (narg, f) ->
  closed (tFix defs n) ->
  closed f.
Proof.
  intros eq clos.
  rewrite <- closed_unfold_fix_cunfold_eq in eq by easy.
  now eapply closed_unfold_fix.
Qed.

Lemma closed_cunfold_cofix defs n narg f :
  cunfold_cofix defs n = Some (narg, f) ->
  closed (tCoFix defs n) ->
  closed f.
Proof.
  intros eq clos.
  rewrite <- closed_unfold_cofix_cunfold_eq in eq by easy.
  now eapply closed_unfold_cofix.
Qed.

Lemma eval_closed Σ t v :
  Σ ⊢ t ▷ v ->
  env_closed Σ ->
  closed t ->
  closed v.
Proof.
  intros ev env_clos clos.
  induction ev; cbn in *; propify.
  - easy.
  - apply IHev3.
    now apply closed_csubst.
  - apply IHev2.
    now apply closed_csubst.
  - apply IHev2.
    apply closed_iota_red.
    + now eapply closed_mkApps_args.
    + now apply forallb_Forall.
  - subst brs.
    cbn in *.
    propify.
    apply IHev2.
    apply closed_mkApps; [easy|].
    clear.
    induction n; [constructor|].
    constructor; easy.
  - apply IHev3.
    split; [|easy].
    destruct clos as (clos & _).
    specialize (IHev1 clos).
    apply closed_mkApps_inv in IHev1 as (? & ?).
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_fix.
  - easy.
  - apply IHev.
    split; [|easy].
    destruct clos as (clos & _).
    apply closed_mkApps_inv in clos.
    cbn in *.
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_cofix.
  - apply IHev.
    apply closed_mkApps_inv in clos.
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_cofix.
  - apply IHev.
    now eapply closed_constant.
  - apply IHev2.
    apply closed_mkApps_args in IHev1; [|easy].
    rewrite nth_nth_error in *.
    destruct (nth_error _ _) eqn:nth_eq.
    + apply nth_error_In in nth_eq.
      rewrite Forall_forall in IHev1.
      now apply IHev1.
    + easy.
  - easy.
  - easy.
  - easy.
Qed.

Fixpoint deriv_length {Σ t v} (ev : Σ ⊢ t ▷ v) : nat :=
  match ev with
  | eval_atom _ _ => 1
  | red_cofix_case _ _ _ _ _ _ _ _ _ ev
  | red_cofix_proj _ _ _ _ _ _ _ _ ev
  | eval_delta _ _ _ _ _ _ ev
  | eval_proj_box _ _ _ _ ev => S (deriv_length ev)
  | eval_box _ _ _ ev1 ev2
  | eval_zeta _ _ _ _ _ ev1 ev2
  | eval_iota _ _ _ _ _ _ _ ev1 ev2
  | eval_iota_sing _ _ _ _ _ _ _ ev1 _ ev2
  | eval_fix_value _ _ _ _ _ _ _ _ ev1 ev2 _ _
  | eval_proj _ _ _ _ _ _ ev1 ev2
  | eval_app_cong _ _ _ _ ev1 _ ev2 => S (deriv_length ev1 + deriv_length ev2)
  | eval_beta _ _ _ _ _ _ ev1 ev2 ev3
  | eval_fix _ _ _ _ _ _ _ _ _ ev1 ev2 _ _ _ ev3 =>
    S (deriv_length ev1 + deriv_length ev2 + deriv_length ev3)
  end.

Lemma deriv_length_min {Σ t v} (ev : Σ ⊢ t ▷ v) :
  1 <= deriv_length ev.
Proof. destruct ev; cbn in *; lia. Qed.

Lemma eval_tApp_deriv {Σ hd arg v} (ev : Σ ⊢ tApp hd arg ▷ v) :
  ∑ hdv (ev_hd : Σ ⊢ hd ▷ hdv) argv (ev_arg : Σ ⊢ arg ▷ argv),
    S (deriv_length ev_hd + deriv_length ev_arg) <= deriv_length ev.
Proof.
  depelim ev; cbn in *;
    try now eexists _, ev1, _, ev2.
  easy.
Qed.

Fixpoint sum_deriv_lengths {Σ ts tsv} (a : All2 (eval Σ) ts tsv) : nat :=
  match a with
  | All2_nil => 0
  | All2_cons _ _ _ _ ev a => deriv_length ev + sum_deriv_lengths a
  end.

Fixpoint app_All2
         {A B}
         {T : A -> B -> Type}
         {la lb la' lb'}
         (a1 : All2 T la lb)
         (a2 : All2 T la' lb') : All2 T (la ++ la') (lb ++ lb').
Proof.
  destruct a1.
  - exact a2.
  - refine (All2_cons t _).
    exact (app_All2 _ _ _ _ _ _ _ a1 a2).
Defined.

Lemma eval_mkApps_deriv {Σ hd args v} (ev : Σ ⊢ mkApps hd args ▷ v) :
  ∑ hdv (ev_hd : Σ ⊢ hd ▷ hdv) argsv (ev_args : All2 (eval Σ) args argsv),
    deriv_length ev_hd + #|args| + sum_deriv_lengths ev_args <= deriv_length ev.
Proof.
  revert hd v ev.
  induction args; intros hd v ev; cbn in *.
  - exists _, ev, [], All2_nil.
    now cbn.
  - specialize (IHargs _ _ ev) as (hdv & ev_hd & argsv & ev_args & len).
    specialize (eval_tApp_deriv ev_hd) as (hdv' & ev_hdv' & argv & ev_argv & len').
    exists _, ev_hdv', (argv :: argsv).
    exists (All2_cons ev_argv ev_args).
    cbn in *.
    lia.
Qed.

Lemma sum_deriv_lengths_app_All2 {Σ}
      {ts tsv} (a : All2 (eval Σ) ts tsv)
      {ts' tsv'} (a' : All2 (eval Σ) ts' tsv') :
  sum_deriv_lengths (app_All2 a a') = sum_deriv_lengths a + sum_deriv_lengths a'.
Proof.
  induction a in ts', tsv', a' |- *; [easy|].
  cbn in *.
  now rewrite IHa.
Qed.

Ltac determ :=
  repeat
    match goal with
    | [ev1 : ?Σ ⊢ ?t ▷ ?v, ev2 : ?Σ ⊢ ?t ▷ ?v' |- _] =>
      match v with
      | v' => fail 1
      | _ => idtac
      end;
      match goal with
      | [H: v = v' |- _] => fail 1
      | [H: v' = v |- _] => fail 1
      | _ => idtac
      end;
      pose proof (eval_deterministic ev1 ev2)
    end;
  subst.

Lemma term_forall_list_rect :
  forall P : term -> Type,
    (P tBox) ->
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall (n : name) (t : term), P t -> P (tLambda n t)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> P (tLetIn n t t0)) ->
    (forall t u : term, P t -> P u -> P (tApp t u)) ->
    (forall s, P (tConst s)) ->
    (forall (i : inductive) (n : nat), P (tConstruct i n)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall l : list (nat * term),
            tCaseBrsProp P l -> P (tCase p t l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), All (fun x => P (dbody x)) m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), All (fun x => P (dbody x)) m -> P (tCoFix m n)) ->
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.

  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  apply auxt.

  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  apply auxt.
Defined.

(* We need UIP below *)
Instance EqDec_term : EqDec term.
Proof.
  intros x.
  induction x using term_forall_list_rect; intros []; try solve [right; discriminate].
  - now left.
  - destruct (eq_dec n n0); subst; [left|right]; congruence.
  - destruct (eq_dec i i0); subst; [left|right]; congruence.
  - destruct (eq_dec n n0); subst; [|right; congruence].
    destruct (eq_dec #|l| #|l0|); [|right; congruence].
    enough ({l = l0} + {l <> l0}).
    { destruct H0; [left|right]; congruence. }
    induction H in l0, e |- *.
    + destruct l0; [|easy].
      now left.
    + destruct l0; [easy|].
      destruct (p t); subst; [|right; congruence].
      destruct (IHAll l0 ltac:(easy)); subst; [left|right]; congruence.
  - destruct (eq_dec n n0); subst; [|right; congruence].
    destruct (IHx t); subst; [left|right]; congruence.
  - destruct (eq_dec n n0); subst; [|right; congruence].
    destruct (IHx1 t); subst; [|right; congruence].
    destruct (IHx2 t0); subst; [left|right]; congruence.
  - destruct (IHx1 t); subst; [|right; congruence].
    destruct (IHx2 t0); subst; [left|right]; congruence.
  - destruct (eq_dec s k); subst; [left|right]; congruence.
  - destruct (eq_dec i i0); subst; [|right; congruence].
    destruct (eq_dec n n0); subst; [left|right]; congruence.
  - destruct (eq_dec p p0); subst; [|right; congruence].
    destruct (IHx t); subst; [|right; congruence].
    destruct (eq_dec #|l| #|l0|); [|right; congruence].
    enough ({l = l0} + {l <> l0}).
    { destruct H; subst; [left|right]; congruence. }
    induction X in l0, e |- *.
    + destruct l0; [|easy].
      now left.
    + destruct l0; cbn in *; [easy|].
      destruct (p p1.2); [|right; congruence].
      destruct (eq_dec x.1 p1.1); [|right; congruence].
      destruct (IHX l0 ltac:(easy)); subst; [|right; congruence].
      destruct x, p1; cbn in *; subst.
      now left.
  - destruct (eq_dec s p); subst; [|right; congruence].
    destruct (IHx t); [left|right]; congruence.
  - destruct (eq_dec n n0); subst; [|right; congruence].
    destruct (eq_dec #|m| #|m0|); [|right; congruence].
    enough ({m = m0} + {m <> m0}).
    { destruct H0; subst; [left|right]; congruence. }
    induction H in m0, e |- *.
    + destruct m0; [|easy].
      now left.
    + destruct m0; cbn in *; [easy|].
      destruct (eq_dec (dname x) (dname d)); [|right; congruence].
      destruct (p (dbody d)); [|right; congruence].
      destruct (eq_dec (rarg x) (rarg d)); [|right; congruence].
      destruct (IHAll m0 ltac:(easy)); subst; [|right; congruence].
      destruct x, d; cbn in *; subst.
      now left.
  - destruct (eq_dec n n0); subst; [|right; congruence].
    destruct (eq_dec #|m| #|m0|); [|right; congruence].
    enough ({m = m0} + {m <> m0}).
    { destruct H0; subst; [left|right]; congruence. }
    induction H in m0, e |- *.
    + destruct m0; [|easy].
      now left.
    + destruct m0; cbn in *; [easy|].
      destruct (eq_dec (dname x) (dname d)); [|right; congruence].
      destruct (p (dbody d)); [|right; congruence].
      destruct (eq_dec (rarg x) (rarg d)); [|right; congruence].
      destruct (IHAll m0 ltac:(easy)); subst; [|right; congruence].
      destruct x, d; cbn in *; subst.
      now left.
Qed.

Lemma deriv_lengths_eq {Σ t v} (ev1 ev2 : Σ ⊢ t ▷ v) :
  deriv_length ev1 = deriv_length ev2.
Proof.
  revert ev2.
  depind ev1; intros ev2; cbn in *.
  - depelim ev2; cbn in *; determ; try congruence; try solve_discr.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    noconf H0.
    intuition.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    + noconf H.
      intuition.
    + apply eval_mkApps_tCoFix in ev1_1 as H.
      destruct H; solve_discr.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    + noconf e0.
      intuition.
    + apply eval_mkApps_tCoFix in ev1_1 as H.
      destruct H; solve_discr.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    + noconf H.
      rewrite e1 in e.
      noconf e.
      intuition.
    + noconf H.
      rewrite e1 in e.
      noconf e.
      destruct o as [|(_ & ?)]; [easy|].
      now rewrite i in H.
    + rewrite isFixApp_mkApps in i0 by easy.
      cbn in *.
      now rewrite Bool.orb_true_r in i0.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    + noconf H.
      rewrite e0 in e.
      noconf e.
      destruct o as [|(_ & ?)]; [easy|].
      now rewrite i in H.
    + apply mkApps_eq_inj in e' as H'; try easy.
      destruct H' as (H' & <-).
      noconf H'.
      assert (e' = eq_refl) as -> by (now apply uip).
      cbn in *.
      subst ev0.
      rewrite e0 in e.
      noconf e.
      cbn in *.
      intuition.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    + apply eval_mkApps_tCoFix in ev2_1 as H.
      destruct H; solve_discr.
    + apply eval_mkApps_tCoFix in ev2_1 as H.
      destruct H; solve_discr.
    + apply mkApps_eq_inj in e' as H'; try easy.
      destruct H' as (H' & <-).
      noconf H'.
      assert (e' = eq_refl) as -> by (now apply uip).
      cbn in *.
      subst ev0.
      rewrite e0 in e.
      noconf e.
      cbn in *.
      intuition.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    + apply mkApps_eq_inj in e1 as H'; try easy.
      destruct H' as (H' & <-).
      noconf H'.
      rewrite e0 in e.
      noconf e.
      assert (e1 = eq_refl) as -> by (now apply uip).
      cbn in *.
      subst ev0.
      cbn in *.
      intuition.
    + apply eval_mkApps_tCoFix in ev2_1 as H.
      destruct H; solve_discr.
    + apply eval_mkApps_tCoFix in ev2 as H.
      destruct H; solve_discr.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    unfold ETyping.declared_constant in *.
    assert (body0 = body) as -> by congruence.
    intuition.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    apply eval_mkApps_tCoFix in ev1_1 as H.
    destruct H; solve_discr.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    apply eval_mkApps_tCoFix in ev1 as H.
    destruct H; solve_discr.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    rewrite isFixApp_mkApps in i by easy.
    cbn in *.
    rewrite Bool.orb_true_r in i.
    now cbn in *.
  - depelim ev2; cbn in *; determ; cbn in *; try congruence; try solve_discr.
    assert (e = eq_refl) as -> by (now apply uip).
    cbn in *.
    now subst ev0.
Qed.

Lemma All2_split_eq
      {X Y} {T : X -> Y -> Type}
      {xs ys xs' ys'}
      (a : All2 T (xs ++ xs') (ys ++ ys')) :
  #|xs| = #|ys| ->
  ∑ apref asuf, a = app_All2 apref asuf.
Proof.
  intros eq.
  induction xs in xs, ys, xs', ys', a, eq |- *.
  - destruct ys; [|easy].
    cbn in *.
    now exists All2_nil, a.
  - destruct ys; [easy|].
    cbn in *.
    depelim a.
    specialize (IHxs ys xs' ys' a ltac:(easy)) as (apref & asuf & ->).
    now exists (All2_cons t apref), asuf.
Qed.

Lemma All2_rev_rect X Y (T : X -> Y -> Type) (P : forall xs ys, All2 T xs ys -> Type) :
  P [] [] All2_nil ->
  (forall x y xs ys (t : T x y) (a : All2 T xs ys),
      P xs ys a -> P (xs ++ [x]) (ys ++ [y]) (app_All2 a (All2_cons t All2_nil))) ->
  forall xs ys (a : All2 T xs ys), P xs ys a.
Proof.
  intros nil_case snoc_case.
  induction xs using MCList.rev_ind; intros ys a.
  - now depelim a.
  - destruct ys as [|y ys _] using MCList.rev_ind.
    + apply All2_length in a as ?.
      rewrite app_length in *.
      now cbn in *.
    + unshelve epose proof (All2_split_eq a _) as (? & ? & ->).
      * apply All2_length in a.
        rewrite !app_length in a.
        now cbn in *.
      * depelim x1.
        depelim x3.
        apply snoc_case.
        apply IHxs.
Qed.

Inductive All2_eval_app_spec Σ : list term -> term ->
                                 list term -> term ->
                                 forall ts tsv, All2 (eval Σ) ts tsv -> Type :=
| All2_eval_app_intro {ts tsv} (a : All2 (eval Σ) ts tsv)
                      {x xv} (evx : Σ ⊢ x ▷ xv) :
    All2_eval_app_spec
      Σ ts x tsv xv
      (ts ++ [x])
      (tsv ++ [xv])
      (app_All2 a (All2_cons evx All2_nil)).

Derive Signature for All2.
Derive NoConfusionHom for All2.

Lemma All2_eval_snoc_elim
      {Σ ts tsv x xv} (a : All2 (eval Σ) (ts ++ [x]) (tsv ++ [xv])) :
  All2_eval_app_spec Σ ts x tsv xv _ _ a.
Proof.
  unshelve epose proof (All2_split_eq a _) as (? & ev & ->).
  - apply All2_length in a.
    rewrite !app_length in a.
    now cbn in *.
  - depelim ev.
    depelim ev.
    constructor.
Qed.

Lemma eval_tApp_heads_deriv {Σ hd hd' hdv arg v}
      (ev_hd : Σ ⊢ hd ▷ hdv)
      (ev_hd' : Σ ⊢ hd' ▷ hdv)
      (ev_app : Σ ⊢ tApp hd arg ▷ v) :
  ∑ (ev_app' : Σ ⊢ tApp hd' arg ▷ v),
    (deriv_length ev_app + deriv_length ev_hd' = deriv_length ev_app' + deriv_length ev_hd)%nat.
Proof.
  depind ev_app.
  - pose proof (eval_deterministic ev_hd ev_app1) as ->.
    pose proof (deriv_lengths_eq ev_hd ev_app1).
    unshelve eexists _; [now eapply eval_box|].
    cbn; lia.
  - pose proof (eval_deterministic ev_hd ev_app1) as ->.
    pose proof (deriv_lengths_eq ev_hd ev_app1).
    unshelve eexists _; [now eapply eval_beta|].
    cbn; lia.
  - pose proof (eval_deterministic ev_hd ev_app1) as ->.
    pose proof (deriv_lengths_eq ev_hd ev_app1).
    unshelve eexists _; [now eapply eval_fix|].
    cbn; lia.
  - pose proof (eval_deterministic ev_hd ev_app1) as ->.
    pose proof (deriv_lengths_eq ev_hd ev_app1).
    unshelve eexists _; [now eapply eval_fix_value|].
    cbn; lia.
  - pose proof (eval_deterministic ev_hd ev_app1) as ->.
    pose proof (deriv_lengths_eq ev_hd ev_app1).
    unshelve eexists _; [now eapply eval_app_cong|].
    cbn; lia.
  - easy.
Qed.

Lemma eval_mkApps_heads_deriv {Σ hd hd' hdv args v}
      (ev_hd : Σ ⊢ hd ▷ hdv)
      (ev_hd' : Σ ⊢ hd' ▷ hdv)
      (ev_apps : Σ ⊢ mkApps hd args ▷ v) :
  ∑ (ev_apps' : Σ ⊢ mkApps hd' args ▷ v),
  (deriv_length ev_apps + deriv_length ev_hd' = deriv_length ev_apps' + deriv_length ev_hd)%nat.
Proof.
  revert hd hd' hdv v ev_hd ev_hd' ev_apps.
  induction args using MCList.rev_ind; intros; cbn in *.
  - pose proof (eval_deterministic ev_hd ev_apps) as ->.
    exists ev_hd'.
    now pose proof (deriv_lengths_eq ev_hd ev_apps).
  - revert ev_apps; rewrite !mkApps_app; intros.
    cbn in *.
    eapply eval_tApp_head in ev_apps as ev_apps'.
    destruct ev_apps' as (? & ev_apps').
    specialize (IHargs _ _ _ _ ev_hd ev_hd' ev_apps') as (ev_apps'' & ?).
    pose proof (eval_tApp_heads_deriv ev_apps' ev_apps'' ev_apps) as (ev & ?).
    exists ev.
    lia.
Qed.
