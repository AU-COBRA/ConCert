(* This file copies the erasure correctness proof from MetaCoq and
   strengthens it for our use where where we do not erase full
   environments but rather only dependencies.
   The admitted proofs in this file comes from the MetaCoq development. *)

From Coq Require Import Bool String List Program.Basics Program.Tactics ZArith.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.Erasure Require Import ELiftSubst ETyping EWcbvEval Extract Prelim
     ESubstitution EInversion EArities ErasureCorrectness.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
  PCUICWeakening PCUICSubstitution PCUICArities
  PCUICWcbvEval PCUICSR  PCUICInversion
  PCUICUnivSubstitution PCUICElimination PCUICCanonicity
  PCUICUnivSubst PCUICWeakeningEnv PCUICCumulativity.
From ConCert.Extraction Require Import Aux.

Require Import Equations.Prop.DepElim.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Local Set Keyed Unification.

Import MonadNotation.

Require Import Lia.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance config.extraction_checker_flags.

Hint Resolve wf_ext_wk_wf : core.
Hint Resolve Is_type_conv_context : core.

Transparent PCUICParallelReductionConfluence.construct_cofix_discr.

Import E.
Inductive erases_deps (Σ : PA.global_env) (Σ' : global_declarations) : term -> Prop :=
| erases_deps_tBox : erases_deps Σ Σ' tBox
| erases_deps_tRel i : erases_deps Σ Σ' (tRel i)
| erases_deps_tVar n : erases_deps Σ Σ' (tVar n)
| erases_deps_tEvar m l :
    Forall (erases_deps Σ Σ') l ->
    erases_deps Σ Σ' (tEvar m l)
| erases_deps_tLambda na body :
    erases_deps Σ Σ' body ->
    erases_deps Σ Σ' (tLambda na body)
| erases_deps_tLetIn na val body :
    erases_deps Σ Σ' val ->
    erases_deps Σ Σ' body ->
    erases_deps Σ Σ' (tLetIn na val body)
| erases_deps_tApp hd arg :
    erases_deps Σ Σ' hd ->
    erases_deps Σ Σ' arg ->
    erases_deps Σ Σ' (tApp hd arg)
| erases_deps_tConst kn cb cb' :
    PCUICTyping.declared_constant Σ kn cb ->
    ETyping.declared_constant Σ' kn cb' ->
    erases_constant_body (Σ, cst_universes cb) cb cb' ->
    (forall body, cst_body cb' = Some body -> erases_deps Σ Σ' body) ->
    erases_deps Σ Σ' (tConst kn)
| erases_deps_tConstruct ind c :
    erases_deps Σ Σ' (tConstruct ind c)
| erases_deps_tCase p discr brs :
    erases_deps Σ Σ' discr ->
    Forall (fun br => erases_deps Σ Σ' br.2) brs ->
    erases_deps Σ Σ' (tCase p discr brs)
| erases_deps_tProj p t :
    erases_deps Σ Σ' t ->
    erases_deps Σ Σ' (tProj p t)
| erases_deps_tFix defs i :
    Forall (fun d => erases_deps Σ Σ' (dbody d)) defs ->
    erases_deps Σ Σ' (tFix defs i)
| erases_deps_tCoFix defs i :
    Forall (fun d => erases_deps Σ Σ' (dbody d)) defs ->
    erases_deps Σ Σ' (tCoFix defs i).

Derive Signature for erases_deps.
Derive Signature for Forall.

Lemma erases_deps_mkApps Σ Σ' hd args :
  erases_deps Σ Σ' hd ->
  Forall (erases_deps Σ Σ') args ->
  erases_deps Σ Σ' (mkApps hd args).
Proof.
  intros er erall.
  induction args using rev_ind; [easy|].
  rewrite !emkApps_snoc.
  apply Forall_app in erall as (? & ?).
  depelim H0.
  now constructor.
Qed.

Lemma erases_deps_mkApps_inv Σ Σ' hd args :
  erases_deps Σ Σ' (mkApps hd args) ->
  erases_deps Σ Σ' hd /\ Forall (erases_deps Σ Σ') args.
Proof.
  intros er.
  induction args using rev_ind; [easy|].
  rewrite emkApps_snoc in *.
  depelim er.
  intuition auto.
  now apply Forall_app_inv.
Qed.

Lemma erases_deps_lift Σ Σ' n k t :
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (lift n k t).
Proof.
  intros er.
  induction t in k, t, er |- * using EInduction.term_forall_list_ind; cbn in *; auto.
  - now destruct (_ <=? _); constructor.
  - depelim er.
    constructor.
    induction H; cbn in *; [easy|].
    now depelim H0.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    constructor; [easy|].
    induction X; [easy|].
    depelim H.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now constructor.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
Qed.

Lemma erases_deps_subst Σ Σ' s k t :
  All (erases_deps Σ Σ') s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (subst s k t).
Proof.
  intros aller er.
  induction t in k, aller, er |- * using EInduction.term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _); [|now constructor].
    destruct nth_error eqn:nth; [|now constructor].
    eapply All_nth_error in nth; [|now eauto].
    now apply erases_deps_lift.
  - depelim er.
    constructor.
    induction H; [easy|].
    depelim H0.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    constructor; [easy|].
    induction X; [easy|].
    depelim H.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now constructor.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
Qed.

Lemma erases_deps_subst1 Σ Σ' t k u :
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' u ->
  erases_deps Σ Σ' (subst1 t k u).
Proof.
  intros.
  apply erases_deps_subst; [|easy].
  now constructor.
Qed.

Lemma erases_deps_csubst Σ Σ' s k t :
  erases_deps Σ Σ' s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (ECSubst.csubst s k t).
Proof.
  intros aller er.
  induction t in k, aller, er |- * using EInduction.term_forall_list_ind; cbn in *; auto.
  - destruct (_ ?= _); try constructor; easy.
  - depelim er.
    constructor.
    induction H; [easy|].
    depelim H0.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    now constructor.
  - depelim er.
    constructor; [easy|].
    induction X; [easy|].
    depelim H.
    constructor; [|easy].
    now cbn.
  - depelim er.
    now constructor.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
  - depelim er.
    constructor.
    induction H in k, H, H0 |- *; [easy|].
    cbn in *.
    rewrite <- !Nat.add_succ_r.
    depelim H0.
    constructor; [|easy].
    now apply H.
Qed.

Lemma erases_deps_substl Σ Σ' s t :
  Forall (fun s => erases_deps Σ Σ' s) s ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' (Ee.substl s t).
Proof.
  intros all exp.
  unfold Ee.substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_snoc in all.
  now apply erases_deps_csubst.
Qed.

Lemma Forall_erases_deps_fix_subst Σ Σ' defs :
  Forall (erases_deps Σ Σ' ∘ dbody) defs ->
  Forall (erases_deps Σ Σ') (ETyping.fix_subst defs).
Proof.
  intros all.
  unfold ETyping.fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now constructor.
  - now apply IHl.
Qed.

Lemma Forall_erases_deps_cofix_subst Σ Σ' defs :
  Forall (erases_deps Σ Σ' ∘ dbody) defs ->
  Forall (erases_deps Σ Σ') (ETyping.cofix_subst defs).
Proof.
  intros all.
  unfold ETyping.cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now constructor.
  - now apply IHl.
Qed.

Lemma erases_deps_cunfold_fix Σ Σ' defs i narg f :
  Ee.cunfold_fix defs i = Some (narg, f) ->
  Forall (fun d => erases_deps Σ Σ' (dbody d)) defs ->
  erases_deps Σ Σ' f.
Proof.
  intros cuf all.
  unfold Ee.cunfold_fix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply erases_deps_substl; [|easy].
  now apply Forall_erases_deps_fix_subst.
Qed.

Lemma erases_deps_cunfold_cofix Σ Σ' defs i narg f :
  Ee.cunfold_cofix defs i = Some (narg, f) ->
  Forall (fun d => erases_deps Σ Σ' (dbody d)) defs ->
  erases_deps Σ Σ' f.
Proof.
  intros cuf all.
  unfold Ee.cunfold_cofix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply erases_deps_substl; [|easy].
  now apply Forall_erases_deps_cofix_subst.
Qed.

Lemma erases_deps_fix_subst Σ Σ' defs :
  Forall (fun d => erases_deps Σ Σ' (E.dbody d)) defs ->
  Forall (erases_deps Σ Σ') (ETyping.fix_subst defs).
Proof.
  intros all.
  unfold ETyping.fix_subst.
  induction #|defs|; [easy|].
  cbn in *.
  constructor; [|easy].
  constructor.
  easy.
Qed.

Lemma erases_deps_eval Σ t v Σ' :
  Σ' ⊢ t ▷ v ->
  erases_deps Σ Σ' t ->
  erases_deps Σ Σ' v.
Proof.
  intros ev er.
  induction ev in t, v, ev, er |- *; cbn in *.
  - now constructor.
  - depelim er.
    apply IHev3.
    apply erases_deps_csubst; [easy|].
    intuition auto.
    now depelim H.
  - depelim er.
    now apply IHev2, erases_deps_csubst.
  - depelim er.
    apply IHev2.
    unfold ETyping.iota_red.
    apply erases_deps_mkApps.
    + rewrite nth_nth_error.
      destruct nth_error eqn:nth; [|now constructor].
      eapply nth_error_forall in nth; [|now eauto].
      assumption.
    + intuition auto.
      apply erases_deps_mkApps_inv in H0.
      now apply Forall_skipn.
  - depelim er.
    subst brs; cbn in *.
    depelim H0.
    cbn in *.
    apply IHev2.
    apply erases_deps_mkApps; [easy|].
    apply Forall_repeat.
    now constructor.
  - depelim er.
    intuition auto.
    eapply erases_deps_mkApps_inv in H2 as (? & ?).
    depelim H2.
    apply IHev3.
    constructor; [|easy].
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_fix.
  - depelim er.
    clear H0.
    intuition auto.
    apply erases_deps_mkApps_inv in H0 as (? & ?).
    constructor; [|easy].
    now apply erases_deps_mkApps.
  - depelim er.
    apply erases_deps_mkApps_inv in er as (? & ?).
    depelim H1.
    apply IHev.
    constructor; [|easy].
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_cofix.
  - depelim er.
    apply erases_deps_mkApps_inv in er as (? & ?).
    depelim H0.
    apply IHev.
    constructor.
    apply erases_deps_mkApps; [|easy].
    now eapply erases_deps_cunfold_cofix.
  - depelim er.
    now apply IHev, H3.
  - depelim er.
    intuition auto.
    apply erases_deps_mkApps_inv in H as (? & ?).
    apply IHev2.
    rewrite nth_nth_error.
    destruct nth_error eqn:nth; [|now constructor].
    now eapply nth_error_forall in nth.
  - constructor.
  - depelim er.
    now constructor.
  - easy.
Qed.

Hint Resolve erases_deps_subst1 erases_deps_eval erases_deps_mkApps : core.

Import PA.

Lemma erases_correct Σ t T t' v Σ' :
  extraction_pre Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ t' ->
  erases_deps Σ Σ' t' ->
  Σ |-p t ▷ v ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ Σ' ⊢ t' ▷ v'.
Proof.
  intros pre Hty He Heg H.
  revert T Hty t' He Heg.
  induction H; intros T Hty t' He Heg; inv pre.
  - assert (Hty' := Hty).
    assert (eval Σ (PCUICAst.tApp f a) res) by eauto.
    eapply inversion_App in Hty as (? & ? & ? & ? & ? & ?); eauto.
    inv He.

    + depelim Heg.
      eapply IHeval1 in H4 as (vf' & Hvf' & He_vf'); eauto.
      eapply IHeval2 in H6 as (vu' & Hvu' & He_vu'); eauto.
      pose proof (subject_reduction_eval Σ _ _ _ (wf_ext_wf _ extr_env_wf') t0 H).
      eapply inversion_Lambda in X0 as (? & ? & ? & ? & ?); eauto.
      assert (Σ ;;; [] |- a' : t). {
        eapply subject_reduction_eval; eauto.
        eapply PCUICConversion.cumul_Prod_inv in c0 as [].
        econstructor. eassumption. eauto. eapply conv_sym in c0; eauto.
        now eapply conv_cumul. auto. auto. }
      assert (eqs := type_closed_subst b extr_env_wf'  X0).
      inv Hvf'.
      * assert (Σ;;; [] |- PCUICLiftSubst.subst1 a' 0 b ⇝ℇ subst1 vu' 0 t').
        eapply (erases_subst Σ [] [PCUICAst.vass na t] [] b [a'] t'); eauto.
        econstructor. econstructor. rewrite parsubst_empty. eassumption.
        rewrite eqs in H2.
        eapply IHeval3 in H2 as (v' & Hv' & He_v').
        -- exists v'. split; eauto.
           econstructor; eauto.
           rewrite ECSubst.closed_subst; auto.
           eapply erases_closed in Hvu'; auto.
           now eapply PCUICClosed.subject_closed in X0.
        -- rewrite <-eqs. eapply substitution0; eauto.
        -- eapply erases_deps_subst1; eauto.
           eapply erases_deps_eval in He_vf'; eauto.
           depelim He_vf'.
           eauto.
      * exists EAst.tBox. split.
        eapply Is_type_lambda in X1; eauto. destruct X1. econstructor.
        eapply (is_type_subst Σ [] [PCUICAst.vass na _] [] _ [a']) in X1 ; auto.
        cbn in X1.
        eapply Is_type_eval.
        eauto. eapply H1. rewrite <-eqs. eassumption.
        all: eauto. econstructor. econstructor. rewrite parsubst_empty.
        eauto. econstructor. eauto. eauto.
    + exists EAst.tBox. split. 2:econstructor; eauto.
      econstructor.
      eapply Is_type_eval; eauto.
  - assert (Hty' := Hty).
    assert (Σ |-p tLetIn na b0 t b1 ▷ res) by eauto.
    eapply inversion_LetIn in Hty' as (? & ? & ? & ? & ? & ?); auto.
    inv He.
    + depelim Heg.
      eapply IHeval1 in H6 as (vt1' & Hvt2' & He_vt1'); eauto.
      assert (Hc : PCUICContextConversion.conv_context Σ ([],, vdef na b0 t) [vdef na b0' t]). {
        econstructor. econstructor. econstructor.
        eapply PCUICCumulativity.red_conv.
        eapply wcbeval_red; eauto. now eapply PCUICClosed.subject_closed in t1. reflexivity.
      }
      assert (Σ;;; [vdef na b0' t] |- b1 : x0). {
        cbn in *. eapply PCUICContextConversion.context_conversion. 3:eauto. all:cbn; eauto.
        econstructor. all: cbn; eauto. eapply subject_reduction_eval; auto. eauto. eauto.
      }
      assert (Σ;;; [] |- PCUICLiftSubst.subst1 b0' 0 b1 ⇝ℇ subst1 vt1' 0 t2'). {
        eapply (erases_subst Σ [] [PCUICAst.vdef na b0' t] [] b1 [b0'] t2'); eauto.
        enough (subslet Σ [] [PCUICLiftSubst.subst [] 0 b0'] [vdef na b0' t]).
        now rewrite parsubst_empty in X1.
        econstructor. econstructor.
        rewrite !parsubst_empty.
        eapply subject_reduction_eval; eauto.
        eapply erases_context_conversion. 3:eassumption.
        all: cbn; eauto.
        econstructor. all: cbn; eauto.
        eapply subject_reduction_eval; eauto.
      }
      unshelve epose proof (subject_reduction_eval _ _ _ _ _ t1 H); eauto.
      assert (eqs := type_closed_subst b1 extr_env_wf' X1).
      rewrite eqs in H1.
      eapply IHeval2 in H1 as (vres & Hvres & Hty_vres); eauto.
      2:{ rewrite <-eqs. eapply substitution_let; eauto. }
      exists vres. split. eauto. econstructor; eauto.
      enough (ECSubst.csubst vt1' 0 t2'  = t2' {0 := vt1'}) as ->; auto.
      eapply ECSubst.closed_subst. eapply erases_closed in Hvt2'; auto.
      eapply eval_closed. eauto. 2:eauto. now eapply PCUICClosed.subject_closed in t1.
    + exists EAst.tBox. split. 2:econstructor; eauto.
      econstructor. eapply Is_type_eval; eauto.

  - destruct Σ as (Σ, univs).
    assert (Σ |-p tConst c u ▷ res) by eauto.
    eapply inversion_Const in Hty as (? & ? & ? & ? & ?); [|easy].
    inv He.
    + depelim Heg.
      assert (isdecl' := isdecl).
      eapply declared_constant_inj in H0; eauto; subst.
      unfold erases_constant_body in *. rewrite e in *.
      destruct ?; try tauto. cbn in *.
      eapply declared_constant_inj in d; eauto; subst.
      edestruct IHeval.
      * cbn in *. pose proof (wf_ext_wf _ extr_env_wf'). cbn in X0.
        assert (isdecl'' := isdecl').
        eapply PCUICWeakeningEnv.declared_constant_inv in isdecl'; eauto.
        2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. red in isdecl'.
        unfold declared_constant in isdecl''.
        eapply typing_subst_instance_decl with (Σ0 := (Σ, univs)) (Γ := []); eauto.
      * pose proof (wf_ext_wf _ extr_env_wf'). cbn in X0.
        assert (isdecl'' := isdecl').
        eapply PCUICWeakeningEnv.declared_constant_inv in isdecl'; eauto.
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. cbn in *.
        2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
        eapply erases_subst_instance_decl with (Σ := (Σ, univs)) (Γ := []); eauto.
      * apply H3; eauto.
      * destruct H0. exists x0. split; eauto. econstructor; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. econstructor. eauto.

  - destruct Σ as (Σ, univs).
    cbn in *.
    eapply extr_env_axiom_free' in isdecl. congruence.

  - assert (Hty' := Hty).
    assert (Σ |-p tCase (ind, pars) p discr brs ▷ res) by eauto.
    eapply inversion_Case in Hty' as [u' [args' [mdecl [idecl [ps [pty [btys
                                    [? [? [? [? [? [_ [? [ht0 [? ?]]]]]]]]]]]]]]]]; auto.
    assert (Σ ;;; [] |- mkApps (tConstruct ind c u) args :  mkApps (tInd ind u') args').
    eapply subject_reduction_eval; eauto.
    eapply PCUICValidity.inversion_mkApps in X0 as (? & ? & ?); eauto.
    eapply inversion_Construct in t1 as (mdecl' & idecl' & cdecl & ? & ? & ? & ?); auto.
    assert (d1 := d0).
    destruct d0.
    edestruct (declared_inductive_inj H1 d). subst.
    pose proof (@length_of_btys ind mdecl' idecl' (firstn pars args') u' p).
    pose proof (length_map_option_out _ _ ht0) as lenbtys. simpl in lenbtys.
    rewrite H3 in lenbtys.

    inv He.
    + depelim Heg.
      eapply IHeval1 in H11 as (v' & Hv' & He_v'); eauto.
      eapply erases_mkApps_inv in Hv' as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
      3: eapply subject_reduction_eval; eauto.
      * subst.

        eapply Is_type_app in X1; auto. destruct X1.
        2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X1.

        eapply tConstruct_no_Type in X1; auto.
        eapply H10 in X1 as []; eauto. 2: exists []; now destruct Σ.

        destruct (ind_ctors idecl'). cbn in *. destruct c; inv H3.
        destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in *; inv H3.

        destruct btys as [ | ? []]; cbn in *; try lia. clear H4 lenbtys H5.
        destruct H8.
        (* eapply H7 in d1. *) inv a. inv X0.
        inv X3. inv X4. destruct H8. destruct x3, y; cbn in *; subst.
        destruct X2. destruct p1; subst; cbn in *.
        destruct p0 as [narg bty]; simpl in *.

        edestruct (IHeval2) as (? & ? & ?).
        eapply subject_reduction. eauto. exact Hty.
        etransitivity.
        eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
        now eapply PCUICClosed.subject_closed in t0.
        eauto.
        econstructor. econstructor. econstructor.

        all:unfold iota_red in *. all:cbn in *.
        eapply erases_mkApps. eauto.
        instantiate (1 := repeat EAst.tBox _).
        eapply All2_Forall2.
        eapply All2_impl.
        eapply All2_All_mix_left. eassumption.
        2:{ intros. destruct X0. assert (y = EAst.tBox). exact y0. subst. econstructor.
            now eapply isErasable_Proof. }

        eapply All2_right_triv. 2: now rewrite repeat_length.
        now eapply All_repeat.

        depelim H1.
        eapply erases_deps_mkApps; [now eauto|].
        apply Forall_repeat.
        now constructor.


        (* destruct x4; cbn in e2; subst. destruct X2. destruct p0; cbn in e2; subst. cbn in *.  destruct y.  *)
        exists x3. split; eauto. eapply eval_iota_sing.  2:eauto.
        pose proof (Ee.eval_to_value _ _ _ He_v').
        eapply value_app_inv in H5. subst. eassumption.

        eapply wf_ext_wf in extr_env_wf'.
        eapply tCase_length_branch_inv in extr_env_wf'.
        2:{ eapply subject_reduction. eauto.
            exact Hty.
            eapply PCUICReduction.red_case_c. eapply wcbeval_red; eauto.
            now eapply PCUICClosed.subject_closed in t0. }
        2: reflexivity.

        enough (#|skipn (ind_npars mdecl') (x0 ++ x1)| = narg) as <- by eauto.
        rewrite skipn_length. rewrite extr_env_wf'. lia.
        rewrite extr_env_wf'. lia.
      * subst. unfold iota_red in *.
        destruct (nth_error brs c) eqn:Hnth.
        2:{ eapply nth_error_None in Hnth. erewrite All2_length in Hnth. 2:exact a.
            eapply nth_error_Some_length in H3. cbn in H3. lia. }
        rewrite <- nth_default_eq in *. unfold nth_default in *.
        rewrite Hnth in *.

        destruct (All2_nth_error_Some _ _ X0 Hnth) as (? & ? & ? & ?).
        destruct (All2_nth_error_Some _ _ a Hnth) as (? & ? & ? & ?).
         destruct p0, x3. cbn in *. subst.
        edestruct IHeval2 as (? & ? & ?).
        eapply subject_reduction. eauto. exact Hty.
        etransitivity.
        eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
        now eapply PCUICClosed.subject_closed in t0. eauto.

        etransitivity. eapply trans_red. econstructor.
        econstructor. unfold iota_red. rewrite <- nth_default_eq. unfold nth_default.
        rewrite Hnth. econstructor.

        eapply erases_mkApps. eauto.
        eapply Forall2_skipn. eauto.

        eapply nth_error_forall in H1; [|now eauto].
        eapply erases_deps_mkApps; [now eauto|].
        eapply erases_deps_eval in He_v'; [|now eauto].
        eapply erases_deps_mkApps_inv in He_v' as (? & ?).
        apply Forall_skipn.
        now eauto.

        inv H6.
        -- exists x3. split; eauto.
           econstructor. eauto. unfold ETyping.iota_red.
           rewrite <- nth_default_eq. unfold nth_default. rewrite e1. cbn. eauto.
        -- eapply Is_type_app in X1 as []; auto.
           2:{ eapply subject_reduction_eval. 3:eassumption. all: eauto. }

           eapply tConstruct_no_Type in X1; auto.
           eapply H10 in X1 as []; eauto. 2: exists []; now destruct Σ.

           destruct (ind_ctors idecl'). cbn in *. destruct c; inv H3.
           destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in *; inv H3.

           destruct btys as [ | ? []]; cbn in *; try discriminate.
           clear H6. destruct H9.
            inv a. inv X2. inv X3. inv X0. destruct H11. destruct x0, y; cbn in *; subst.
           inv X2. destruct p1. subst. destruct p0; cbn in *.
           destruct X4; subst n1. inv e1. simpl in *. inv Hnth. inv e4. cbn in *.

           edestruct (IHeval2) as (? & ? & ?).
           eapply subject_reduction. eauto. exact Hty.
           etransitivity.
           eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
           now eapply PCUICClosed.subject_closed in t0; eauto. eauto.
           econstructor. econstructor.
           econstructor.

           eapply erases_mkApps. eauto.
           instantiate (1 := repeat EAst.tBox _).
           eapply All2_Forall2.
           eapply All2_impl.
           eapply All2_All_mix_left. eassumption.
           2:{ intros. destruct X0. assert (y = EAst.tBox). exact y0. subst. econstructor.
               now eapply isErasable_Proof. }

           eapply All2_right_triv. 2:now rewrite repeat_length.
           now eapply All_repeat.

           depelim H1.
           eapply erases_deps_mkApps; [now eauto|].
           eapply Forall_repeat.
           now constructor.

           exists x0. split; eauto.
           eapply eval_iota_sing.
           pose proof (Ee.eval_to_value _ _ _ He_v').
           2:eauto. auto.
           apply value_app_inv in H9; subst x1.
           apply He_v'.
           enough (#|skipn (ind_npars mdecl') args| = n) as <- by eauto.

           eapply wf_ext_wf in extr_env_wf'.
           eapply tCase_length_branch_inv in extr_env_wf'.
           2:{ eapply subject_reduction. eauto.
               exact Hty.
               eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
               now eapply PCUICClosed.subject_closed in t0. eauto. }
           2: reflexivity.

           enough (#|skipn (ind_npars mdecl') args| = n) as <- by eauto.
           rewrite skipn_length. rewrite extr_env_wf'. lia.
           rewrite extr_env_wf'. lia.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval; eauto. econstructor; eauto.

  - pose (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?); [|easy].
    inv He.

    + depelim Heg.
      eapply IHeval1 in H5 as (vc' & Hvc' & Hty_vc'); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      2: eapply subject_reduction_eval; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists EAst.tBox. split.

        eapply Is_type_app in X as []; eauto. 2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X.

        eapply tConstruct_no_Type in X; eauto. eapply H3 in X as [? []]; eauto.
        2: now destruct d. 2: now exists []; destruct Σ.

        econstructor.
        eapply Is_type_eval. eauto. eauto.
        eapply nth_error_all.
        erewrite nth_error_skipn. reflexivity. eassumption.
        eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H7. subst.
        eassumption.
        eapply isErasable_Proof. eauto.

        eapply eval_proj_box.
        pose proof (Ee.eval_to_value _ _ _ Hty_vc').
        eapply value_app_inv in H1. subst. eassumption.
      * rename H3 into Hinf.
        eapply Forall2_nth_error_Some in H4 as (? & ? & ?); eauto.
        assert (Σ ;;; [] |- mkApps (tConstruct i 0 u) args : mkApps (tInd i x) x2).
        eapply subject_reduction_eval; eauto.
        eapply PCUICValidity.inversion_mkApps in X as (? & ? & ?); eauto.
        eapply typing_spine_inv in t2 as []; eauto.
        eapply IHeval2 in H3 as (? & ? & ?); eauto.
        inv H2.
        -- exists x8. split; eauto. econstructor. eauto.
           rewrite <- nth_default_eq. unfold nth_default. now rewrite H1.
        -- exists EAst.tBox. split.


           eapply Is_type_app in X as []; eauto. 2:{ eapply subject_reduction_eval. 3: eauto. eauto. eauto. }

           eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
           2: now destruct d. 2: now exists []; destruct Σ.

           econstructor.
           eapply Is_type_eval. eauto. eauto.
           eapply nth_error_all.
           erewrite nth_error_skipn. reflexivity. eassumption.
           eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H7. subst.
           eassumption.
           eapply isErasable_Proof. eauto.

           eapply eval_proj_box.
           pose proof (Ee.eval_to_value _ _ _ Hty_vc').
           eapply value_app_inv in H2. subst. eassumption.
        -- eapply erases_deps_eval in Hty_vc'; [|now eauto].
           eapply erases_deps_mkApps_inv in Hty_vc' as (? & ?).
           now eapply nth_error_forall in H1; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. econstructor. eauto.

  - assert (Hty' := Hty).
    assert (Hunf := H).
    assert (Hcon := H1).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    assert (Ht := t).
    eapply subject_reduction in t. 2:eauto. 2:eapply wcbeval_red; eauto.
    2:now eapply PCUICClosed.subject_closed in Ht.
    assert (HT := t).
    apply PCUICValidity.inversion_mkApps in HT as (? & ? & ?); auto.
    assert (Ht1 := t1).
    apply inversion_Fix in t1 as Hfix; auto.
    destruct Hfix as (? & ? & ? & ? & ? & ? & ?).
    rewrite <- closed_unfold_fix_cunfold_eq in e; first last.
    eapply (PCUICClosed.subject_closed (Γ := [])); eauto.
    assert (uf := e).
    unfold unfold_fix in e. rewrite e0 in e. inv e.
    depelim He; first last.

    + exists EAst.tBox. split; [|now constructor].
      econstructor.
      eapply Is_type_eval. eauto. eassumption.
      eapply Is_type_red. eauto. 2: exact X.
      cbn.
      etransitivity.
      eapply PCUICReduction.red_app.
      eapply wcbeval_red. eauto. now eapply PCUICClosed.subject_closed in Ht.
      eauto. eapply wcbeval_red. eauto. now eapply PCUICClosed.subject_closed in t0.
      eauto.
      rewrite <- !mkApps_snoc.
      eapply PCUICReduction.red1_red.
      eapply red_fix.
      eauto.
      unfold is_constructor.
      rewrite nth_error_snoc; eauto.
    + depelim Heg.
      eapply IHeval1 in He1 as IH1; eauto.
      destruct IH1 as (er_stuck_v & er_stuck & ev_stuck).
      eapply IHeval2 in He2 as IH2; eauto.
      destruct IH2 as (er_argv & er_arg & ev_arg).
      eapply erases_mkApps_inv in er_stuck; eauto.
      destruct er_stuck as [(? & ? & ? & -> & ? & ? & ? & ->)|
                            (? & ? & -> & ? & ?)].
      { exists E.tBox.
        eapply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
        cbn in *.
        split; [|eauto using Ee.eval].
        destruct H2.
        eapply (Is_type_app _ _ _ (x5 ++ [av])) in X as []; eauto; first last.
        - rewrite mkApps_nested, app_assoc, mkApps_snoc.
          eapply type_App; eauto.
          eapply subject_reduction; eauto.
          eapply wcbeval_red; eauto.
          eapply PCUICClosed.subject_closed in t0; eauto.
        - eapply erases_box.
          eapply Is_type_eval; eauto.
          eapply Is_type_red; [eauto| |].
          + rewrite <- mkApps_snoc.
            eapply PCUICReduction.red1_red.
            eapply red_fix; [eauto|].
            unfold is_constructor.
            now rewrite nth_error_snoc.
          + rewrite <- app_assoc.
            now rewrite <- mkApps_nested. }

      inv H2.
      * assert (Hmfix' := X).
        eapply All2_nth_error_Some in X as (? & ? & ?); eauto.
        destruct x3. cbn in *. subst.

        enough (Σ;;; [] ,,, PCUICLiftSubst.subst_context (fix_subst mfix) 0 []
                |- PCUICLiftSubst.subst (fix_subst mfix) 0 dbody
                ⇝ℇ subst (ETyping.fix_subst mfix') 0 (Extract.E.dbody x4)).
        destruct p. destruct p.

        clear e3. rename H into e3.
        -- cbn in e3. rename x5 into L.
           eapply (erases_mkApps _ _ _ _ (argsv ++ [av])) in H2; first last.
           { eapply Forall2_app.
             - exact H4.
             - eauto. }
           rewrite <- mkApps_nested in H2.
           rewrite EAstUtils.mkApps_app in H2.
           cbn in *.
           eapply IHeval3 in H2 as (? & ? & ?); cbn; eauto; cycle 1.
           { eapply subject_reduction. eauto. exact Hty.
             etransitivity.
             eapply PCUICReduction.red_app. eapply wcbeval_red; eauto.
             now eapply PCUICClosed.subject_closed in Ht.
             eapply wcbeval_red. eauto. now eapply PCUICClosed.subject_closed in t0.
             eauto.
             rewrite <- !mkApps_snoc.
             eapply PCUICReduction.red1_red.
             eapply red_fix.
             eauto.
             unfold is_constructor.
             rewrite nth_error_snoc; eauto. }
           { constructor.
             - eapply erases_deps_eval in ev_stuck; [|now eauto].
               eapply erases_deps_mkApps_inv in ev_stuck as (? & ?).
               apply erases_deps_mkApps; [|now eauto].
               depelim H.
               eapply nth_error_forall in H as H'; eauto.
               apply erases_deps_subst; [|now eauto].
               now apply Forall_All, erases_deps_fix_subst; eauto.
             - now eapply erases_deps_eval in ev_arg; eauto. }

           exists x3. split. eauto.
           eapply Ee.eval_fix.
           ++ eauto.
           ++ eauto.
           ++ rewrite <- Ee.closed_unfold_fix_cunfold_eq.
              { unfold ETyping.unfold_fix. now rewrite e. }
              eapply eval_closed in e3; eauto.
              clear -e3 Hmfix'.
              pose proof (All2_length _ _ Hmfix').
              eapply PCUICClosed.closedn_mkApps_inv in e3.
              apply andb_true_iff in e3 as (e3 & _).
              change (?a = true) with (is_true a) in e3.
              simpl in e3 |- *. solve_all.
              rewrite app_context_nil_l in b.
              eapply erases_closed in b. simpl in b.
              rewrite <- H.
              unfold EAst.test_def.
              simpl in b.
              rewrite fix_context_length in b.
              now rewrite Nat.add_0_r.
              unfold test_def in a. apply andP in a as [_ Hbod].
              rewrite fix_context_length.
              now rewrite Nat.add_0_r in Hbod.
              eauto with pcuic.
              now eapply PCUICClosed.subject_closed in Ht.
           ++ apply Forall2_length in H4.
              congruence.
           ++ unfold isConstruct_app in *.
              destruct (decompose_app av) eqn:EE.
              assert (E2 : fst (decompose_app av) = t3) by now rewrite EE.
              destruct t3.
              all:inv i.

              pose proof (decompose_app_rec_inv EE).
              cbn in H3. subst.

              eapply erases_mkApps_inv in er_arg
                as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?) ].
              ** subst.
                 now apply eval_to_mkApps_tBox_inv in ev_arg as ->.
              ** subst. inv H5.
                 +++ destruct x6 using rev_ind; cbn - [EAstUtils.decompose_app]. reflexivity.
                     unfold is_constructor_app_or_box.
                     rewrite emkApps_snoc at 1.
                     now rewrite EAstUtils.decompose_app_mkApps.
                 +++ now apply eval_to_mkApps_tBox_inv in ev_arg as ->.
              ** eauto.
              ** eapply subject_reduction; last first.
                 eapply wcbeval_red; last first.
                 eauto.
                 now eapply PCUICClosed.subject_closed in t0.
                 eauto.
                 eauto.
                 eauto.
           ++ eauto.
        -- cbn. destruct p. destruct p.
           eapply (erases_subst Σ [] (PCUICLiftSubst.fix_context mfix) [] dbody (fix_subst mfix)) in e3; cbn; eauto.
           ++ eapply subslet_fix_subst. now eapply wf_ext_wf. all: eassumption.
           ++ eapply nth_error_all in a1; eauto. cbn in a1.
              eapply a1.
           ++ eapply All2_from_nth_error.
              erewrite fix_subst_length, ETyping.fix_subst_length, All2_length; eauto.
              intros.
              rewrite fix_subst_nth in H3. 2:{ now rewrite fix_subst_length in H2. }
              rewrite efix_subst_nth in H5. 2:{ rewrite fix_subst_length in H2.
                                                erewrite <- All2_length; eauto. }
              inv H5; inv H3.
              erewrite All2_length; eauto.
      * eapply Is_type_app in X as []; tas.
        -- exists EAst.tBox.
           split.
           ++ econstructor.
              eapply Is_type_eval; eauto.
              eapply Is_type_red; [eauto| |].
              ** eapply PCUICReduction.red1_red.
                 rewrite <- mkApps_snoc.
                 eapply red_fix; [eauto|].
                 unfold is_constructor.
                 now rewrite nth_error_snoc.
              ** eauto.
           ++ eapply Ee.eval_box; [|eauto].
              apply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
              eauto.
        -- eauto.
        -- rewrite mkApps_snoc.
           eapply type_App; eauto.
           eapply subject_reduction; eauto.
           eapply wcbeval_red; eauto.
           eapply PCUICClosed.subject_closed in t0; eauto.

  - apply inversion_App in Hty as Hty'; [|eauto].
    destruct Hty' as (? & ? & ? & ? & ? & ?).

    eapply subject_reduction in t as typ_stuck_fix; [|eauto|]; first last.
    { eapply wcbeval_red; [eauto| |eauto].
      eapply PCUICClosed.subject_closed in t; eauto. }

    eapply erases_App in He as He'; [|eauto].
    destruct He' as [(-> & [])|(? & ? & -> & ? & ?)].
    + exists E.tBox.
      split; [|eauto using Ee.eval].
      constructor.
      eapply Is_type_red.
      * eauto.
      * eapply PCUICReduction.red_app.
        -- eapply wcbeval_red; [eauto| |eauto].
           eapply PCUICClosed.subject_closed in t; eauto.
        -- eapply wcbeval_red; [eauto| |eauto].
           eapply PCUICClosed.subject_closed in t0; eauto.
      * eauto.
    + depelim Heg.
      eapply subject_reduction in t0 as typ_arg; [|eauto|]; first last.
      { eapply wcbeval_red; [eauto| |eauto].
        eapply PCUICClosed.subject_closed in t0; eauto. }

      eapply IHeval1 in H1 as (? & ? & ?); [|now eauto|now eauto].
      eapply IHeval2 in H2 as (? & ? & ?); [|now eauto|now eauto].
      eapply erases_mkApps_inv in H1; [|eauto|eauto].
      destruct H1 as [(? & ? & ? & -> & [] & ? & ? & ->)|(? & ? & -> & ? & ?)].
      * apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
        depelim H5.
        rewrite !app_nil_r in *.
        cbn in *.
        exists E.tBox.
        split; [|eauto using Ee.eval].
        eapply (Is_type_app _ _ _ [av]) in X as [].
        -- constructor.
           apply X.
        -- eauto.
        -- eauto.
        -- cbn.
           eapply type_App; eauto.
      * depelim H1.
        -- exists (E.tApp (E.mkApps (E.tFix mfix' idx) x7) x5).
           split; [eauto using erases_tApp, erases_mkApps|].
           unfold cunfold_fix in *.
           destruct (nth_error _ _) eqn:nth; [|congruence].
           eapply All2_nth_error_Some in X as (? & ? & ? & ? & ?); [|eauto].
           eapply Ee.eval_fix_value.
           ++ eauto.
           ++ eauto.
           ++ unfold Ee.cunfold_fix.
              rewrite e0.
              reflexivity.
           ++ eapply Forall2_length in H5.
              destruct o as [|(<- & ?)]; [left; congruence|right].
              split; [congruence|].
              eapply subject_reduction_eval in t; eauto.
              injection e. intros <- eq.
              assert (Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [a]) : PCUICLiftSubst.subst1 a 0 x1).
              { rewrite <-mkApps_nested; simpl. eapply type_App; eauto. }
              eapply PCUICValidity.inversion_mkApps in X as (fixty & tyfix & sp); auto.
              eapply inversion_Fix in tyfix as (? & ? & ? & ? & ? & ? & ?); auto.
              rewrite e4 in nth. injection nth; intros ->.
              eapply PCUICSpine.typing_spine_strengthen in sp; eauto.
              eapply wf_fixpoint_spine in sp; eauto.
              2:{ eapply nth_error_all in a0; eauto. eapply a0. }
              rewrite eq in sp. rewrite nth_error_app_ge in sp; try lia.
              rewrite Nat.sub_diag in sp. simpl in sp.
              destruct sp as [ind [u [indargs [tya ck]]]].
              eapply wf_ext_wf in extr_env_wf'.
              pose proof (eval_ind_canonical Σ _ _ _ _ extr_env_axiom_free' tya _ H0).
              revert H1 H6.
              unfold negb, isConstruct_app,
              PCUICParallelReductionConfluence.construct_cofix_discr, PCUICInductives.head.
              destruct (decompose_app av) as [hd tl] eqn:da. simpl.
              destruct hd; try congruence. intros _ _.
              eapply subject_reduction_eval in tya; eauto.
              eapply decompose_app_inv in da. subst av.
              eapply typing_cofix_coind in tya; auto.
              pose proof (check_recursivity_kind_inj Σ ck tya).
              now discriminate.

        -- exists E.tBox.
           apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
           split; [|eauto using Ee.eval].
           eapply Is_type_app in X as [].
           ++ constructor.
              rewrite <- mkApps_snoc.
              exact X.
           ++ eauto.
           ++ eauto.
           ++ rewrite mkApps_snoc.
              eapply type_App; eauto.

  - destruct ip.
    assert (Hty' := Hty).
    eapply inversion_Case in Hty' as [u' [args' [mdecl [idecl [ps [pty [btys
                                   [? [? [? [? [? [_ [? [ht0 [? ?]]]]]]]]]]]]]]]];
    eauto.
    eapply PCUICValidity.inversion_mkApps in t0 as (? & ? & ?); eauto.
    eapply inversion_CoFix in t0 as (? & ? & ? &?); eauto.
    todo "erasure cofix"%string.

  - assert (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?).
    eapply PCUICValidity.inversion_mkApps in t0 as (? & ? & ?); eauto.
    eapply inversion_CoFix in t0 as (? & ? & ? &?); eauto.
    todo "erasure cofix". auto.
  - pose (Hty' := Hty).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    inv He.
    + depelim Heg.
      assert (t' := t). eapply IHeval1 in t as (? & ? & ?); eauto.
      eapply IHeval2 in t0 as (? & ? & ?); eauto.
      destruct (EAstUtils.isBox x2) eqn:E.
      * destruct x2; inv E. exists EAst.tBox. split. 2: econstructor; eauto.
        pose proof (Is_type_app Σ [] f'[a']).
        inversion H1.
        edestruct H7; eauto. cbn. eapply subject_reduction. eauto.
        exact Hty. eapply PCUICReduction.red_app.
        eapply PCUICClosed.subject_closed in t'; auto.
        eapply wcbeval_red; eauto.
        eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; auto.
        eapply PCUICClosed.subject_closed in Ha; auto.
        eapply wcbeval_red; eauto.
      * exists (E.tApp x2 x3).
        split. 2:{ eapply Ee.eval_app_cong; eauto.
                   eapply ssrbool.negbT.
                   repeat eapply orb_false_intro.
                   - destruct x2; try reflexivity.
                     inv H1. inv i.
                   - destruct x2 eqn:Ex; try reflexivity.
                     + cbn. inv H1. cbn in *.
                       eapply ssrbool.negbTE, is_FixApp_erases.
                       econstructor; eauto.
                       now rewrite orb_false_r in i.
                     + cbn in *.
                       inv H1. inv i.
                   - eauto. }
        econstructor; eauto.
    + exists EAst.tBox. split. 2: now econstructor.
      econstructor.
      eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; auto.
      eapply Is_type_red. 3:eauto. eauto.
      eapply PCUICReduction.red_app.
      eapply PCUICClosed.subject_closed in Hf; auto.
      eapply wcbeval_red; eauto.
      eapply PCUICClosed.subject_closed in Ha; auto.
      eapply wcbeval_red; eauto.

  - destruct t; try easy.
    + inv He. eexists. split; eauto. now econstructor.
    + inv He. eexists. split; eauto. now econstructor.
    + inv He.
      * eexists. split; eauto. now econstructor.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
    + inv He.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
    + inv He.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
      * eexists. split. 2: now econstructor.
        eauto.
    + inv He.
      * eexists. split; eauto. now econstructor.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
    + inv He.
      * eexists. split; eauto. now econstructor.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
Qed.
