From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EDeps.
From MetaCoq.Erasure Require Import ErasureCorrectness.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.Erasure Require Import ESubstitution.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICInduction.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICSR.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICWcbvEval.
From MetaCoq.PCUIC Require Import PCUICWeakeningEnv.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import utils.

Open Scope string.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma contains_In k ks :
  Erasure.contains k ks <-> In k ks.
Proof.
  split; intros.
  - unfold contains in *.
    apply existsb_exists in H as (? & ? & ?).
    unfold eq_kername in *.
    now destruct kername_eq_dec as [<-|].
  - unfold contains.
    induction ks; cbn in *; [easy|].
    destruct H as [->|].
    + now rewrite eq_kername_refl.
    + rewrite IHks by easy.
      now rewrite Bool.orb_true_r.
Qed.

Lemma contains_In_not k ks :
  Erasure.contains k ks = false <-> ~ In k ks.
Proof.
  split; intros.
  - intros isin.
    now apply contains_In in isin.
  - destruct (contains k ks) eqn:cont; [|easy].
    now apply contains_In in cont.
Qed.

Lemma erases_deps_cons_left Σ Σ' kn decl t :
  wf ((kn, decl) :: Σ) ->
  erases_deps Σ Σ' t ->
  erases_deps ((kn, decl) :: Σ) Σ' t.
Proof.
  intros wfΣ er.
  induction er using erases_deps_forall_ind; try solve [now constructor].
  apply lookup_env_Some_fresh in H as not_fresh.
  econstructor.
  - unfold declared_constant in *.
    cbn.
    unfold eq_kername.
    inversion wfΣ; subst.
    destruct kername_eq_dec as [<-|]; [congruence|].
    eassumption.
  - eassumption.
  - unfold erases_constant_body in *.
    destruct PCUICAst.cst_body eqn:body.
    + destruct E.cst_body eqn:ebody; [|easy].
      assert (declared_constant ((kn, decl) :: Σ) kn0 cb).
      { unfold declared_constant.
        cbn.
        unfold eq_kername.
        inversion wfΣ; subst.
        destruct kername_eq_dec as [<-|]; [congruence|].
        easy. }
      inversion wfΣ; subst.
      eapply PCUICWeakeningEnv.declared_constant_inv in H4; eauto.
      2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
      red in H4.
      rewrite body in *.
      cbn in *.
      eapply (erases_extends (_, P.cst_universes cb)); eauto.
      2: eexists [_]; reflexivity.
      eapply declared_constant_inv in H.
      2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
      2: easy.
      2: easy.
      unfold on_constant_decl in H.
      rewrite body in *.
      apply H.
    + now destruct E.cst_body.
  - easy.
Qed.

Lemma In_add_seen k k' ks :
  (k = k' \/ In k ks) ->
  In k (add_seen k' ks).
Proof.
  intros [->|].
  - unfold add_seen.
    destruct existsb eqn:ex; [|now left].
    apply existsb_exists in ex as (k & ? & ?).
    unfold eq_kername in *.
    now destruct kername_eq_dec as [<-|].
  - unfold add_seen.
    destruct existsb eqn:ex; [easy|].
    now right.
Qed.

Lemma In_box_type_deps k ks t :
  In k ks ->
  In k (box_type_deps ks t).
Proof.
  intros isin.
  induction t in ks, t, isin |- *; cbn in *; auto.
  - now apply In_add_seen.
  - now apply In_add_seen.
Qed.

Lemma In_fold_left {A} k (ks : list kername) f (ts : list A) :
  In k ks ->
  (forall a ks, In a ts -> In k ks -> In k (f ks a)) ->
  In k (fold_left f ts ks).
Proof.
  intros isin allin.
  induction ts in ks, ts, isin, allin |- *; [easy|].
  apply IHts.
  - apply allin; [|easy].
    now left.
  - intros.
    apply allin; [|easy].
    now right.
Qed.

Lemma In_Eterm_deps_already k ks t :
  In k ks ->
  In k (Eterm_deps ks t).
Proof.
  intros isin.
  induction t in ks, t, isin |- * using EInduction.term_forall_list_ind; cbn in *; auto.
  - induction H in ks, isin |- *; [easy|].
    cbn in *.
    now apply IHAll.
  - now apply In_add_seen.
  - now apply In_add_seen.
  - destruct p.
    apply In_fold_left.
    + now apply IHt, In_add_seen.
    + intros.
      destruct a.
      now eapply All_In in H as [H]; [|eassumption].
  - destruct s as ((ind & npars) & arg).
    now apply IHt, In_add_seen.
  - apply In_fold_left; [easy|].
    intros.
    now eapply All_In in H as [H]; [|eassumption].
  - apply In_fold_left; [easy|].
    intros.
    now eapply All_In in H as [H]; [|eassumption].
Qed.

Lemma In_fold_left_new_exists {A} k (ks : list kername) f (ts : list A) :
  In k (fold_left f ts ks) ->
  ~In k ks ->
  exists tspref t' tssuf,
    ts = (tspref ++ [t'] ++ tssuf)%list /\
    ~In k (fold_left f tspref ks) /\
    In k (f (fold_left f tspref ks) t').
Proof.
  intros isin notin.
  induction ts in ks, ts, isin, notin |- *; cbn in *; [congruence|].
  destruct (contains k (f ks a)) eqn:cont.
  - apply contains_In in cont.
    now exists [], a, ts.
  - apply IHts in isin as (pref & t' & suf & -> & ? & ?); cycle 1.
    { intros isin'.
      apply contains_In in isin'.
      congruence. }
    now exists (a :: pref), t', suf.
Qed.

Lemma In_fold_left_new {A} k (ks ks' : list kername) f (ts : list A) :
  In k (fold_left f ts ks) ->
  ~In k ks ->
  (forall a ks, In a ts -> In k ks -> In k (f ks a)) ->
  (forall a ks ks', In a ts -> ~In k ks -> In k (f ks a) -> In k (f ks' a)) ->
  In k (fold_left f ts ks').
Proof.
  intros isin notin allin_already allin_new.
  destruct (In_fold_left_new_exists _ _ _ _ isin) as (tspref & t' & tssuf & -> & ? & ?); [easy|].
  rewrite !fold_left_app in *.
  cbn in *.
  apply In_fold_left.
  - eapply allin_new; [| |exact H0].
    + apply in_or_app.
      now right; left.
    + easy.
  - intros.
    eapply allin_already; [|easy].
    apply in_or_app.
    now right; right.
Qed.

Lemma add_seen_new k ks k' :
  ~In k ks ->
  In k (add_seen k' ks) ->
  k = k'.
Proof.
  intros notin isin.
  unfold add_seen in *.
  destruct existsb eqn:ex; [easy|].
  now destruct isin.
Qed.

Lemma In_Eterm_deps_new k ks ks' t :
  In k (Eterm_deps ks t) ->
  ~In k ks ->
  In k (Eterm_deps ks' t).
Proof.
  intros isin notin.
  induction t in ks, ks', isin, notin |- * using EInduction.term_forall_list_ind; cbn in *; try easy.
  - eapply In_fold_left_new; eauto.
    + intros.
      now apply In_Eterm_deps_already.
    + intros.
      now eapply All_In in H as [H]; [|eassumption].
  - destruct (contains k (Eterm_deps ks t1)) eqn:cont.
    + apply contains_In in cont.
      now apply In_Eterm_deps_already.
    + eapply IHt2; [easy|].
      apply contains_In_not.
      eassumption.
  - destruct (contains k (Eterm_deps ks t1)) eqn:cont.
    + apply contains_In in cont.
      now apply In_Eterm_deps_already.
    + eapply IHt2; [easy|].
      apply contains_In_not.
      eassumption.
  - apply add_seen_new in isin as ->; [|easy].
    now apply In_add_seen.
  - apply add_seen_new in isin as ->; [|easy].
    now apply In_add_seen.
  - destruct p.
    destruct (contains k (Eterm_deps (add_seen (inductive_mind i) ks) t)) eqn:cont.
    + apply contains_In in cont.
      apply In_fold_left.
      * destruct (eq_dec k (inductive_mind i)) as [->|].
        -- now apply In_Eterm_deps_already, In_add_seen.
        -- eapply IHt; [eassumption|].
           intros isin'.
           now apply add_seen_new in isin'; subst.
      * intros; destruct a.
        now apply In_Eterm_deps_already.
    + apply contains_In_not in cont.
      eapply In_fold_left_new; eauto.
      * intros; destruct a.
        now apply In_Eterm_deps_already.
      * intros; destruct a.
        now eapply All_In in X as []; [|eassumption].
  - destruct s as ((? & ?) & ?).
    destruct (eq_dec (inductive_mind i) k) as [<-|].
    + now apply In_Eterm_deps_already, In_add_seen.
    + eapply IHt; [easy|].
      intros isin'.
      now apply add_seen_new in isin'; subst.
  - eapply In_fold_left_new; eauto.
    + intros.
      now apply In_Eterm_deps_already.
    + intros.
      now eapply All_In in H as [H]; [|eassumption].
  - eapply In_fold_left_new; eauto.
    + intros.
      now apply In_Eterm_deps_already.
    + intros.
      now eapply All_In in H as [H]; [|eassumption].
Qed.

Lemma In_fold_box_type_deps k ks ts :
  In k ks ->
  In k (fold_left box_type_deps ts ks).
Proof.
  intros isin.
  induction ts in ks, ts, isin |- *; [easy|].
  now apply IHts, In_box_type_deps.
Qed.

Lemma In_decl_deps k ks decl :
  In k ks ->
  In k (decl_deps ks decl).
Proof.
  intros isin.
  destruct decl; cbn in *.
  - apply In_box_type_deps.
    destruct ExAst.cst_body; [|easy].
    now apply In_Eterm_deps_already.
  - apply In_fold_left; [easy|].
    intros.
    apply In_fold_left.
    + apply In_fold_left; [easy|].
      intros.
      now eapply In_box_type_deps.
    + intros.
      now apply In_box_type_deps.
  - destruct p.
    now apply In_box_type_deps.
Qed.

Lemma erases_deps_recursive Σ Σer t T et :
  wf_ext Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ et ->
  (forall k,
      In k (Eterm_deps [] et) ->
      match P.lookup_env Σ k with
      | Some (P.ConstantDecl _) => erases_deps Σ Σer (E.tConst k)
      | _ => True
      end) ->
  erases_deps Σ Σer et.
Proof.
  intros wf wt er deps_er.
  induction er in t, T, et, wf, wt, er, deps_er |- * using erases_forall_list_ind; cbn in *.
  - now constructor.
  - now constructor.
  - now apply inversion_Evar in wt.
  - constructor.
    apply inversion_Lambda in wt as (? & ? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & ? & ? & ? & ? & ?); eauto.
    constructor.
    + eapply IHer1; eauto.
      intros.
      apply deps_er.
      now apply In_Eterm_deps_already.
    + eapply IHer2; eauto.
      intros.
      apply deps_er.
      now eapply In_Eterm_deps_new.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
    constructor.
    + eapply IHer1; eauto.
      intros.
      apply deps_er.
      now apply In_Eterm_deps_already.
    + eapply IHer2; eauto.
      intros.
      apply deps_er.
      now eapply In_Eterm_deps_new.
  - apply inversion_Const in wt as (? & ? & ? & ? & ?); eauto.
    specialize (deps_er kn (or_introl eq_refl)).
    unfold declared_constant in d.
    unfold PCUICAst.fst_ctx, fst_ctx in *.
    now rewrite d in deps_er.
  - now constructor.
  - apply inversion_Case in wt
      as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
    constructor.
    + eapply IHer; eauto.
      intros.
      eapply deps_er.
      eapply In_fold_left.
      * now eapply In_Eterm_deps_new.
      * intros.
        destruct a0.
        now apply In_Eterm_deps_already.
    + clear -wf a X H0 deps_er.
      revert brs' x5 a X H0 deps_er.
      induction brs; intros brs' x5 brtys typ er deps.
      { now depelim er. }
      depelim brtys.
      depelim typ.
      depelim er.
      destruct p as ((? & ?) & ?).
      destruct p0.
      constructor.
      * eapply H; eauto.
        intros.
        apply deps.
        cbn.
        destruct y0; cbn in *.
        apply In_fold_left.
        -- now eapply In_Eterm_deps_new.
        -- intros; destruct a0.
           now apply In_Eterm_deps_already.
      * eapply IHbrs; eauto.
        intros.
        apply deps.
        cbn.
        destruct y0; cbn in *.
        destruct (contains k (Eterm_deps (Eterm_deps [inductive_mind ind] c') t1)) eqn:cont.
        -- apply contains_In in cont.
           apply In_fold_left; cbn in *; [easy|].
           intros; destruct a0.
           now apply In_Eterm_deps_already.
        -- apply contains_In_not in cont.
           eapply In_fold_left_new; eauto.
           ++ intros isin'.
              contradiction cont.
              now apply In_Eterm_deps_already.
           ++ intros; destruct a0.
              now apply In_Eterm_deps_already.
           ++ intros; destruct a0.
              eapply In_Eterm_deps_new; eauto.

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?); eauto.
    constructor.
    eapply IHer; eauto.
    intros; apply deps_er.
    destruct p as ((? & ?) & ?).
    now eapply In_Eterm_deps_new.
  - constructor.
    apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    clear -wf a0 X H deps_er.
    revert a0 X H deps_er.
    generalize mfix at 1 2 4 6.
    intros mfix_gen.
    revert mfix'.
    induction mfix; cbn in *; intros mfix' typ er all_deps deps.
    { now depelim er. }
    depelim typ.
    depelim er.
    depelim all_deps.
    destruct p.
    destruct p0 as (?&?&?).
    constructor.
    + eapply H; eauto.
      intros.
      apply deps.
      cbn in *.
      apply In_fold_left; [easy|].
      intros.
      now apply In_Eterm_deps_already.
    + apply IHmfix; eauto.
      intros.
      apply deps.
      cbn in *.
      eapply In_fold_left_new; eauto.
      * intros.
        now apply In_Eterm_deps_already.
      * intros.
        now eapply In_Eterm_deps_new.
  - constructor.
    apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    clear -wf a0 X H deps_er.
    revert a0 X H deps_er.
    generalize mfix at 1 2 4 6.
    intros mfix_gen.
    revert mfix'.
    induction mfix; cbn in *; intros mfix' typ er all_deps deps.
    { now depelim er. }
    depelim typ.
    depelim er.
    depelim all_deps.
    destruct p as (?&?&?).
    constructor.
    + eapply H; eauto.
      intros.
      apply deps.
      cbn in *.
      apply In_fold_left; [easy|].
      intros.
      now apply In_Eterm_deps_already.
    + apply IHmfix; eauto.
      intros.
      apply deps.
      cbn in *.
      eapply In_fold_left_new; eauto.
      * intros.
        now apply In_Eterm_deps_already.
      * intros.
        now eapply In_Eterm_deps_new.
  - now constructor.
Qed.

Opaque erase_type SafeErasureFunction.wf_reduction.
Lemma erase_global_decls_deps_recursive_correct Σ wfΣ include ignore Σex :
  (forall k, ignore k = false) ->
  erase_global_decls_deps_recursive Σ wfΣ include ignore = Ok Σex ->
  (forall k,
      In k include ->
      match P.lookup_env Σ k with
      | Some (P.ConstantDecl cst) =>
        erases_deps Σ (trans_env Σex) (E.tConst k)
      | _ => True
      end).
Proof.
  intros no_ignores er.
  induction Σ as [|(kn, decl) Σ IH] in wfΣ, include, Σex, er |- *; [easy|].
  simpl in *.
  match goal with
  | [H: context[erase_global_decl _ ?wfΣarg _ _ ?wfdeclarg] |- _] =>
      set (wfΣext := wfΣarg) in *; clearbody wfΣext;
        set (wfdecl := wfdeclarg) in *; clearbody wfdecl
  end.
  match goal with
  | [H: context[erase_global_decls_deps_recursive _ ?wfΣarg] |- _] =>
    set (wfΣprev := wfΣarg) in *; clearbody wfΣprev
  end.

  rewrite no_ignores in er.
  destruct (contains kn include) eqn:contains; cycle 1.
  - cbn in *.
    intros.
    eapply IH with (k := k) in er; eauto.
    unfold eq_kername.
    destruct kername_eq_dec as [->|].
    + now apply contains_In in H.
    + destruct P.lookup_env; [|easy].
      destruct g; [|easy].
      destruct wfΣ.
      now apply erases_deps_cons_left.
  - cbn in *.
    destruct erase_global_decl eqn:erdecl; cbn in *; [|congruence].
    destruct erase_global_decls_deps_recursive eqn:errec; [|congruence].
    inversion er; subst; clear er.
    intros k isin.
    unfold eq_kername.
    destruct kername_eq_dec as [->|]; cycle 1.
    { cbn in *.
      eapply IH with (k := k) in errec; eauto.
      destruct P.lookup_env; [|easy].
      destruct g; [|easy].
      destruct wfΣ.
      destruct t;
        eauto using erases_deps_cons, erases_deps_cons_left.
      now apply In_decl_deps. }
    destruct decl; [|easy].
    cbn -[erase_constant_decl] in *.
    destruct erase_constant_decl eqn:erconst; cbn -[erase_constant_decl] in *; [|congruence].
    unfold erase_constant_decl in erconst.
    destruct flag_of_type; cbn in *; [|congruence].
    destruct a; cbn in *.
    destruct is_sort.
    + cbn in wfdecl.
      destruct c.
      destruct cst_body; cbn in *; [|congruence].
      destruct erase_type; cbn in *; [|congruence].
      inversion erconst; subst; clear erconst.
      inversion erdecl; subst; clear erdecl.
      cbn in *.
      econstructor.
      * unfold declared_constant; cbn; rewrite eq_kername_refl.
        reflexivity.
      * unfold ETyping.declared_constant; cbn.
        destruct kername_eq_dec; [|congruence].
        reflexivity.
      * cbn.
        destruct wfΣ as [wfΣ].
        destruct wfdecl as [wfdecl].
        destruct i as (u & [redu]).
        eapply type_reduction in wfdecl; eauto.
        2: now inversion wfΣ.
        constructor.
        eapply (Is_type_extends (Σ, _)).
        2: now eauto.
        2: eexists [_]; reflexivity.
        1: now eauto.
        eexists _.
        split; [eassumption|].
        now left.
      * intros.
        cbn in *.
        inversion H; subst; clear H.
        now constructor.
    + destruct erase_type; cbn in *; [|congruence].
      destruct c; cbn in *.
      destruct cst_body; cycle 1.
      { inversion erconst; subst; clear erconst.
        inversion erdecl; subst; clear erdecl.
        cbn in *.
        econstructor.
        - unfold declared_constant; cbn; rewrite eq_kername_refl; reflexivity.
        - unfold ETyping.declared_constant; cbn.
          destruct kername_eq_dec; [|congruence].
          reflexivity.
        - easy.
        - intros.
          cbn in *.
          congruence. }

      match goal with
      | [H: context[SafeErasureFunction.erase _ _ _ _ ?p] |- _] =>
        set (twt := p) in *; clearbody twt
      end.
      inversion erconst; subst; clear erconst.
      inversion erdecl; subst; clear erdecl.
      cbn in *.
      specialize (IH _ _ _ errec).
      destruct wfΣ as [wfΣ].
      destruct wfdecl as [wfdecl].
      econstructor.
      * unfold declared_constant; cbn; rewrite eq_kername_refl; reflexivity.
      * unfold ETyping.declared_constant; cbn.
        destruct kername_eq_dec; [|congruence].
        reflexivity.
      * cbn.
        eapply type_reduction in wfdecl; eauto.
        2: now inversion wfΣ.
        eapply (erases_extends (_, _)).
        2: now eauto.
        1: now inversion wfΣ.
        2: eexists [_]; reflexivity.
        1: now eauto.
        apply SafeErasureFunction.erases_erase.
      * intros.
        cbn in *.
        noconf H.
        destruct wfΣext.
        apply erases_deps_cons; eauto.
        eapply (erases_deps_recursive (Σ, cst_universes)); eauto.
        { apply SafeErasureFunction.erases_erase. }
        intros.
        apply IH.
        apply In_box_type_deps.
        now eapply In_Eterm_deps_new.
Qed.
