From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import MetaCoqErasureCorrectnessStrong.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import WcbvEvalType.
From Coq Require Import List.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import ErasureCorrectness.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.Erasure Require Import ESubstitution.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICInduction.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
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
Notation "Σ 'e⊢' s ▷ t" := (EWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

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

Lemma erases_deps_forall_ind Σ Σ'
  (P : Extract.E.term -> Prop)
  (Hbox : P Extract.E.tBox)
  (Hrel : forall i : nat, P (Extract.E.tRel i))
  (Hvar : forall n : ident, P (Extract.E.tVar n))
  (Hevar :
     forall (m : nat) (l : list Extract.E.term),
       Forall P l ->
       Forall (erases_deps Σ Σ') l -> P (Extract.E.tEvar m l))
  (Hlam : forall (na : name) (body : Extract.E.term),
        erases_deps Σ Σ' body -> P body -> P (Extract.E.tLambda na body))
  (Hletin : forall (na : name) (val body : Extract.E.term),
        erases_deps Σ Σ' val ->
        P val -> erases_deps Σ Σ' body -> P body -> P (Extract.E.tLetIn na val body))
  (Happ : forall hd arg : Extract.E.term,
        erases_deps Σ Σ' hd -> P hd -> erases_deps Σ Σ' arg -> P arg -> P (Extract.E.tApp hd arg))
  (Hconst : forall (kn : kername) (cb : PCUICAst.PCUICEnvironment.constant_body) (cb' : EAst.constant_body),
      declared_constant Σ kn cb ->
      ETyping.declared_constant Σ' kn cb' ->
      erases_constant_body (Σ, PCUICAst.cst_universes cb) cb cb' ->
      (forall body : Extract.E.term, Extract.E.cst_body cb' = Some body -> erases_deps Σ Σ' body) ->
      (forall body : Extract.E.term, Extract.E.cst_body cb' = Some body -> P body) ->
        P (Extract.E.tConst kn))
  (Hconstruct : forall (ind : inductive) (c : nat), P (Extract.E.tConstruct ind c))
  (Hcase : forall (p : inductive × nat) (discr : Extract.E.term) (brs : list (nat × Extract.E.term)),
        erases_deps Σ Σ' discr ->
        P discr ->
        Forall (fun br : nat × Extract.E.term => erases_deps Σ Σ' br.2) brs ->
        Forall (fun br => P br.2) brs ->
        P (Extract.E.tCase p discr brs))
  (Hproj : forall (p : projection) (t : Extract.E.term),
        erases_deps Σ Σ' t -> P t -> P (Extract.E.tProj p t))
  (Hfix : forall (defs : list (Extract.E.def Extract.E.term)) (i : nat),
         Forall (fun d : Extract.E.def Extract.E.term => erases_deps Σ Σ' (Extract.E.dbody d)) defs ->
         Forall (fun d => P (E.dbody d)) defs ->
         P (Extract.E.tFix defs i))
  (Hcofix : forall (defs : list (Extract.E.def Extract.E.term)) (i : nat),
         Forall (fun d : Extract.E.def Extract.E.term => erases_deps Σ Σ' (Extract.E.dbody d)) defs ->
         Forall (fun d => P (E.dbody d)) defs ->
         P (Extract.E.tCoFix defs i)) :
  forall t, erases_deps Σ Σ' t -> P t.
Proof.
  fix f 2.
  intros t ed.
  move f at top.
  destruct ed;
    try solve [match goal with
    | [H: _ |- _] => apply H
    end; auto].
  - apply Hevar; [|assumption].
    revert l H.
    fix f' 2.
    intros l [].
    + now constructor.
    + constructor; [now apply f|now apply f'].
  - eapply Hconst; try eassumption.
    intros.
    apply f.
    now apply H2.
  - apply Hcase; try assumption.
    + now apply f.
    + revert brs H.
      fix f' 2.
      intros brs []; [now constructor|].
      constructor; [now apply f|now apply f'].
  - apply Hfix; try assumption.
    revert defs H.
    fix f' 2.
    intros defs []; [now constructor|].
    constructor; [now apply f|now apply f'].
  - apply Hcofix; try assumption.
    revert defs H.
    fix f' 2.
    intros defs []; [now constructor|].
    constructor; [now apply f|now apply f'].
Defined.

Lemma erases_deps_cons Σ Σ' kn decl t :
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

Lemma erase_global_decls_deps_recursive_correct Σ wfΣ include ignore erase_func Σex :
  (forall k, ignore k = false) ->
  erase_global_decls_deps_recursive erase_func Σ wfΣ include ignore = Ok Σex ->
  (forall k,
      In k include ->
      match P.lookup_env Σ k with
      | Some (P.ConstantDecl cst) =>
        erases_deps Σ (trans_env Σex) (E.tConst k)
      | _ => True
      end).
Proof.
Ltac unproof :=
  repeat
    multimatch goal with
    | [H: context[erase_global_decl _ _ ?wfΣ _ _ _ ?wfdecl] |- _] =>
      first
        [is_var wfΣ|
         (let wfΣid := fresh "wfΣ" in set (wfΣid := wfΣ) in *; clearbody wfΣid)];
      first
        [is_var wfdecl|
         (let wfdeclid := fresh "wfdecl" in set (wfdeclid := wfdecl) in *; clearbody wfdeclid)]
    | [H: context[erase_global_decls_deps_recursive _ _ ?wfΣ] |- _] =>
      first
        [is_var wfΣ|
         (let wfΣid := fresh "wfΣ" in set (wfΣid := wfΣ) in *; clearbody wfΣid)]
    end.

  intros no_ignores er.
  induction Σ as [|(kn, decl) Σ IH] in wfΣ, include, Σex, er |- *; [easy|].
  cbn in *; unproof.
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
      now apply erases_deps_cons.
  - cbn in *.
    destruct erase_global_decl eqn:erdecl; cbn in *; [|congruence].
    destruct erase_global_decls_deps_recursive eqn:errec; [|congruence].
    inversion er; subst; clear er.
    intros k isin.
    unfold eq_kername.
    destruct kername_eq_dec as [->|].
    + destruct decl; [|easy].
      econstructor.
      * unfold declared_constant; cbn.
        rewrite eq_kername_refl.
        reflexivity.
      * simpl in erdecl.

    eapply IH in errec.
  - cbn in *.
    destruct erase_global_decl eqn:erdecl; [|congruence].
    inversion er; subst; clear er.
    cbn in *.
    destruct decl; cycle 1.
    * simpl in erdecl.
  rew
  destruct P.lookup_env eqn:lookup; [|easy].
  destruct g; [|easy].
  cbn in *; unproof.
  Admitted.
(*  cbn.
  cbn in *; unproof.
  rewrite no_ignores in er.
  destruct (contains kn include) eqn:contains.
  - cbn in *.
    destruct erase_global_decl eqn:erdecl; [|congruence].
    destruct erase_global_decls_deps_recursive eqn:errec; [|congruence].
    inversion er; subst; clear er.
    cbn in *.
    destruct decl; cycle 1.
    * simpl in erdecl.
      destruct erase_ind; simpl in *; [|congruence].
      inversion erdecl; subst; clear erdecl.
      simpl in *.
      eapply IH in errec.
    * cbn.
      constructor.

  econstructor.
  - easy.
  -
  eapply erases_deps_tConst.
  er : erase_global_decls_deps_recursive SafeErasureFunction.erase Σ (wf_ext_wf_squash wfΣ) [kn]
         (fun _ : kername => false) = Ok Σex
*)
