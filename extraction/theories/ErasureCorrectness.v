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
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICInduction.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICWcbvEval.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import utils.

Open Scope string.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.
Notation "Σ 'e⊢' s ▷ t" := (EWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

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
  induction Σ as [|(kn, decl) Σ IH] in wfΣ, include, Σex, er |- *; intros k isin;
    [easy|].
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
