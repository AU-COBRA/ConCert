From ConCert.Extraction Require Import Aux.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Psatz.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.
Set Equations Transparent.

Lemma closed_mkApps hd args :
  closed hd ->
  Forall (closedn 0) args ->
  closed (mkApps hd args).
Proof.
  revert hd.
  induction args using List.rev_ind; [easy|].
  intros hd closed_hd closed_args.
  rewrite mkApps_app.
  cbn.
  propify.
  apply Forall_app in closed_args.
  destruct closed_args as (? & closed_x).
  split; [|now inversion closed_x].
  easy.
Qed.

Lemma closed_mkApps_inv hd args :
  closed (mkApps hd args) ->
  closed hd /\
  Forall (closedn 0) args.
Proof.
  revert hd.
  induction args using List.rev_ind; [easy|]; intros hd clos.
  rewrite mkApps_app in clos.
  cbn in clos.
  propify.
  specialize (IHargs hd ltac:(easy)).
  split; [easy|].
  apply app_Forall; [easy|].
  constructor; easy.
Qed.

Lemma closed_mkApps_head hd args :
  closed (mkApps hd args) ->
  closed hd.
Proof.
  intros clos.
  now pose proof (closed_mkApps_inv _ _ clos).
Qed.

Lemma closed_mkApps_args hd args :
  closed (mkApps hd args) ->
  Forall (closedn 0) args.
Proof.
  intros clos.
  now pose proof (closed_mkApps_inv _ _ clos).
Qed.

Definition decl_closed (decl : EAst.global_decl) : Prop :=
  match decl with
  | EAst.ConstantDecl cst =>
    match EAst.cst_body cst with
    | Some body => closed body
    | _ => True
    end
  | _ => True
  end.

Arguments Nat.ltb : simpl nomatch.

Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert n k k'.
  induction t using term_forall_list_ind; intros n' k k' clos;
    cbn in *; auto; propify.
  - destruct (Nat.leb_spec k' n);
      cbn; propify; lia.
  - induction H; cbn in *; propify; easy.
  - erewrite <- IHt by eassumption.
    easy.
  - erewrite <- IHt1 at 1 by easy.
    erewrite <- IHt2 by easy.
    easy.
  - easy.
  - split; [easy|].
    destruct clos as (_ & clos).
    induction X; cbn in *; propify; easy.
  - rewrite map_length.
    revert n' k k' clos.
    induction H; intros n' k k' clos; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (H _ (S (#|l| + k)) _) by easy.
      f_equal.
      lia.
    + erewrite <- (IHForall n' (S k) (S k'));
        repeat (f_equal; try lia).
      rewrite <- (proj2 clos);
        repeat (f_equal; try lia).
  - rewrite map_length.
    revert n' k k' clos.
    induction H; intros n' k k' clos; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (H _ (S (#|l| + k)) _) by easy.
      f_equal.
      lia.
    + erewrite <- (IHForall n' (S k) (S k'));
        repeat (f_equal; try lia).
      rewrite <- (proj2 clos);
        repeat (f_equal; try lia).
Qed.

Lemma closedn_subst s k k' t :
  Forall (closedn k) s -> closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  revert k k'.
  induction t using term_forall_list_ind; intros k k' all clos;
    cbn in *; auto; propify.
  - destruct (Nat.leb_spec k' n); cbn in *; propify.
    + destruct nth_error eqn:eq;
        cbn in *.
      * apply closedn_lift.
        rewrite Forall_forall in all.
        apply nth_error_In in eq.
        easy.
      * propify.
        apply nth_error_None in eq.
        lia.
    + lia.
  - induction H; cbn in *; propify; easy.
  - erewrite <- (IHt _ (S k')); [|easy|rewrite <- clos; f_equal; lia].
    f_equal; lia.
  - split; [easy|].
    erewrite <- (IHt2 _ (S k')); [|easy|].
    + f_equal; lia.
    + rewrite <- (proj2 clos); f_equal; lia.
  - easy.
  - split; [easy|].
    induction X; cbn in *; propify; easy.
  - rewrite map_length.
    revert k k' all clos.
    induction H; intros k k' all all'; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (H _ (S (#|l| + k'))); [|easy|].
      * f_equal; lia.
      * rewrite <- (proj1 all').
        f_equal; lia.
    + erewrite <- (IHForall _ (S k')); [|easy|].
      * repeat (f_equal; try lia).
      * rewrite <- (proj2 all').
        repeat (f_equal; try lia).
  - rewrite map_length.
    revert k k' all clos.
    induction H; intros k k' all all'; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (H _ (S (#|l| + k'))); [|easy|].
      * f_equal; lia.
      * rewrite <- (proj1 all').
        f_equal; lia.
    + erewrite <- (IHForall _ (S k')); [|easy|].
      * repeat (f_equal; try lia).
      * rewrite <- (proj2 all').
        repeat (f_equal; try lia).
Qed.

Lemma lookup_env_find Σ kn :
  ETyping.lookup_env Σ kn =
  option_map snd (find (fun '(kn', _) => if kername_eq_dec kn kn' then true else false) Σ).
Proof.
  induction Σ as [|(kn' & decl) Σ IH]; [easy|].
  cbn.
  now destruct (kername_eq_dec kn kn').
Qed.

Lemma closedn_subst0 s k t :
  Forall (closedn k) s ->
  closedn (k + #|s|) t ->
  closedn k (subst0 s t).
Proof.
  intros all clos.
  rewrite <- (Nat.add_0_r k).
  apply closedn_subst; [easy|].
  now rewrite Nat.add_0_r.
Qed.

Lemma closed_csubst t k u : closed t -> closedn (S k) u -> closedn k (csubst t 0 u).
Proof.
  intros clost closu.
  rewrite closed_subst by easy.
  apply closedn_subst0.
  - constructor; [|easy].
    now eapply closed_upwards.
  - cbn.
    now rewrite Nat.add_1_r.
Qed.