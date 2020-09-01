From ConCert.Extraction Require Import AffineLambdaCalculus.
From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import WcbvEvalAux.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import RelationClasses.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import EInversion.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Import EAstUtils.
Import Erasure.
Import ExAst.

(* We have our own environment which is different from MetaCoq's erased environment
   (it includes more information and a different treatment of types).
   To reconcile this, we map our environments to theirs, but the treatment of types
   remains different. However, MetaCoq does not actually use information about types
   for anything during evaluation, so we just filter them out. This is justified
   by the following lemmas. *)
Definition is_constant (decl : EAst.global_decl) : bool :=
  match decl with
  | EAst.ConstantDecl _ => true
  | _ => false
  end.

Definition only_constants (Σ : EAst.global_context) : EAst.global_context :=
  filter (is_constant ∘ snd) Σ.

Lemma declared_constant_only_constants Σ kn decl :
  ETyping.declared_constant Σ kn decl ->
  ETyping.declared_constant (only_constants Σ) kn decl.
Proof.
  unfold ETyping.declared_constant.
  intros lookup_decl.
  induction Σ; [easy|].
  destruct a as (kn' & decl').
  cbn in *.
  destruct (is_constant decl') eqn:isconst.
  - cbn in *.
    destruct (kername_eq_dec _ _) as [<-|?]; easy.
  - apply IHΣ.
    destruct (kername_eq_dec _ _).
    + inversion lookup_decl; subst; easy.
    + auto.
Qed.

Lemma eval_only_constants Σ s t :
  Σ ⊢ s ▷ t ->
  only_constants Σ ⊢ s ▷ t.
Proof.
  induction 1; eauto using eval, declared_constant_only_constants.
Qed.

Definition trans_cst (cst : constant_body) : EAst.constant_body :=
  {| EAst.cst_body := cst_body cst |}.

Definition trans (Σ : global_env) : EAst.global_context :=
  let map_decl kn (decl : global_decl) : list (kername * EAst.global_decl) :=
      match decl with
      | ConstantDecl cst => [(kn, EAst.ConstantDecl (trans_cst cst))]
      | InductiveDecl _ => []
      end in
  flat_map (fun '(kn, decl) => map_decl kn decl) Σ.

Lemma declared_constant_trans Σ kn cst :
  declared_constant Σ kn cst ->
  ETyping.declared_constant (trans Σ) kn (trans_cst cst).
Proof.
  unfold ETyping.declared_constant, declared_constant in *.
  induction Σ; [easy|]; intros lookup.
  cbn in *.
  destruct a as (kn' & []).
  - cbn in *.
    unfold eq_kername in *.
    destruct (kername_eq_dec kn kn') as [<-|].
    + now inversion lookup; subst; clear lookup.
    + now apply IHΣ.
  - apply IHΣ.
    unfold eq_kername in lookup.
    now destruct (kername_eq_dec _ _).
Qed.

Fixpoint has_use (rel : nat) (t : term) : bool :=
  match t with
  | tRel i => i =? rel
  | tEvar _ ts => fold_right orb false (map (has_use rel) ts)
  | tLambda _ body => has_use (S rel) body
  | tLetIn _ val body => has_use rel val || has_use (S rel) body
  | tApp hd arg => has_use rel hd || has_use rel arg
  | tCase _ discr brs => has_use rel discr || fold_right orb false (map (has_use rel ∘ snd) brs)
  | tProj _ t => has_use rel t
  | tFix defs _
  | tCoFix defs _ => fold_right orb false (map (has_use (rel + #|defs|) ∘ dbody) defs)
  | _ => false
  end.

Fixpoint valid_dearg_mask (mask : bitmask) (body : term) : Prop :=
  match body, mask with
  | tLetIn na val body, _ => valid_dearg_mask mask body
  | tLambda _ body, b :: mask =>
    (if b then has_use 0 body = false else True) /\ valid_dearg_mask mask body
  | _, [] => True
  | _, _ => False
  end.

Lemma dearg_cst_body_top_nil t :
  dearg_cst_body_top [] t = t.
Proof.
  induction t; auto.
  cbn.
  now rewrite IHt2.
Qed.

(* We use our own "properly ordered" contexts to represent the lambdas/lets
   that we debox away. Unlike the rest of MetaCoq, these contexts actually
   have the first declaration at the beginning. *)
Fixpoint subst_context (t : term) (k : nat) (Γ : context) : context :=
  match Γ with
  | [] => []
  | cd :: Γ => map_decl (csubst t k) cd :: subst_context t (S k) Γ
  end.

Definition mkLambda_or_LetIn (cd : context_decl) (t : term) : term :=
  match decl_body cd with
  | None => tLambda (decl_name cd) t
  | Some body => tLetIn (decl_name cd) body t
  end.

Definition it_mkLambda_or_LetIn (Γ : context) (u : term) : term :=
  fold_right mkLambda_or_LetIn u Γ.

Fixpoint decompose_body_masked (mask : bitmask) (t : term) : context * term :=
  match mask, t with
  | _, tLetIn na val body =>
    let (Γ, t) := decompose_body_masked mask body in
    (vdef na val :: Γ, t)
  | b :: mask, tLambda na body =>
    let (Γ, t) := decompose_body_masked mask body in
    (vass na :: Γ, t)
  | _, _ => ([], t)
  end.

Definition vasses (Γ : context) : context :=
  filter (fun cd => match decl_body cd with
                    | Some _ => false
                    | None => true
                    end) Γ.

Lemma vasses_app Γ Γ' :
  vasses (Γ ++ Γ') = vasses Γ ++ vasses Γ'.
Proof.
  unfold vasses.
  now rewrite filter_app.
Qed.

Ltac refold :=
  repeat
    match goal with
    | [H: context[fold_right _ ?t ?Γ] |- _] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [|- context[fold_right _ ?t ?Γ]] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [H: context[filter _ ?Γ] |- _] => progress (fold (vasses Γ) in * )
    | [|- context[filter _ ?Γ]] => progress (fold (vasses Γ) in * )
    end.

Lemma decompose_body_masked_spec mask Γ t t' :
  valid_dearg_mask mask t ->
  (Γ, t') = decompose_body_masked mask t ->
  #|vasses Γ| = #|mask| /\
  it_mkLambda_or_LetIn Γ t' = t.
Proof.
  revert Γ t' mask.
  induction t using term_forall_list_ind; intros Γ t' mask valid_mask eq.
  all: cbn in *.
  all: try solve [destruct mask; [|easy]; inversion eq; easy].
  - destruct mask as [|b mask]; inversion eq; subst; clear eq; [easy|].
    cbn in *.
    destruct (decompose_body_masked mask t) as (Γ' & t'') eqn:decomp_eq.
    inversion H0; subst; clear H0.
    symmetry in decomp_eq.
    cbn.
    refold.
    now destruct (IHt _ _ _ (proj2 valid_mask) decomp_eq) as (-> & ->).
  - destruct (decompose_body_masked mask t2) eqn:decomp_eq.
    symmetry in decomp_eq.
    destruct (IHt2 _ _ _ valid_mask decomp_eq).
    now destruct mask; inversion eq; subst.
Qed.

Lemma valid_dearg_mask_spec mask t :
  valid_dearg_mask mask t ->
  exists Γ inner,
    #|vasses Γ| = #|mask| /\ it_mkLambda_or_LetIn Γ inner = t.
Proof.
  intros is_valid.
  destruct (decompose_body_masked mask t) as (Γ & inner) eqn:decomp.
  exists Γ, inner.
  now apply decompose_body_masked_spec.
Qed.

Lemma subst_it_mkLambda_or_LetIn t k Γ u :
  csubst t k (it_mkLambda_or_LetIn Γ u) =
  it_mkLambda_or_LetIn (subst_context t k Γ) (csubst t (k + length Γ) u).
Proof.
  revert t k u.
  induction Γ as [|cd Γ IH]; intros t k u.
  - cbn.
    f_equal; lia.
  - cbn in *; refold.
    destruct cd as [na [val|]];
      cbn in *; refold;
      repeat (f_equal; rewrite ?IH; try lia).
Qed.

Lemma length_subst_context t k Γ :
  #|subst_context t k Γ| = #|Γ|.
Proof.
  revert t k.
  induction Γ; [easy|]; intros t k.
  cbn.
  now rewrite IHΓ.
Qed.

Lemma has_use_closed k t n :
  closedn k t ->
  k <= n ->
  has_use n t = false.
Proof.
  revert k n.
  induction t using term_forall_list_ind; intros k n' clos klen;
    cbn in *; auto.
  - propify.
    destruct (Nat.eqb_spec n n'); lia.
  - induction H; [easy|].
    cbn in *.
    propify.
    easy.
  - easy.
  - propify.
    easy.
  - propify.
    easy.
  - propify.
    induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    easy.
  - easy.
  - revert k n' clos klen.
    induction H; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    replace (n' + S #|l|) with (S n' + #|l|) by abstract lia.
    apply (IHForall (S k)); [|easy].
    now rewrite Nat.add_succ_r.
  - revert k n' clos klen.
    induction H; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    replace (n' + S #|l|) with (S n' + #|l|) by abstract lia.
    apply (IHForall (S k)); [|easy].
    now rewrite Nat.add_succ_r.
Qed.

Lemma has_use_csubst k t u k' :
  has_use k t = false ->
  closedn k u ->
  k < k' ->
  has_use k (csubst u k' t) = false.
Proof.
  revert k u k'.
  induction t using term_forall_list_ind; intros k u k' use_eq clos kltn;
    cbn in *; propify; auto.
  - destruct (Nat.compare_spec k' n) as [->| |].
    + now apply has_use_closed with k.
    + cbn.
      propify.
      lia.
    + cbn.
      propify.
      lia.
  - induction H; [easy|].
    cbn in *.
    propify.
    easy.
  - apply IHt; [easy| |easy].
    now eapply closed_upwards.
  - split; [easy|].
    apply IHt2; [easy| |easy].
    now eapply closed_upwards.
  - split; [easy|].
    apply IHt2; [easy| |easy].
    now eapply closed_upwards.
  - induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    easy.
  - revert k k' kltn use_eq clos.
    induction H; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    rewrite map_length in *.
    split.
    + apply H; [easy| |easy].
      now eapply closed_upwards.
    + setoid_rewrite map_length in IHForall.
      replace (k + S #|l|) with (S k + #|l|) in * by abstract lia.
      rewrite <- Nat.add_succ_r.
      apply IHForall; [easy|easy|].
      now eapply closed_upwards.
  - revert k k' kltn use_eq clos.
    induction H; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    rewrite map_length in *.
    split.
    + apply H; [easy| |easy].
      now eapply closed_upwards.
    + setoid_rewrite map_length in IHForall.
      replace (k + S #|l|) with (S k + #|l|) in * by abstract lia.
      rewrite <- Nat.add_succ_r.
      apply IHForall; [easy|easy|].
      now eapply closed_upwards.
Qed.

Lemma valid_dearg_mask_nil t : valid_dearg_mask [] t.
Proof. induction t; easy. Qed.

Lemma valid_dearg_mask_csubst mask t u k :
  valid_dearg_mask mask t ->
  closed u ->
  valid_dearg_mask mask (csubst u k t).
Proof.
  revert mask u k.
  induction t using term_forall_list_ind; intros mask u k valid_mask clos;
    cbn in *;
    try solve [now destruct mask].
  - destruct mask; [|easy].
    apply valid_dearg_mask_nil.
  - destruct mask; [easy|].
    split.
    + destruct b; [|easy].
      now apply (has_use_csubst 0).
    + now apply IHt.
Qed.

Lemma vasses_subst_context t k Γ :
  vasses (subst_context t k Γ) = vasses Γ.
Proof.
  revert t k.
  induction Γ as [|cd Γ IH]; [easy|]; intros t k.
  cbn in *.
  unfold map_decl.
  destruct cd.
  cbn in *.
  destruct decl_body; cbn.
  - easy.
  - f_equal.
    easy.
Qed.

Lemma dearg_cst_body_top_subst mask s k Γ inner :
  #|vasses Γ| = #|mask| ->
  dearg_cst_body_top mask (subst [s] k (it_mkLambda_or_LetIn Γ inner)) =
  subst [s] k (dearg_cst_body_top mask (it_mkLambda_or_LetIn Γ inner)).
Proof.
  revert mask s k inner.
  induction Γ as [|cd Γ IH]; intros mask s k inner len_eq.
  - destruct mask; [|easy].
    cbn in *.
    rewrite !dearg_cst_body_top_nil.
    now f_equal.
  - destruct cd as [na [body|]];
      cbn in *; refold.
    + now rewrite IH by easy.
    + destruct mask as [|[] mask].
      * easy.
      * rewrite IH by easy.
        cbn in *.
        unfold subst1.
        now rewrite !distr_subst.
      * now rewrite IH.
Qed.

Lemma eval_dearg_single_head Σ mask head args v :
  #|args| = #|mask| ->
  Σ ⊢ dearg_single mask head args ▷ v ->
  exists hdv, Σ ⊢ head ▷ hdv.
Proof.
  revert head args v.
  induction mask as [|[] mask IH]; intros head args v len_eq ev.
  - cbn in *.
    now apply eval_mkApps_head in ev.
  - destruct args as [|a args]; [easy|].
    cbn in *.
    easy.
  - destruct args as [|a args]; [easy|].
    cbn in *.
    specialize (IH _ _ _ ltac:(easy) ev).
    destruct IH as (appv & ev_app).
    now apply eval_tApp_head in ev_app.
Qed.

Lemma eval_dearg_cst_body_top_inv Σ mask Γ inner v :
  env_closed Σ ->
  closed (it_mkLambda_or_LetIn Γ inner) ->
  #|mask| = #|vasses Γ| ->
  Σ ⊢ dearg_cst_body_top mask (it_mkLambda_or_LetIn Γ inner) ▷ v ->
  exists tv,
    Σ ⊢ it_mkLambda_or_LetIn Γ inner ▷ tv.
Proof.
  intros env_clos clos len_eq ev.
  induction #|Γ| as [|Γlen IH] eqn:Γlen_eq in Γ, mask, inner, v, clos, len_eq, ev |- *.
  - destruct Γ, mask; try easy.
    cbn in *.
    now rewrite dearg_cst_body_top_nil in *.
  - destruct Γ as [|[na [body|]] Γ];
      cbn in *; refold.
    + easy.
    + apply eval_tLetIn_inv in ev as (bodyv & ev_body & ev_let).
      propify.
      assert (closed bodyv) by (now eapply eval_closed).
      rewrite closed_subst in ev_let by easy.
      rewrite <- dearg_cst_body_top_subst in ev_let by easy.
      rewrite <- closed_subst in ev_let by easy.
      rewrite subst_it_mkLambda_or_LetIn in ev_let.
      cbn in *.
      apply IH in ev_let as (tv & ev_tv).
      * exists tv.
        rewrite <- subst_it_mkLambda_or_LetIn in ev_tv.
        now econstructor.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * now rewrite length_subst_context.
    + destruct mask as [|[] mask].
      * easy.
      * eexists.
        now eapply eval_atom.
      * eexists.
        now eapply eval_atom.
Qed.

Lemma eval_dearg_single_heads Σ hd hd' hdv mask args v :
  #|mask| = #|args| ->
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ dearg_single mask hd args ▷ v ->
  Σ ⊢ dearg_single mask hd' args ▷ v.
Proof.
  revert hd hd' hdv args v.
  induction mask as [|[] mask IH]; intros hd hd' hdv args v len_eq ev_hd ev_hd' ev;
    cbn in *.
  - destruct args; [|easy].
    now rewrite (eval_deterministic ev ev_hd).
  - now destruct args.
  - destruct args; [easy|].
    cbn in *.
    apply eval_dearg_single_head in ev as ev_app_hd; [|easy].
    destruct ev_app_hd as (app_hdv & ev_app_hd).
    eapply IH.
    3: {
      eapply eval_tApp_heads; [| |exact ev_app_hd].
      all: easy.
    }
    all: easy.
Qed.

Lemma no_use_subst k t s s' :
  has_use k t = false ->
  subst [s] k t = subst [s'] k t.
Proof.
  revert k.
  induction t using term_forall_list_ind; cbn in *; intros k no_use; propify.
  - easy.
  - destruct (Nat.leb_spec k n).
    + now rewrite !(proj2 (nth_error_None _ _)) by (cbn; lia).
    + easy.
  - easy.
  - f_equal.
    induction H; [easy|].
    cbn in *.
    propify.
    now f_equal.
  - now f_equal.
  - now f_equal.
  - now f_equal.
  - easy.
  - easy.
  - f_equal; [easy|].
    destruct no_use as (_ & no_use).
    induction X; [easy|].
    cbn in *.
    propify.
    f_equal; [|easy].
    now f_equal.
  - now f_equal.
  - f_equal.
    revert k no_use.
    induction H; [easy|]; intros k no_use.
    unfold map_def in *.
    destruct x; cbn in *; propify.
    f_equal.
    + f_equal.
      apply H.
      rewrite <- (proj1 no_use).
      now f_equal.
    + rewrite <- Nat.add_succ_r in *.
      apply IHForall.
      now rewrite Nat.add_succ_comm.
  - f_equal.
    revert k no_use.
    induction H; [easy|]; intros k no_use.
    unfold map_def in *.
    destruct x; cbn in *; propify.
    f_equal.
    + f_equal.
      apply H.
      rewrite <- (proj1 no_use).
      now f_equal.
    + rewrite <- Nat.add_succ_r in *.
      apply IHForall.
      now rewrite Nat.add_succ_comm.
Qed.

Lemma dearg_single_correct Σ body args mask t :
  env_closed Σ ->
  closed body ->
  Forall (closedn 0) args ->
  valid_dearg_mask mask body ->
  #|args| = #|mask| ->
  Σ ⊢ mkApps body args ▷ t ->
  Σ ⊢ dearg_single mask (dearg_cst_body_top mask body) args ▷ t.
Proof.
  intros env_clos body_clos args_clos valid_mask len_eq ev.
  destruct (valid_dearg_mask_spec _ _ valid_mask) as (Γ & inner & vasses_len & <-).
  induction #|Γ| as [|Γlen IH] eqn:eq
    in Γ, mask, valid_mask, args, body_clos, args_clos, inner, ev, len_eq, vasses_len |- *.
  1: { destruct Γ, mask, args; try easy.
       cbn in *.
       now rewrite dearg_cst_body_top_nil. }
  destruct Γ as [|[na [body|]] Γ];
    cbn in *; refold.
  - easy.
  - apply eval_mkApps_head in ev as ev_let.
    destruct ev_let as (letv & ev_let).
    apply eval_tLetIn_inv in ev_let as ev_subst.
    destruct ev_subst as (bodyv & ev_body & ev_subst).
    propify.
    assert (closed bodyv) by (now eapply eval_closed).
    unshelve epose proof
             (IH args mask
                 (subst_context bodyv 0 Γ)
                 (csubst bodyv #|Γ| inner)
                 _ _ _ _ _ _ _) as IH.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply closed_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply valid_dearg_mask_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      eapply (eval_mkApps_heads _ _ _ letv); [easy|easy|].
      now eapply eval_mkApps_heads; [exact ev_let| |]; easy.
    + now rewrite vasses_subst_context.
    + now rewrite length_subst_context.
    + rewrite <- subst_it_mkLambda_or_LetIn in IH.
      apply eval_dearg_single_head in IH as ev_top; [|easy].
      destruct ev_top as (topv & ev_top).
      rewrite subst_it_mkLambda_or_LetIn in ev_top.
      apply eval_dearg_cst_body_top_inv in ev_top as ev_sub_top; cycle 1.
      * easy.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * destruct ev_sub_top as (sub_top & ev_sub_top).
        rewrite <- subst_it_mkLambda_or_LetIn in ev_top.
        eapply eval_dearg_single_heads; [easy|exact ev_top| |easy].
        econstructor; [easy|].
        rewrite !closed_subst in * by easy.
        now rewrite <- dearg_cst_body_top_subst.
  - destruct mask as [|b mask]; [easy|];
      cbn in *; refold.
    destruct args as [|a args]; [easy|].
    cbn in *.
    apply eval_mkApps_head in ev as ev_app.
    destruct ev_app as (appv & ev_app).
    apply eval_tApp_tLambda_inv in ev_app as ev_subst.
    destruct ev_subst as (av & ev_a & ev_subst).
    assert (closed av).
    { apply Forall_inv in args_clos.
      now eapply eval_closed. }
    unshelve epose proof
    (IH args mask
        (subst_context av 0 Γ)
        (csubst av #|Γ| inner)
        _ _ _ _ _ _ _) as IH.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply closed_csubst.
    + now apply Forall_inv_tail in args_clos.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply valid_dearg_mask_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now eapply eval_mkApps_heads; [exact ev_app| |]; easy.
    + now rewrite vasses_subst_context.
    + now rewrite length_subst_context.
    + apply eval_dearg_single_head in IH as ev_top; [|easy].
      destruct ev_top as (topv & ev_top).
      apply eval_dearg_cst_body_top_inv in ev_top as ev_sub_top; cycle 1.
      * easy.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * rewrite <- !subst_it_mkLambda_or_LetIn in *.
        destruct ev_sub_top as (sub_top & ev_sub_top).
        rewrite !closed_subst in * by easy.
        destruct b.
        -- eapply eval_dearg_single_heads; [easy|exact ev_top| |easy].
           unfold subst1.
           rewrite <- dearg_cst_body_top_subst by easy.
           now erewrite no_use_subst.
        -- eapply eval_dearg_single_heads; [easy|exact ev_top| |easy].
           rewrite dearg_cst_body_top_subst in ev_top by easy.
           rewrite <- closed_subst in ev_top by easy.
           eapply eval_beta; [|easy|easy].
           now eapply eval_atom.
Qed.

Lemma nth_set_bit_eq k bs d :
  nth k (set_bit k bs) d = true.
Proof.
  revert bs.
  induction k as [|k IH]; intros bs.
  - now destruct bs.
  - cbn.
    now destruct bs.
Qed.

Lemma nth_set_bit_neq k k' bs :
  k <> k' ->
  nth k (set_bit k' bs) false = nth k bs false.
Proof.
  revert bs k'.
  induction k as [|k IH]; intros bs k' ne.
  - destruct k'; [easy|].
    now destruct bs.
  - destruct k'.
    + destruct bs; [|easy].
      now destruct k.
    + destruct bs.
      * cbn.
        assert (k <> k') by easy.
        clear -H.
        revert k H.
        induction k'; intros k H.
        -- cbn.
           destruct k; [easy|].
           now destruct k.
        -- cbn.
           destruct k; [easy|].
           easy.
      * cbn.
        easy.
Qed.

Lemma nth_bitmask_or k bs1 bs2 :
  nth k (bs1 #|| bs2) false = nth k bs1 false || nth k bs2 false.
Proof.
  revert bs1 bs2.
  induction k; intros bs1 bs2.
  + cbn.
    destruct bs1, bs2; try easy.
    cbn.
    now rewrite orb_false_r.
  + destruct bs1, bs2; try easy.
    * cbn in *.
      now rewrite orb_false_r.
    * cbn in *.
      easy.
Qed.

Lemma nth_tl {A} k (l : list A) d :
  nth k (tl l) d = nth (S k) l d.
Proof.
  destruct l.
  - now destruct k.
  - easy.
Qed.

Lemma used_context_vars_has_use k bs t :
  nth k (used_context_vars bs t) false = nth k bs false || has_use k t.
Proof.
  revert k bs.
  induction t using term_forall_list_ind; intros k bs; cbn in *;
    rewrite ?orb_false_r; auto.
  - destruct (Nat.eqb_spec n k) as [->|].
    + rewrite nth_set_bit_eq.
      now rewrite orb_true_r.
    + rewrite nth_set_bit_neq by easy.
      now rewrite orb_false_r.
  - revert k bs.
    induction H; intros k bs.
    + cbn.
      now rewrite orb_false_r.
    + cbn.
      rewrite nth_bitmask_or.
      rewrite H.
      rewrite orb_assoc.
      rewrite IHForall.
      now destruct (nth k bs false).
  - now rewrite nth_tl, IHt.
  - rewrite nth_tl.
    rewrite IHt2.
    cbn.
    rewrite IHt1.
    now rewrite orb_assoc.
  - rewrite IHt2, IHt1.
    now rewrite orb_assoc.
  - rewrite orb_assoc.
    induction X; cbn in *.
    + rewrite IHt.
      now rewrite orb_false_r.
    + rewrite nth_bitmask_or.
      rewrite p0, IHt.
      rewrite orb_assoc.
      rewrite IHX.
      destruct (nth k bs false); [easy|].
      destruct (has_use k t); [easy|].
      easy.
  - rewrite nth_nth_error, nth_error_skipn, <- nth_nth_error.
    generalize #|m|.
    intros.
    induction H; cbn in *.
    + rewrite app_nth2; rewrite repeat_length; [|easy].
      rewrite minus_plus.
      now rewrite orb_false_r.
    + rewrite nth_bitmask_or.
      rewrite H.
      rewrite app_nth2; rewrite repeat_length; [|easy].
      rewrite minus_plus.
      rewrite orb_assoc.
      rewrite IHForall.
      destruct (nth k bs false); [|easy].
      rewrite Nat.add_comm.
      now destruct (has_use _ _).
  - rewrite nth_nth_error, nth_error_skipn, <- nth_nth_error.
    generalize #|m|.
    intros.
    induction H; cbn in *.
    + rewrite app_nth2; rewrite repeat_length; [|easy].
      rewrite minus_plus.
      now rewrite orb_false_r.
    + rewrite nth_bitmask_or.
      rewrite H.
      rewrite app_nth2; rewrite repeat_length; [|easy].
      rewrite minus_plus.
      rewrite orb_assoc.
      rewrite IHForall.
      destruct (nth k bs false); [|easy].
      rewrite Nat.add_comm.
      now destruct (has_use _ _).
Qed.

Lemma hd_nth {A} d (l : list A) :
  hd d l = nth 0 l d.
Proof. now destruct l. Qed.

Lemma func_body_used_params_valid_mask uses_before t ty use_mask uses_after :
  func_body_used_params uses_before t ty = (use_mask, uses_after) ->
  uses_after = used_context_vars uses_before t /\
  valid_dearg_mask (bitmask_not use_mask) t.
Proof.
  revert uses_before ty use_mask uses_after.
  induction t using term_forall_list_ind;
    intros uses_before ty use_mask uses_after fun_eq;
    cbn in *;
    try solve [now noconf fun_eq].
  - destruct ty; try solve [now noconf fun_eq].
    destruct (func_body_used_params _ _ _) eqn:fun_eq'.
    noconf fun_eq.
    apply IHt in fun_eq' as (-> & valid).
    split; [easy|].
    cbn.
    split; [|easy].
    destruct (hd false _) eqn:hd_eq; [easy|].
    cbn.
    rewrite hd_nth in hd_eq.
    now rewrite used_context_vars_has_use in hd_eq.
  - destruct (func_body_used_params _ _ _) eqn:fun_eq'.
    noconf fun_eq.
    now apply IHt2 in fun_eq'.
Qed.

Section dearg_correct.
Context (ind_masks : list (kername * mib_masks)).
Context (const_masks : list (kername * bitmask)).
Notation get_ctor_mask := (get_ctor_mask ind_masks).
Notation get_mib_masks := (get_mib_masks ind_masks).
Notation get_const_mask := (get_const_mask const_masks).
Notation dearg := (dearg ind_masks const_masks).
Notation dearg_aux := (dearg_aux ind_masks const_masks).
Notation dearg_env := (dearg_env ind_masks const_masks).
Notation dearg_case := (dearg_case ind_masks).

Lemma dearg_aux_mkApps args args' hd :
  dearg_aux args (mkApps hd args') = dearg_aux (map dearg args' ++ args) hd.
Proof.
  revert args hd.
  induction args' as [|a args' IH]; intros args hd; [easy|].
  cbn.
  now rewrite IH.
Qed.

Lemma dearg_single_app bs t args args' :
  dearg_single bs t (args ++ args') =
  dearg_single (skipn #|args| bs) (dearg_single (firstn #|args| bs) t args) args'.
Proof.
  revert t args args'.
  induction bs as [|[] bs IH]; intros t args args'; cbn in *.
  - now rewrite firstn_nil, skipn_nil, mkApps_app.
  - now destruct args; cbn.
  - now destruct args; cbn.
Qed.

Lemma dearg_single_mask_length Σ bs h args v :
  Σ ⊢ dearg_single bs h args ▷ v ->
  (forall na b, v <> tLambda na b) ->
  #|bs| <= #|args|.
Proof.
  intros ev disc.
  revert args h ev.
  induction bs as [|b bs IH]; intros args h ev; cbn in *; [easy|].
  destruct b, args; cbn in *;
    (try apply eval_tLambda_inv in ev; subst); intuition.
Qed.

Lemma csubst_mkApps s k t args :
  csubst s k (mkApps t args) =
  mkApps (csubst s k t) (map (csubst s k) args).
Proof.
  revert s k t.
  induction args as [|a args IH]; intros s k t; cbn in *; [easy|].
  now rewrite IH.
Qed.

Ltac refold' :=
  refold;
  repeat
    match goal with
    | [H: context[dearg_aux [] ?t] |- _] => progress (fold (dearg t) in * )
    | [|- context[dearg_aux [] ?t]] => progress (fold (dearg t) in * )
    end.

Fixpoint is_first_order (t : term) : bool :=
  match t with
  | tBox => true
  | tRel _ => true
  | tVar _ => true
  | tEvar _ ts => fold_right andb true (map is_first_order ts)
  | tLambda _ _ => false
  | tLetIn _ val body => is_first_order val && is_first_order body
  | tApp hd arg => is_first_order hd && is_first_order arg
  | tConst _ => true
  | tConstruct _ _ => true
  | tCase _ disc brs =>
    is_first_order disc &&
    fold_right andb true (map (is_first_order ∘ snd) brs)
  | tProj _ t => is_first_order t
  | tFix defs _ => false
  | tCoFix defs _ => false
  end.

Lemma value_app_inv hd arg :
  value (tApp hd arg) ->
  value hd /\ value arg.
Proof.
  intros val.
  inversion val.
  - easy.
  - destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in H.
    inversion H; subst; clear H.
    apply Forall_app in H1 as (? & ?).
    depelim H1.
    split; [|easy].
    now apply value_app.
  - destruct args as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in H.
    inversion H; subst; clear H.
    apply Forall_app in H0 as (? & ?).
    depelim H0.
    split; [|easy].
    apply value_stuck_fix; [easy|].
    unfold isStuckFix in *.
    destruct f; try easy.
    destruct (cunfold_fix m n) as [(? & ?)|]; [|easy].
    unfold ETyping.is_nth_constructor_app_or_box in *.
    destruct (nth_error args n0) eqn:nth; [|easy].
    now erewrite nth_error_app_left in H1.
Qed.

Lemma value_normalize_tBox v :
  value v ->
  normalize v = tBox ->
  v = tBox.
Proof.
  intros val norm.
  destruct val.
  - now destruct t.
  - rewrite normalize_mkApps_notlambda in norm by (now destruct t).
    destruct t; try easy; simp normalize in norm; solve_discr.
  - destruct f; try easy.
    rewrite normalize_mkApps_notlambda in norm by easy.
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
  - rewrite normalize_mkApps_notlambda in norm by (now destruct t).
    destruct t; try easy; simp normalize in norm; solve_discr.
  - destruct f; try easy.
    rewrite normalize_mkApps_notlambda in norm by easy.
    simp normalize in norm; solve_discr.
Qed.

Lemma subst_dearg_single s k mask t  args :
  subst s k (dearg_single mask t args) =
  dearg_single mask (subst s k t) (map (subst s k) args).
Proof.
  induction mask as [|[] mask IH] in mask, args, k, t |- *; cbn in *.
  - now rewrite subst_mkApps.
  - destruct args.
    + cbn.
      f_equal.
      rewrite IH.
      now rewrite <- commut_lift_subst.
    + apply IH.
  - destruct args.
    + cbn.
      f_equal.
      rewrite IH.
      cbn.
      now rewrite commut_lift_subst.
    + apply IH.
Qed.

Lemma count_uses_dearg_single_nil k mask t :
  count_uses k (dearg_single mask t []) = count_uses k t.
Proof.
  induction mask as [|[] mask IH] in mask, k, t |- *.
  - easy.
  - cbn in *.
    rewrite IH.
    rewrite count_uses_lift by lia.
    now f_equal.
  - cbn in *.
    rewrite IH.
    cbn.
    rewrite count_uses_lift by lia.
    rewrite Nat.add_0_r.
    now f_equal.
Qed.

Lemma normalize_mkApps_dearg_single mask t args args' :
  normalize (mkApps (dearg_single mask t args) args') =
  normalize (dearg_single mask t (args ++ args')).
Proof.
  induction mask as [|[] mask IH] in t, mask, args, args' |- *; cbn in *.
  - now rewrite <- mkApps_app.
  - destruct args, args'; cbn in *.
    + easy.
    + rewrite <- normalize_mkApps_normalize_hd, normalize_tApp.
      simp normalize.
      cbn.
      rewrite ared_affinely_used; [|apply ared_to_normalize|]; last first.
      { unfold affinely_used.
        rewrite count_uses_dearg_single_nil.
        now rewrite count_uses_lift_all. }
      unfold subst1.
      rewrite <- normalize_subst_r.
      rewrite normalize_mkApps_normalize_hd.
      rewrite subst_dearg_single.
      rewrite simpl_subst_k by easy.
      apply IH.
    + now rewrite app_nil_r.
    + apply (IH _ args (t1 :: args')).
  - destruct args, args'; cbn in *.
    + easy.
    + rewrite <- normalize_mkApps_normalize_hd, normalize_tApp.
      simp normalize.
      cbn.
      rewrite ared_affinely_used; [|apply ared_to_normalize|]; last first.
      { unfold affinely_used.
        rewrite count_uses_dearg_single_nil.
        cbn.
        now rewrite count_uses_lift_all. }
      unfold subst1.
      rewrite <- normalize_subst_r.
      rewrite normalize_mkApps_normalize_hd.
      rewrite subst_dearg_single.
      cbn.
      rewrite simpl_subst_k by easy.
      rewrite lift0_id.
      apply IH.
    + now rewrite app_nil_r.
    + apply (IH _ args (t1 :: args')).
Qed.

Lemma normalize_mkApps_dearg_aux s args args' :
  normalize (mkApps (dearg_aux args s) args') =
  normalize (dearg_aux (args ++ args') s).
Proof.
  induction s in s, args, args' |- *; cbn in *; try now rewrite <- mkApps_app.
  - now rewrite IHs1.
  - apply normalize_mkApps_dearg_single.
  - apply normalize_mkApps_dearg_single.
  - destruct p.
    now rewrite mkApps_app.
Qed.

Lemma normalize_mkApps_dearg s args :
  normalize (mkApps (dearg s) args) =
  normalize (dearg_aux args s).
Proof. apply normalize_mkApps_dearg_aux. Qed.

(*
Lemma normalize_csubst_dearg s k args t :
  normalize (csubst (dearg s) k (dearg_aux args t)) =
  normalize (dearg_aux (map (csubst (dearg s) k) args) (csubst s k t)).
Proof.
  induction t in k, t, args |- * using term_forall_list_ind;
    cbn in *; rewrite ?csubst_mkApps; cbn in *.
  - easy.
  - destruct (k ?= n); try easy.
    apply normalize_mkApps_dearg.
  - easy.
  - rewrite !normalize_mkApps by easy.
    f_equal.
    simp normalize.
    f_equal.
    induction H; [easy|].
    cbn in *.
    rewrite H.
    now cbn.
  - destruct args.
    + cbn.
      now rewrite !normalize_tLambda, IHt.
    + cbn.
      rewrite !normalize_mkApps.
      f_equal.
      rewrite !normalize_tApp.
      cbn.
      rewrite !normalize_tLambda.
      rewrite IHt.
      cbn.
      unfold affinely_used.
      rewrite count_uses_csubst_dearg_aux by easy.
      destruct (_ <=? _); cbn; [|easy].
      rewrite IHt.
      *
      easy.
      admit.
    f_equal.
    f_equal.
    f_equal.
  - simp normalize.
    f_equal.
    induction H; [easy|].
    cbn in *.
    now rewrite H.
  - rewrite !normalize_tLambda.
    now f_equal.
  - rewrite !normalize_tLetIn.

    now f_equal.
  -
*)

Lemma lift_dearg_single n k mask t args :
  lift n k (dearg_single mask t args) = dearg_single mask (lift n k t) (map (lift n k) args).
Proof.
  induction mask as [|[] mask IH] in mask, t, args, k |- *; cbn in *.
  - now rewrite lift_mkApps.
  - destruct args.
    + cbn.
      rewrite IH.
      cbn.
      now symmetry; rewrite permute_lift.
    + apply IH.
  - destruct args; cbn.
    + rewrite IH.
      cbn.
      now symmetry; rewrite permute_lift.
    + apply IH.
Qed.

Lemma dearg_lambdas_lift n k mask ar t :
  dearg_lambdas mask ar (lift n k t) =
  ((dearg_lambdas mask ar t).1, lift n k (dearg_lambdas mask ar t).2).
Proof.
  induction mask as [|[] mask IH] in mask, k, t, ar |- *; cbn in *.
  - easy.
  - destruct t; try easy; cbn in *.
    + now destruct (_ <=? _).
    + change tBox with (lift n k tBox).
      rewrite <- distr_lift_subst10.
      now rewrite IH.
  - destruct t; try easy; cbn in *.
    + now destruct (_ <=? _).
    + rewrite IH.
      assert (H: forall {A B} (t : A * B), t = (fst t, snd t)) by (now intros ? ? []).
      now symmetry; rewrite (H _ _ (dearg_lambdas _ _ _)); symmetry.
Qed.

Lemma lift_dearg_aux n k args t :
  lift n k (dearg_aux args t) = dearg_aux (map (lift n k) args) (lift n k t).
Proof.
  induction t in k, args, t |- * using term_forall_list_ind; cbn in *.
  - now rewrite lift_mkApps.
  - rewrite lift_mkApps.
    cbn.
    now destruct (_ <=? _).
  - now rewrite lift_mkApps.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    induction H; [easy|].
    cbn in *.
    now rewrite H, IHForall.
  - rewrite lift_mkApps.
    cbn.
    now rewrite IHt.
  - rewrite lift_mkApps.
    cbn.
    now rewrite IHt1, IHt2.
  - rewrite IHt1.
    cbn.
    now rewrite IHt2.
  - apply lift_dearg_single.
  - now rewrite lift_dearg_single.
  - destruct p.
    rewrite lift_mkApps.
    f_equal.
    unfold dearg_case.
    destruct (get_mib_masks _); last first.
    + cbn.
      rewrite IHt.
      f_equal.
      induction X; [easy|].
      cbn.
      now rewrite p, IHX.
    + cbn.
      rewrite IHt.
      f_equal.
      unfold mapi.
      generalize 0.
      induction X; [easy|]; intros ?.
      cbn in *.
      rewrite IHX.
      f_equal.
      destruct (find _ _) as [((? & ?) & ?)|].
      -- rewrite <- dearg_lambdas_lift.
         now rewrite p.
      -- cbn.
         now rewrite p.
  - rewrite lift_mkApps.
    cbn.
    now rewrite IHt.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    rewrite map_length.
    induction H in k |- *; [easy|].
    cbn in *.
    rewrite <- Nat.add_succ_r.
    rewrite IHForall.
    f_equal.
    unfold map_def.
    cbn.
    f_equal.
    now rewrite H.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    rewrite map_length.
    induction H in k |- *; [easy|].
    cbn in *.
    rewrite <- Nat.add_succ_r.
    rewrite IHForall.
    f_equal.
    unfold map_def.
    cbn.
    f_equal.
    now rewrite H.
Qed.

Lemma lift_dearg n k t :
  lift n k (dearg t) = dearg (lift n k t).
Proof. apply lift_dearg_aux. Qed.

Fixpoint valid_branch_mask (mask : bitmask) (t : term) : Prop :=
  match t, mask with
  | tLambda na body, b :: mask =>
    (if b then has_use 0 body = false else True) /\
    valid_branch_mask mask body
  | _, [] => True
  | _, _ => False
  end.

Definition valid_branch (mm : mib_masks) (ind c : nat) (br : term) : Prop :=
  match find (fun '(ind', c', _) => (ind' =? ind) && (c' =? c)) (ctor_masks mm) with
  | Some (_, _, mask) => valid_branch_mask mask br
  | None => True
  end.

Definition valid_case_masks (ind : inductive) (npars : nat) (brs : list (nat * term)) : Prop :=
  match get_mib_masks (inductive_mind ind) with
  | Some mm =>
    (#|param_mask mm| = npars)
    /\ ∥ Alli (fun c '(ar, br) => valid_branch mm (inductive_ind ind) c br) 0 brs ∥
  | None =>
    True
  end.

(* Prop representing that all case discriminations in a term are valid according to the masks:
   they have the proper number of parameters and their branches are compatible with the masks
   (they are iterated lambdas, and when 'true' appears in the mask, the parameter is unused *)
Fixpoint valid_cases (t : term) : Prop :=
  match t with
  | tEvar _ ts => fold_right and True (map valid_cases ts)
  | tLambda _ body => valid_cases body
  | tLetIn _ val body => valid_cases val /\ valid_cases body
  | tApp hd arg => valid_cases hd /\ valid_cases arg
  | tCase (ind, npars) discr brs =>
    valid_cases discr /\
    fold_right and True (map (valid_cases ∘ snd) brs) /\
    valid_case_masks ind npars brs
  | tProj _ t => valid_cases t
  | tFix defs _
  | tCoFix defs _  => fold_right and True (map (valid_cases ∘ dbody) defs)
  | _ => True
  end.

(* Proposition representing whether masks are valid for entire environment.
   We should be able to prove that our analysis produces masks that satisfy this
   predicate. *)
Fixpoint valid_masks (Σ : global_env) : Prop :=
  match Σ with
  | (kn, decl) :: Σ =>
    match decl with
    | ConstantDecl {| cst_body := Some body |} =>
      valid_dearg_mask (get_const_mask kn) body /\
      valid_cases body
    | _ => True
    end /\ valid_masks Σ
  | [] => True
  end.

(* Check if all applications are applied enough to be deboxed without eta expansion *)
Fixpoint is_expanded_aux (nargs : nat) (t : term) : bool :=
  match t with
  | tBox => true
  | tRel _ => true
  | tVar _ => true
  | tEvar _ ts => fold_right andb true (map (is_expanded_aux 0) ts)
  | tLambda _ body => is_expanded_aux 0 body
  | tLetIn _ val body => is_expanded_aux 0 val && is_expanded_aux 0 body
  | tApp hd arg => is_expanded_aux 0 arg && is_expanded_aux (S nargs) hd
  | tConst kn => #|get_const_mask kn| <=? nargs
  | tConstruct ind c => #|get_ctor_mask ind c| <=? nargs
  | tCase _ discr brs =>
    is_expanded_aux 0 discr &&
    fold_right andb true (map (is_expanded_aux 0 ∘ snd) brs)
  | tProj _ t => is_expanded_aux 0 t
  | tFix defs _
  | tCoFix defs _ => fold_right andb true (map (is_expanded_aux 0 ∘ dbody) defs)
  end.

(* Check if all applications are applied enough to be deboxed without eta expansion *)
Definition is_expanded (t : term) : bool :=
  is_expanded_aux 0 t.

(* Like above, but check all bodies in environment. This assumption does not necessarily hold,
   but we should try to make it hold by eta expansion before quoting *)
Fixpoint is_expanded_env (Σ : global_env) : bool :=
  match Σ with
  | (kn, decl) :: Σ =>
    match decl with
    | ConstantDecl {| cst_body := Some body |} => is_expanded body
    | _ => true
    end && is_expanded_env Σ
  | [] => true
  end.

Lemma has_use_subst k t u k' :
  has_use k t = false ->
  k < k' ->
  has_use k (subst u k' t) = false.
Proof.
  revert k u k'.
  induction t using term_forall_list_ind; intros k u k' use_eq kltn;
    cbn in *; propify; auto.
  - destruct (Nat.leb_spec k' n).
    + destruct (nth_error _ _) eqn:nth.
      * admit.
      * cbn.
        propify.
        apply nth_error_None in nth.
        lia.
    + cbn.
      propify.
      lia.
  - induction H; [easy|].
    cbn in *.
    propify.
    easy.
  - now apply IHt.
  - easy.
  - easy.
  - induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    easy.
  - revert k k' kltn use_eq.
    induction H; [easy|]; intros k k' kltn use_eq.
    destruct x.
    cbn in *.
    propify.
    rewrite map_length in *.
    split.
    + now apply H.
    + setoid_rewrite map_length in IHForall.
      replace (k + S #|l|) with (S k + #|l|) in * by abstract lia.
      rewrite <- Nat.add_succ_r.
      now apply IHForall.
  - revert k k' kltn use_eq.
    induction H; [easy|]; intros k k' kltn use_eq.
    destruct x.
    cbn in *.
    propify.
    rewrite map_length in *.
    split.
    + now apply H.
    + setoid_rewrite map_length in IHForall.
      replace (k + S #|l|) with (S k + #|l|) in * by abstract lia.
      rewrite <- Nat.add_succ_r.
      now apply IHForall.
Admitted.

Lemma valid_branch_mask_subst mask s k t :
  valid_branch_mask mask t ->
  valid_branch_mask mask (subst s k t).
Proof.
  intros valid.
  induction mask as [|b mask IH] in mask, s, k, t, valid |- *.
  - cbn in *.
    now destruct (subst s k t).
  - cbn in *.
    destruct t; try contradiction.
    cbn in *.
    split; [|now apply IH].
    destruct b; [|easy].
    now apply has_use_subst.
Qed.

Lemma subst_dearg_case s k ind c discr brs :
  valid_case_masks ind c brs ->
  subst s k (dearg_case ind c discr brs) =
  dearg_case ind c (subst s k discr) (map (on_snd (subst s k)) brs).
Proof.
  intros valid.
  unfold dearg_case, valid_case_masks in *.
  destruct (get_mib_masks _) as [masks|]; [|easy].
  cbn.
  f_equal.
  rewrite map_mapi, mapi_map.
  destruct valid as (? & [valid]).
  eapply Alli_mapi_spec; [eassumption|].
  clear valid.
  intros ? [] valid.
  cbn in *.
  unfold valid_branch in valid.
  destruct (find _ _) as [((? & ?) & ?)|]; [|easy].
  induction b as [|[] mask IH] in k, t, valid, n0 |- *; [easy| |]; cbn in *.
  - destruct t; cbn in *; try contradiction.
    intuition auto.
    unfold subst1.
    change [tBox] with (map (subst s k) [tBox]) at 3.
    change (S k) with (#|[tBox]| + k).
    rewrite <- distr_subst.
    apply IH.
    now apply valid_branch_mask_subst.
  - destruct t; cbn in *; try contradiction.
    intuition auto.
    rewrite <- IH by easy.
    now destruct (dearg_lambdas mask n0 t).
Qed.

Lemma dearg_single_enough_args mask t args :
  dearg_single mask t args =
  mkApps (dearg_single mask t (firstn #|mask| args)) (skipn #|mask| args).
Proof.
  induction mask as [|b mask IH] in mask, t, args |- *; cbn in *.
  - now rewrite skipn_0.
  - destruct args as [|a args].
    + now rewrite skipn_nil.
    + cbn.
      rewrite skipn_cons.
      destruct b; apply IH.
Qed.

Lemma dearg_expanded_aux k t args :
  is_expanded_aux k t = true ->
  dearg_aux args t = mkApps (dearg_aux (firstn k args) t) (skipn k args).
Proof.
  intros expanded.
  induction t in k, t, args, expanded |- * using term_forall_list_ind; cbn in *;
    refold';
    try now rewrite mkApps_nested, firstn_skipn.
  - propify; intuition auto.
    now erewrite IHt1 by eassumption.
  - propify.
    symmetry; rewrite dearg_single_enough_args; symmetry.
    rewrite mkApps_nested, firstn_firstn.
    replace (Init.Nat.min _ _) with #|get_const_mask s| by lia.
    rewrite dearg_single_enough_args.
    f_equal.
    now rewrite skipn_firstn_slice by assumption.
  - propify.
    symmetry; rewrite dearg_single_enough_args; symmetry.
    rewrite mkApps_nested, firstn_firstn.
    replace (Init.Nat.min _ _) with #|get_ctor_mask i n| by lia.
    rewrite dearg_single_enough_args.
    f_equal.
    now rewrite skipn_firstn_slice by assumption.
  - destruct p.
    now rewrite mkApps_nested, firstn_skipn.
Qed.

Lemma dearg_expanded t args :
  is_expanded t = true ->
  dearg_aux args t = mkApps (dearg t) args.
Proof. apply dearg_expanded_aux. Qed.

(*
Lemma csubst_dearg_single s k mask t args :
  csubst s k t = t ->
  csubst s k (dearg_single mask t args) =
  dearg_single mask t (map (csubst s k) args).
Proof.
  intros not_rel.
  induction mask as [|[] mask IH] in s, k, mask, t, args, not_rel |- *; cbn in *.
  - now rewrite csubst_mkApps, not_rel.
  - destruct args; cbn.
    + f_equal.
      rewrite IH.
      easy.
      rewrite subst_lift.
    destruct t; cbn in *; try easy.
*)

Lemma is_expanded_aux_lift k n k' t :
  is_expanded_aux k (lift n k' t) = is_expanded_aux k t.
Proof.
  induction t in n, k, k', t |- * using term_forall_list_ind; cbn in *; auto.
  - now destruct (_ <=? _).
  - induction H; [easy|].
    cbn in *.
    now rewrite H, IHForall.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - rewrite IHt.
    f_equal.
    induction X; [easy|].
    cbn in *.
    now rewrite p0, IHX.
  - induction H in k' |- *; [easy|].
    cbn.
    rewrite <- Nat.add_succ_r.
    now rewrite H, IHForall.
  - induction H in k' |- *; [easy|].
    cbn.
    rewrite <- Nat.add_succ_r.
    now rewrite H, IHForall.
Qed.

Lemma is_expanded_lift n k t :
  is_expanded (lift n k t) = is_expanded t.
Proof. apply is_expanded_aux_lift. Qed.

Lemma dearg_subst_expanded s k t args :
  valid_cases t ->
  is_expanded s = true ->
  is_expanded_aux #|args| t = true ->
  dearg_aux (map (subst [dearg s] k ∘ dearg) args) (subst [s] k t) =
  subst [dearg s] k (dearg_aux (map dearg args) t).
Proof.
  intros vcases es et.
  induction t using term_forall_list_ind in s, k, t, args, vcases, es, et |- *; cbn in *; refold'.
  - now rewrite subst_mkApps, map_map.
  - rewrite subst_mkApps, map_map.
    cbn in *.
    rewrite Nat.leb_compare.
    destruct (Nat.compare_spec k n) as [->| |].
    + rewrite Nat.sub_diag.
      cbn.
      rewrite dearg_expanded, lift_dearg; [easy|].
      now rewrite is_expanded_lift.
    + rewrite !(proj2 (nth_error_None _ _)) by (cbn in *; lia).
      now rewrite dearg_expanded.
    + now rewrite dearg_expanded.
  - now rewrite subst_mkApps, map_map.
  - rewrite subst_mkApps, map_map.
    cbn in *.
    rewrite !map_map.
    f_equal.
    f_equal.
    induction H; [easy|].
    cbn in *.
    propify.
    rewrite (H _ _ []) by easy.
    cbn in *.
    f_equal.
    now apply IHForall.
  - rewrite subst_mkApps, map_map.
    cbn.
    f_equal.
    f_equal.
    now apply (IHt _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    propify.
    f_equal.
    f_equal.
    + now apply (IHt1 _ _ []).
    + now apply (IHt2 _ _ []).
  - propify.
    specialize (IHt1 s k (t2 :: args)).
    cbn in *.
    rewrite <- IHt1 by easy.
    f_equal.
    f_equal.
    now apply (IHt2 _ _ []).
  - now rewrite subst_dearg_single, map_map.
  - now rewrite subst_dearg_single, map_map.
  - propify.
    destruct p.
    rewrite subst_mkApps, !map_map.
    cbn.
    f_equal.
    rewrite subst_dearg_case by admit.
    rewrite map_map.
    cbn.
    f_equal.
    + now apply (IHt _ _ []).
    + destruct et as (_ & et).
      destruct vcases as (vdiscr & vcases & _).
      clear -X vdiscr vcases es et X.
      induction X; [easy|].
      cbn in *.
      propify.
      f_equal; [f_equal|].
      * now apply (p _ _ []).
      * now apply IHX.
  - rewrite subst_mkApps, map_map.
    cbn.
    f_equal.
    f_equal.
    now apply (IHt _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    rewrite !map_map.
    f_equal.
    cbn.
    f_equal.
    rewrite map_length.
    revert k; induction H; intros k; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    f_equal; [|now apply IHForall].
    unfold map_def; cbn.
    f_equal.
    now apply (H _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    rewrite !map_map.
    f_equal.
    cbn.
    f_equal.
    rewrite map_length.
    revert k; induction H; intros k; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    f_equal; [|now apply IHForall].
    unfold map_def; cbn.
    f_equal.
    now apply (H _ _ []).
Admitted.

Lemma dearg_correct Σ hd args v :
  (* Masks produced by analysis are valid *)
  valid_masks Σ ->
  (* All relevant applications are applied enough *)
  is_expanded_env Σ = true ->
  closed hd ->
  Forall (closedn 0) args ->
  trans Σ ⊢ mkApps hd args ▷ v ->
  trans (dearg_env Σ) ⊢ dearg_aux (map dearg args) hd ▷ dearg v.
Proof.
  intros masks expanded clos_hd clos_args ev.
  depind ev.
  - destruct (mkApps_elim hd args).
    destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in *.
    cbn in *.
    noconf H.
    rewrite dearg_aux_mkApps, <- map_app, firstn_skipn, map_app.
    specialize (IHev1 _ _ _ masks expanded eq_refl).
    specialize (IHev2 _ [] _ masks expanded eq_refl).
    destruct f;
      cbn in *;
      rewrite ?mkApps_app;
      cbn in *;
      try now econstructor.
    + easy.
    + rewrite dearg_single_app.
      apply dearg_single_mask_length in IHev1 as ?; [|easy].
      rewrite firstn_all2, skipn_all2 by easy.
      cbn.
      now econstructor.
    + rewrite dearg_single_app.
      apply dearg_single_mask_length in IHev1 as ?; [|easy].
      rewrite firstn_all2, skipn_all2 by easy.
      cbn.
      now econstructor.
    + destruct p.
      rewrite mkApps_app.
      cbn.
      now econstructor.
  - destruct (mkApps_elim hd args).
    destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in *.
    cbn in *.
    noconf H.
    rewrite dearg_aux_mkApps, <- map_app, firstn_skipn, map_app.
    specialize (IHev1 _ _ _ masks expanded eq_refl).
    specialize (IHev2 _ [] _ masks expanded eq_refl).
    specialize (IHev3 _ [] _ masks expanded eq_refl).
    cbn in *; refold'.
    destruct f0; cbn in *.

Lemma dearg_correct Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  Σ ⊢ dearg_aux (map dearg args) hd ▷ dearg v.
Proof.
  intros ev.
  depind ev.
  - destruct (mkApps_elim hd args).
    destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in *.
    cbn in *.
    noconf H.
    rewrite dearg_aux_mkApps, <- map_app, firstn_skipn, map_app.
    specialize (IHev1 _ _ _ eq_refl).
    specialize (IHev2 _ [] _ eq_refl).
    cbn in *; refold'.
    admit.
  - destruct (mkApps_elim hd args).
    destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in *.
    cbn in *.
    noconf H.
    rewrite dearg_aux_mkApps, <- map_app, firstn_skipn, map_app.
    specialize (IHev1 _ _ _ eq_refl).
    specialize (IHev2 _ [] _ eq_refl) as (? & ? & ?).
    specialize (IHev3 _ [] _ eq_refl).
    cbn in *; refold'.
    rewrite closed_subst in IHev3 by admit.
    destruct f0; cbn in *.
    + admit.
    + admit.
    + admit.
    + admit.
    + refold'.
      rewrite mkApps_app.
      cbn.
      eexists.
      split.
      * eapply eval_beta; [easy|easy|].
      eapply aeval_beta.
    +
    rewrite normalize_tLambda in norm_lam.
    apply eval_to_value in ev_lam as value_x.
    destruct (value_normalize_tLambda _ _ _ value_x norm_lam) as (body & -> & norm_body).
    clear norm_lam value_x.

    destruct f0; cbn in *.
    + admit.
    + admit.
    + admit.
    + admit.
    + refold'.
      rewrite mkApps_app.
      cbn.
      eexists; split.
      eapply eval_beta.
      eassumption.
      eassumption.
      rewrite closed_subst in ev_sub by admit.
      apply eval_dearg_subst in ev_sub as (? & ? & ?).
      rewrite <- norm_a, <- norm_body in H.
      rewrite eval_dearg_
      (* have: normalize av = normalize (dearg a')
               subst [av] 0 body =
      (* red  t' ->
         subst s k t = foo ->
         subst

      (* need something about subst [dearg a] 0 (dearg b) *)
      rewrite closed_subst in ev_sub by admit.
      apply eval_dearg_subst in ev_sub as (? & ? & ?).
      exists (normalize x).
      rewrite H0.
      rewrite normalize_normalize.
      split; [|congruence].
      assert (H': forall t v, Σ ⊢ normalize t ▷ normalize v <-> Σ ⊢ t ▷ v) by admit.
      apply H'.
      rewrite normalize_mkApps.
      apply H'.
      rewrite map_app.
      rewrite ?mkApps_app.
      cbn.
      eapply eval_beta.
      2: { apply H'. eassumption. }
      2: { rewrite closed_subst by admit.
           rewrite norm_a.
           apply H'.
           rewrite <- (normalize_subst [dearg a']).
           rewrite <- H0, normalize_normalize.
           apply H'.
           eassumption. }
      rewrite <- norm_body.
      apply H'.
      rewrite <- normalize_mkApps.
      rewrite <- normalize_tLambda.
      rewrite normalize_normalize.
      apply H'.
      eassumption.
      admit.
    + admit.
    + admit.
    + admit.
    + admit.
    +
      rewrite closed_subst by admit.
      eapply eval_dearg_subst.
      (* normalize x = tLambda na (normalize (dearg b)) and
         normalize
      try now econstructor.
      exists tBox.
      split; [|easy].
      apply eval_mkApps_args in ev_f as (? & ?).
      eapply eval_box_apps; [|now apply eval_atom].
      now apply Forall2_app.
    + apply eval_mkApps_head in ev1 as (? & ?).
      now depelim H1.
    + apply eval_mkApps_head in ev1 as (? & ?).
      now depelim H1.
    + apply eval_mkApps_head in ev1 as (? & ?).
      now depelim H1.
    +
rewrite mkApps_app.
      cbn in *.

      apply eval_to_value in ev_f.
      destruct ev_f.
      * replace t0 with tBox in * by admit.
      * admit.
      *
    destruct f;
      cbn in *;
      rewrite ?mkApps_app;
      cbn in *;
      try solve [now eexists; split; [|apply dearged_syntactic]; econstructor].
    + destruct IHev1 as (? & ? & ?).
      destruct H0; cbn in *.
      * exists tBox.
      exists tBox.
      split; [|apply dearged_syntactic].
      admit.
    + eexists.
      split; [|apply dearged_syntactic].

    + easy.
    + unfold dearg_const in *.
      destruct (find _ _) as [[]|] eqn:find_eq;
        [|rewrite mkApps_app; cbn in *; now econstructor].
      rewrite dearg_single_app.
      apply dearg_single_mask_length in IHev1 as ?; [|easy].
      rewrite firstn_all2, skipn_all2 by easy.
      cbn.
      now econstructor.
    + unfold dearg_ctor in *.
      rewrite dearg_single_app.
      apply dearg_single_mask_length in IHev1 as ?; [|easy].
      rewrite firstn_all2, skipn_all2 by easy.
      cbn.
      now econstructor.
    + destruct p.
      rewrite mkApps_app.
      cbn.
      now econstructor.


Lemma dearg_correct Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  Σ ⊢ dearg_aux (map dearg args) hd ▷ dearg v.
Proof.
  intros ev.
  remember (mkApps hd args) eqn:teq.
  induction ev using eval_evals_ind in ev, t, v, hd, args, teq; cbn in *.
  - destruct (mkApps_elim hd args).
    destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in *.
    cbn in *.
    noconf teq.
    rewrite dearg_aux_mkApps.
    rewrite <- map_app.
    rewrite firstn_skipn.
    specialize (IHev1 f l eq_refl).
    specialize (IHev2 t [] eq_refl).
    rewrite map_app.
    destruct f;
      cbn in *;
      rewrite ?mkApps_app;
      cbn in *;
      try now econstructor.
    + easy.
    + unfold dearg_const in *.
      destruct (find _ _) as [[]|] eqn:find_eq;
        [|rewrite mkApps_app; cbn in *; now econstructor].
      rewrite dearg_single_app.
      apply dearg_single_mask_length in IHev1 as ?; [|easy].
      rewrite firstn_all2, skipn_all2 by easy.
      cbn.
      now econstructor.
    + unfold dearg_ctor in *.
      rewrite dearg_single_app.
      apply dearg_single_mask_length in IHev1 as ?; [|easy].
      rewrite firstn_all2, skipn_all2 by easy.
      cbn.
      now econstructor.
    + destruct p.
      rewrite mkApps_app.
      cbn.
      now econstructor.
  - destruct (mkApps_elim hd args).
    destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in *.
    cbn in *.
    noconf teq.
    rewrite dearg_aux_mkApps, <- map_app, firstn_skipn.
    specialize (IHev1 _ _ eq_refl).
    specialize (IHev2 _ [] eq_refl).
    specialize (IHev3 _ [] eq_refl).
    rewrite map_app.
    destruct f0; cbn in *; rewrite ?mkApps_app; cbn in *; refold'.
    + eapply eval_beta.
      easy.
      easy.
      admit.
    + admit.
    + admit.
    + admit.
    + eapply eval_beta.
      easy.
      easy.
      admit.
    + eapply eval_beta.
      easy.
      easy.

    destruct f0;
      cbn in *;
      rewrite ?mkApps_app;
      cbn in *;
      try now econstructor.
    destruct l; cbn in *.
    subst
    2:
    specialize (IHev1 _ _ eq_refl).
    specialize (IHev2 _ [] eq_refl).
    cbn in *.
      unfold dearg_case in *.
      rewrite firstn_length_le.

      rewrite skipn_all_eq.
      revert l ev1 IHev1.
      generalize (tConst k) as hd.
      induction b; cbn in *; intros hd l ev IHev1; rewrite ?mkApps_app; try now econstructor.
      destruct a.
      * destruct l as [|? ? _]; cbn in *.
        -- now apply eval_tLambda_inv in IHev1.
        -- apply IHb; [|easy].
      rewrite dearg_single_app.

      destruct (skipn _ _); cbn; [now econstructor|].
      destruct b0; cbn.

    + cbn.
      rewrite map_app.
      rewrite mkApps_app.
      cbn.
      eapply eval_box; [easy|].
      now apply (IHev2 t []).
    + cbn.
      rewrite map_app.
      rewrite mkApps_app.
      cbn.
      eapply eval_box; [easy|].
      now apply (IHev2 t []).
    rewrite map_app.
    cbn.
    clear IHev2.
    destruct l.
    cbn in *.
    +
    rewrite map_app.
    rewrite <- dearg_aux_mkApps.
    cbn.
    apply (IHev1 _ [t]).
    cbn.
  - rewrite dearg_mkApps.
    cbn.
    admit.
  -
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  -
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma dearg_correct_b Σ t v :
  Σ ⊢ t ▷ v ->
  Σ ⊢ dearg t ▷ dearg v.
Proof.
  intros ev.
  induction ev using eval_evals_ind.
  - cbn in *.
    unfold dearg in IHev2.
