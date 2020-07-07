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
Notation dearg := (dearg ind_masks const_masks).
Notation dearg_aux := (dearg_aux ind_masks const_masks).

Reserved Infix "β=" (at level 70, right associativity).

Inductive betaeq : term -> term -> Prop :=
| betaeq_beta na body arg arg' sub :
    arg β= arg' ->
    sub β= subst1 arg' 0 body ->
    tApp (tLambda na body) arg β= sub
| betaeq_box : tBox β= tBox
| betaeq_rel i : tRel i β= tRel i
| betaeq_var id : tVar id β= tVar id
| betaeq_evar i ts ts' :
    Forall2 betaeq ts ts' ->
    tEvar i ts β= tEvar i ts'
| betaeq_lambda na body body' :
    body β= body' ->
    tLambda na body β= tLambda na body'
| betaeq_let_in na val val' body body' :
    val β= val' ->
    body β= body' ->
    tLetIn na val body β= tLetIn na val' body'
| betaeq_app hd hd' arg arg' :
    hd β= hd' ->
    arg β= arg' ->
    tApp hd arg β= tApp hd' arg'
| betaeq_const kn : tConst kn β= tConst kn
| betaeq_construct ind c : tConstruct ind c β= tConstruct ind c
| betaeq_case ind npars disc disc' brs brs' :
    disc β= disc' ->
    betaeq_branches brs brs' ->
    tCase (ind, npars) disc brs β= tCase (ind, npars) disc' brs'
| betaeq_proj p t t' :
    t β= t' ->
    tProj p t β= tProj p t'
| betaeq_fix defs defs' i :
    betaeq_defs defs defs' ->
    tFix defs i β= tFix defs' i
| betaeq_cofix defs defs' i :
    betaeq_defs defs defs' ->
    tCoFix defs i β= tCoFix defs' i

with betaeq_branches : list (nat × term) -> list (nat × term) -> Prop :=
| betaeq_branches_nil : betaeq_branches [] []
| betaeq_branches_cons ar t t' brs brs' :
    t β= t' ->
    betaeq_branches brs brs' ->
    betaeq_branches ((ar, t) :: brs) ((ar, t') :: brs')

with betaeq_defs : mfixpoint term -> mfixpoint term -> Prop :=
| betaeq_defs_nil : betaeq_defs [] []
| betaeq_defs_cons dname rarg dbody dbody' defs defs' :
    dbody β= dbody' ->
    betaeq_defs defs defs' ->
    betaeq_defs
      ({| dname := dname; dbody := dbody; rarg := rarg |} :: defs)
      ({| dname := dname; dbody := dbody'; rarg := rarg |} :: defs')

where "t β= t'" := (betaeq t t').

Scheme betaeq_mind := Induction for betaeq Sort Prop
  with betaeq_branches_mind := Induction for betaeq_branches Sort Prop
  with betaeq_defs_mind := Induction for betaeq_defs Sort Prop.

Fixpoint betaeq_refl (t : term) {struct term} : t β= t :=
  match t with
  | tBox =>
with betaeq_branches_refl (brs : list (nat × term)) : betaeq_branches brs brs
with betaeq_defs_refl (defs : mfixpoint term) : betaeq_defs defs defs.

Global Instance betaeq_equivalence : Coq.Classes.RelationClasses.Equivalence betaeq.
Proof.
  constructor.
  - intros x.
    induction x.

Lemma dearg_mkApps hd args :
  dearg (mkApps hd args) = dearg_aux (map dearg args) hd.
Proof.
  Admitted.

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

(*
Lemma csubst_dearg_aux args s k t :
  csubst (dearg_aux args s) k (dearg_aux args t) =
  dearg_aux args (csubst s k t).
Proof.
  induction t in s, k, t |- * using term_forall_list_ind; cbn in *.
  - rewrite csubst_mkApps.
    cbn.
  - now destruct (_ ?= _).
  - easy.
  - f_equal.
    induction H; [easy|].
    cbn.
    now rewrite H, IHForall.
  - now rewrite IHt.
  - now f_equal.
  -
*)

Ltac refold' :=
  refold;
  repeat
    match goal with
    | [H: context[dearg_aux [] ?t] |- _] => progress (fold (dearg t) in * )
    | [|- context[dearg_aux [] ?t]] => progress (fold (dearg t) in * )
    end.

(* dearg_aux args (csubst (tConstruct _ _ _) 0 (tRel 0) = dearg_aux args (tConstruct _ _ _) *)
(* dearg_aux args (csubst (tConstruct _ _ _) 0 (tLambda na (tRel 0))) =
   dearg_aux args (tLambda na (tConstruct _ _ _)) =
   mkApps (tLambda na (dearg (tConstruct _ _ _))) args *)

(*
Lemma csubst_dearg_aux args args' s k t :
  csubst (dearg_aux args s) k (dearg_aux args' t) =
  dearg_aux (map (csubst (dearg_aux args s) k) args') (csubst (dearg_aux args s) k t).
Proof.
  induction t in args, args', s, k, t |- * using term_forall_list_ind; cbn in *.
  - now rewrite csubst_mkApps.
  - rewrite csubst_mkApps.
    cbn.
    destruct (_ ?= _).
    + rewrite
*)


(*
Section examples.
  Open Scope string.
  Definition foo : kername := (MPfile [], "foo").
  Definition masks : list (kername * bitmask) :=
    [(foo, [false; false])].

  Notation dearg := (Optimize.dearg [] masks).
  Definition s := (tApp (tConst foo) (tVar "something")).
  Definition t := (tLambda nAnon (tApp (tRel 1) (tVar "something 2"))).
  Compute (dearg (csubst s 0 t)).
  Compute (csubst (dearg s) 0 (dearg t)).

  Definition prog :=
    tLetIn
      nAnon
      (tApp (tConst foo) (tVar "something"))
      (tLambda nAnon (tApp (tRel 1) (tVar "something 2"))).

  (* Given
       let x := foo "something" in fun y => x "something 2"
     this evaluates to
       fun y => foo "something" "something 2"

     With eta expansion, we first transform
       let x := foo "something" in fun y => x "something 2"
     to
       let x := fun v => foo "something" v in fun y => x "something 2"

     and then this evaluates to
       fun y => (fun v => foo "something" v) "something 2") *)

  (* = tApp (tApp (tConst (MPfile [], "foo")) (tVar "something")) (tVar "something 2")
     : term *)
  (* = tApp
         (tLambda nAnon (tApp (tApp (tConst (MPfile [], "foo")) (tVar "something")) (tRel 0)))
         (tVar "something 2")
     : term *)
End examples.
*)

(*
Lemma eval_csubst_dearg Σ s k t v :
  Σ ⊢ dearg (csubst s k t) ▷ v ->
  Σ ⊢ csubst (dearg s) k (dearg t) ▷ v.
Proof.
  induction t in s, k, t, v |- * using term_forall_list_ind; intros ev; cbn in *.
  - easy.
  - now destruct (_ ?= _).
  - easy.
  - now apply eval_tEvar_inv in ev.
  - refold'.
*)

(*
Lemma csubst_dearg s k t :
  csubst (dearg s) k (dearg t) =
  dearg (csubst s k t).
Proof.
  induction t in s, k, t |- * using term_forall_list_ind; cbn in *.
  - easy.
  - now destruct (_ ?= _).
  - easy.
  - f_equal.
    induction H; [easy|].
    cbn.
    now rewrite H, IHForall.
  - now rewrite IHt.
  - now f_equal.
  - refold'.
    rewrite <- (app_nil_r [dearg t2]).
    change [dearg t2] with (map dearg [t2]).
    rewrite <- dearg_aux_mkApps.
    rewrite dearg_aux_mkApps.
    cbn.
    rewrite IHt1.
    rewrite mkApps_csubst.
    cbn.
    rewrite
  csubst (dearg s) k (dearg_aux args t) =
  dearg_aux args (csubst (dearg s) k
  dearg_aux (map dearg args) (csubst s k t)
    rewrite <- IHt2.
    rewrite <- dearg_aux_mkApps.
*)

Inductive dearged_result Σ v : term -> Prop :=
| dearged_syntactic : dearged_result Σ v (dearg v)
| dearged_extensional dv :
    (forall a vv,
        Σ ⊢ tApp v a ▷ vv ->
        exists v'v,
          Σ ⊢ tApp dv a ▷ v'v /\
          dearged_result Σ vv v'v) ->
    dearged_result Σ v dv.

Lemma dearg_correct Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists dv,
    Σ ⊢ dearg_aux (map dearg args) hd ▷ dv /\
    dearged_result Σ v dv.
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
    destruct IHev1 as (fv & ev_f & drf).
    rewrite map_app.
    exists tBox.
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
