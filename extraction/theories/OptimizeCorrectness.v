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
From MetaCoq.Erasure Require Import ETyping.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Import EAstUtils.
Import Erasure.
Import ExAst.
Import ExTyping.

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
  ETyping.declared_constant (trans Σ) kn cst ->
  exists n typ,
    nth_error Σ n =
    Some (kn, ConstantDecl {| cst_type := typ; cst_body := EAst.cst_body cst |}).
Proof.
  unfold ETyping.declared_constant.
  intros decl.
  induction Σ as [|(kn' & cst') Σ IH]; [easy|].
  destruct cst'; cbn in *.
  - destruct (kername_eq_dec _ _) as [->|].
    + noconf decl.
      cbn in *.
      exists 0, (cst_type c).
      now destruct c.
    + destruct IH as (n' & typ & cond); [assumption|].
      now exists (S n'), typ.
  - destruct IH as (n' & typ & cond); [assumption|].
    now exists (S n'), typ.
Qed.

Fixpoint has_use (rel : nat) (t : term) : bool :=
  match t with
  | tRel i => i =? rel
  | tEvar _ ts => existsb (has_use rel) ts
  | tLambda _ body => has_use (S rel) body
  | tLetIn _ val body => has_use rel val || has_use (S rel) body
  | tApp hd arg => has_use rel hd || has_use rel arg
  | tCase _ discr brs => has_use rel discr || existsb (has_use rel ∘ snd) brs
  | tProj _ t => has_use rel t
  | tFix defs _
  | tCoFix defs _ => existsb (has_use (#|defs| + rel) ∘ dbody) defs
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
  ∑ Γ inner,
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
    rewrite <- Nat.add_succ_r in *.
    now eapply IHForall.
  - revert k n' clos klen.
    induction H; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    rewrite <- Nat.add_succ_r in *.
    now eapply IHForall.
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
  - rewrite map_length.
    revert k k' kltn use_eq clos.
    induction H; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    split.
    + apply H; [easy| |easy].
      now eapply closed_upwards.
    + rewrite <- !Nat.add_succ_r in *.
      apply IHForall; [easy|easy|].
      now eapply closed_upwards.
  - rewrite map_length.
    revert k k' kltn use_eq clos.
    induction H; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    split.
    + apply H; [easy| |easy].
      now eapply closed_upwards.
    + rewrite <- !Nat.add_succ_r in *.
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
  #|mask| <= #|args| ->
  Σ ⊢ dearg_single mask head args ▷ v ->
  ∑ hdv, Σ ⊢ head ▷ hdv.
Proof.
  revert head args v.
  induction mask as [|[] mask IH]; intros head args v l ev.
  - cbn in *.
    now apply eval_mkApps_head in ev.
  - destruct args as [|a args]; cbn in *; [easy|].
    now eapply (IH _ args).
  - destruct args as [|a args]; cbn in *; [easy|].
    edestruct (IH (tApp head a) args) as (appv & ev_app).
    + easy.
    + exact ev.
    + now apply eval_tApp_head in ev_app.
Qed.

Lemma eval_dearg_cst_body_top_inv Σ mask Γ inner v :
  env_closed Σ ->
  closed (it_mkLambda_or_LetIn Γ inner) ->
  #|mask| = #|vasses Γ| ->
  Σ ⊢ dearg_cst_body_top mask (it_mkLambda_or_LetIn Γ inner) ▷ v ->
  ∑ tv,
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

Lemma eval_dearg_single_heads mask args Σ hd hd' hdv v :
  #|mask| <= #|args| ->
  Σ ⊢ hd ▷ hdv ->
  Σ ⊢ dearg_single mask hd' args ▷ v ->
  Σ ⊢ hd' ▷ hdv ->
  Σ ⊢ dearg_single mask hd args ▷ v.
Proof.
  revert hd hd' hdv args v.
  induction mask as [|[] mask IH]; intros hd hd' hdv args v len ev_hd ev ev_hd';
    cbn in *.
  - now eapply eval_mkApps_heads; [|eassumption|eassumption].
  - now destruct args; cbn in *.
  - destruct args; cbn in *; [easy|].
    apply eval_dearg_single_head in ev as ev_app_hd; [|easy].
    destruct ev_app_hd as (app_hdv & ev_app_hd).
    eapply IH.
    + easy.
    + now eapply eval_tApp_heads; [| |exact ev_app_hd].
    + eassumption.
    + easy.
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
      now apply IHForall.
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
    + rewrite <- !Nat.add_succ_r in *.
      now apply IHForall.
Qed.

Lemma dearg_single_correct Σ body args mask t :
  env_closed Σ ->
  closed body ->
  Forall (closedn 0) args ->
  valid_dearg_mask mask body ->
  #|mask| <= #|args| ->
  Σ ⊢ mkApps body args ▷ t ->
  Σ ⊢ dearg_single mask (dearg_cst_body_top mask body) args ▷ t.
Proof.
  intros env_clos body_clos args_clos valid_mask l ev.
  destruct (valid_dearg_mask_spec _ _ valid_mask) as (Γ & inner & vasses_len & <-).
  induction #|Γ| as [|Γlen IH] eqn:eq
    in Γ, mask, valid_mask, args, body_clos, args_clos, inner, ev, l, vasses_len |- *.
  1: { destruct Γ, mask, args; try easy; cbn in *;
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
        eapply eval_dearg_single_heads; eauto.
        econstructor; [easy|].
        rewrite !closed_subst in * by easy.
        now rewrite <- dearg_cst_body_top_subst.
  - destruct mask as [|b mask]; [easy|];
      cbn in *; refold.
    destruct args as [|a args]; cbn in *; [easy|].
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
        -- eapply eval_dearg_single_heads; eauto; [easy|].
           unfold subst1.
           rewrite <- dearg_cst_body_top_subst by easy.
           now erewrite no_use_subst.
        -- eapply eval_dearg_single_heads; eauto; [easy|].
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
Notation dearg_decl := (dearg_decl ind_masks const_masks).
Notation dearg_cst := (dearg_cst ind_masks const_masks).
Notation dearg_case := (dearg_case ind_masks).

Lemma dearg_aux_mkApps args args' hd :
  dearg_aux args (mkApps hd args') = dearg_aux (map dearg args' ++ args) hd.
Proof.
  revert args hd.
  induction args' as [|a args' IH]; intros args hd; [easy|].
  cbn.
  now rewrite IH.
Qed.

Lemma dearg_mkApps hd args :
  dearg (mkApps hd args) = dearg_aux (map dearg args) hd.
Proof.
  unfold dearg.
  now rewrite dearg_aux_mkApps, app_nil_r.
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
  value hd × value arg.
Proof.
  intros val.
  inversion val.
  - easy.
  - destruct l as [|? ? _] using MCList.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in H.
    inversion H; subst; clear H.
    apply All_app in H1 as (? & ?).
    depelim a0.
    split; [|easy].
    now apply value_app.
  - destruct args as [|? ? _] using MCList.rev_ind; cbn in *; [now subst|].
    rewrite mkApps_app in H.
    inversion H; subst; clear H.
    apply All_app in H0 as (? & ?).
    depelim a0.
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
  ∑ body',
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

Definition valid_masks_decl (p : kername * global_decl) : Prop :=
  match p with
  | (kn, ConstantDecl {| cst_body := Some body |}) =>
    valid_dearg_mask (get_const_mask kn) body /\ valid_cases body
  | _ => True
  end.

(* Proposition representing whether masks are valid for entire environment.
   We should be able to prove that our analysis produces masks that satisfy this
   predicate. *)
Definition valid_masks_env (Σ : global_env) : Prop :=
  Forall valid_masks_decl Σ.

(* Check if all applications are applied enough to be deboxed without eta expansion *)
Fixpoint is_expanded_aux (nargs : nat) (t : term) : bool :=
  match t with
  | tBox => true
  | tRel _ => true
  | tVar _ => true
  | tEvar _ ts => forallb (is_expanded_aux 0) ts
  | tLambda _ body => is_expanded_aux 0 body
  | tLetIn _ val body => is_expanded_aux 0 val && is_expanded_aux 0 body
  | tApp hd arg => is_expanded_aux 0 arg && is_expanded_aux (S nargs) hd
  | tConst kn => #|get_const_mask kn| <=? nargs
  | tConstruct ind c => #|get_ctor_mask ind c| <=? nargs
  | tCase _ discr brs => is_expanded_aux 0 discr && forallb (is_expanded_aux 0 ∘ snd) brs
  | tProj _ t => is_expanded_aux 0 t
  | tFix defs _
  | tCoFix defs _ => forallb (is_expanded_aux 0 ∘ dbody) defs
  end.

(* Check if all applications are applied enough to be deboxed without eta expansion *)
Definition is_expanded (t : term) : bool :=
  is_expanded_aux 0 t.

(* Like above, but check all bodies in environment. This assumption does not necessarily hold,
   but we should try to make it hold by eta expansion before quoting *)
Definition is_expanded_env (Σ : global_env) : bool :=
  forallb (fun '(kn, decl) =>
             match decl with
             | ConstantDecl {| cst_body := Some body |} => is_expanded body
             | _ => true
             end) Σ.

Lemma has_use_lift_other k k' n t :
  k < k' ->
  has_use k (lift n k' t) = has_use k t.
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
    now rewrite H, IHForall.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - easy.
  - easy.
  - rewrite IHt by easy.
    f_equal.
    induction X; [easy|].
    cbn.
    now rewrite p0, IHX.
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

Lemma has_use_lift_all k k' n t :
  k <= k' ->
  k' < n + k ->
  has_use k' (lift n k t) = false.
Proof.
  intros l1 l2.
  induction t using term_forall_list_ind in t, n, k, k', l1, l2 |- *; cbn in *; auto.
  - destruct (_ <=? _) eqn:?; cbn; propify; lia.
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

Lemma has_use_subst_other k k' s t :
  k < k' ->
  has_use k (subst s k' t) = has_use k t.
Proof.
  intros lt.
  induction t in t, k, k', lt |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _) eqn:?, (_ =? _) eqn:?; propify; subst.
    + lia.
    + destruct (nth_error _ _) eqn:nth.
      * now apply has_use_lift_all.
      * cbn.
        destruct (_ =? _) eqn:?; propify; [|easy].
        apply nth_error_None in nth.
        lia.
    + cbn.
      now rewrite Nat.eqb_refl.
    + cbn.
      propify.
      lia.
  - induction H; [easy|].
    cbn in *.
    now rewrite H.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
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

Lemma valid_branch_mask_lift mask n k t :
  valid_branch_mask mask t ->
  valid_branch_mask mask (lift n k t).
Proof.
  intros valid.
  induction mask as [|b mask IH] in mask, n, k, t, valid |- *.
  - cbn in *.
    now destruct ?.
  - cbn in *.
    destruct t; try contradiction.
    cbn in *.
    split; [|now apply IH].
    destruct b; [|easy].
    now rewrite has_use_lift_other.
Qed.

Lemma valid_branch_mask_subst mask s k t :
  valid_branch_mask mask t ->
  valid_branch_mask mask (subst s k t).
Proof.
  intros valid.
  induction mask as [|b mask IH] in mask, s, k, t, valid |- *.
  - cbn in *.
    now destruct ?.
  - cbn in *.
    destruct t; try contradiction.
    cbn in *.
    split; [|now apply IH].
    destruct b; [|easy].
    now erewrite has_use_subst_other.
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
  is_expanded_aux k t ->
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
  is_expanded t ->
  dearg_aux args t = mkApps (dearg t) args.
Proof. apply dearg_expanded_aux. Qed.

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

Lemma has_use_mkApps k t args :
  has_use k (mkApps t args) =
  has_use k t || existsb (has_use k) args.
Proof.
  induction args using List.rev_ind; cbn in *.
  - now rewrite Bool.orb_false_r.
  - rewrite mkApps_app, existsb_app.
    cbn.
    rewrite IHargs.
    now rewrite Bool.orb_false_r, Bool.orb_assoc.
Qed.

Lemma Forall_existsb_false {A} (p : A -> bool) (l : list A) :
  Forall (fun a => p a = false) l ->
  existsb p l = false.
Proof.
  induction 1; [easy|].
  cbn in *.
  now rewrite H, IHForall.
Qed.

Lemma has_use_lift k k' n t :
  k' <= k ->
  n + k' <= k ->
  has_use k (lift n k' t) = has_use (k - n) t.
Proof.
  intros l1 l2.
  induction t in k, k', n, t, l1, l2 |- * using term_forall_list_ind; cbn in *; auto.
  - repeat
      (try destruct (_ <=? _) eqn:?; propify;
       try destruct (_ =? _) eqn:?; propify;
       cbn in *);
       lia.
  - induction H; [easy|].
    cbn in *.
    now rewrite H.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - rewrite IHt by easy.
    f_equal.
    induction X; cbn in *; [easy|].
    now rewrite p0.
  - rewrite map_length.
    induction H in H, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite H by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    rewrite IHForall by easy.
    now replace (S (k - n)) with (S k - n) by lia.
  - rewrite map_length.
    induction H in H, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite H by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    rewrite IHForall by easy.
    now replace (S (k - n)) with (S k - n) by lia.
Qed.

Lemma has_use_dearg_single k mask t args :
  has_use k t = false ->
  Forall (fun t => has_use k t = false) args ->
  has_use k (dearg_single mask t args) = false.
Proof.
  intros no_use args_no_use.
  induction mask as [|[] mask IH] in k, mask, t, args, no_use, args_no_use |- *; cbn in *.
  - now rewrite has_use_mkApps, no_use, Forall_existsb_false.
  - destruct args; cbn.
    + apply IH; [|easy].
      rewrite has_use_lift by lia.
      cbn.
      now rewrite Nat.sub_0_r.
    + apply IH; [easy|].
      now inversion args_no_use.
  - destruct args; cbn.
    + apply IH; [|easy].
      cbn.
      rewrite Bool.orb_false_r.
      rewrite has_use_lift by lia.
      cbn.
      now rewrite Nat.sub_0_r.
    + inversion args_no_use.
      apply IH; [|easy].
      cbn.
      now propify.
Qed.

Lemma existsb_map {A B} (p : B -> bool) (f : A -> B) (l : list A) :
  existsb p (map f l) = existsb (fun a => p (f a)) l.
Proof.
  induction l; [easy|]; cbn in *.
  intuition.
Qed.

Ltac bia :=
  repeat (destruct (has_use _ _); cbn;
          rewrite ?Bool.orb_true_r, ?Bool.orb_false_r, ?Bool.andb_false_r; auto).

Lemma has_use_subst s k k' t :
  k' <= k ->
  has_use k (subst [s] k' t) =
  has_use (S k) t || (has_use k' t && has_use (k - k') s).
Proof.
  intros le.
  induction t in t, k, k', le |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _) eqn:?; propify; cbn.
    + destruct (nth_error _ _) eqn:nth.
      * replace n with k' in * by (now apply nth_error_Some_length in nth; cbn in * ).
        rewrite Nat.sub_diag in nth.
        cbn in *.
        noconf nth.
        rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq _ _)) by easy.
        now rewrite has_use_lift.
      * cbn.
        apply nth_error_None in nth.
        cbn in *.
        repeat (destruct (_ =? _) eqn:?; propify); auto; try lia.
    + destruct (n =? k) eqn:?, (n =? S k) eqn:?, (n =? k') eqn:?; propify; cbn in *; auto; lia.
   - induction H; [easy|].
     cbn.
     rewrite !H, !IHForall by easy.
     bia.
   - now rewrite IHt.
   - rewrite IHt1, IHt2 by easy.
     replace (S k - S k') with (k - k') by lia.
     bia.
   - rewrite IHt1, IHt2 by easy.
     bia.
   - rewrite IHt by easy.
     clear IHt.
     induction X; cbn in *; [bia|].
     rewrite p0 by easy.
     bia; cbn in *.
     + now rewrite Bool.orb_false_r in IHX.
     + now rewrite Bool.andb_false_r, Bool.orb_false_r in IHX.
   - rewrite map_length.
     induction H in H, m, k, k', le |- *; cbn in *; [easy|].
     rewrite H by easy.
     specialize (IHForall (S k) (S k') ltac:(lia)).
     rewrite !Nat.sub_succ in *.
     replace (#|l| + k - (#|l| + k')) with (k - k') by lia.
     rewrite <- !Nat.add_succ_r.
     rewrite IHForall.
     bia.
   - rewrite map_length.
     induction H in H, m, k, k', le |- *; cbn in *; [easy|].
     rewrite H by easy.
     specialize (IHForall (S k) (S k') ltac:(lia)).
     rewrite !Nat.sub_succ in *.
     replace (#|l| + k - (#|l| + k')) with (k - k') by lia.
     rewrite <- !Nat.add_succ_r.
     rewrite IHForall.
     bia.
Qed.

Lemma has_use_dearg_lambdas k mask ar t :
  has_use k (dearg_lambdas mask ar t).2 = has_use k t.
Proof.
  induction mask as [|[] mask IH] in mask, k, ar, t |- *; cbn.
  - easy.
  - destruct t; try reflexivity.
    cbn in *.
    rewrite IH.
    unfold subst1.
    rewrite has_use_subst by easy.
    cbn.
    now rewrite Bool.andb_false_r, Bool.orb_false_r.
  - destruct t; try reflexivity.
    destruct (dearg_lambdas mask ar t) eqn:dearg.
    cbn.
    replace t0 with (dearg_lambdas mask ar t).2.
    + now rewrite IH.
    + destruct (dearg_lambdas _ _ _); cbn; congruence.
Qed.

Lemma has_use_dearg_case k ind npars discr brs :
  has_use k (dearg_case ind npars discr brs) =
  has_use k discr || existsb (has_use k) (map snd brs).
Proof.
  unfold dearg_case.
  destruct (get_mib_masks _); cbn; [|now rewrite existsb_map].
  f_equal.
  unfold mapi.
  generalize 0.
  induction brs; intros; [easy|].
  cbn in *.
  rewrite IHbrs.
  f_equal.
  destruct (find _ _); [|easy].
  destruct p as ((? & ?) & ?).
  now rewrite has_use_dearg_lambdas.
Qed.

Lemma has_use_dearg_aux k t args :
  has_use k t = false ->
  Forall (fun t => has_use k t = false) args ->
  has_use k (dearg_aux args t) = false.
Proof.
  intros no_use args_no_use.
  induction t using term_forall_list_ind in k, t, args, no_use, args_no_use |- *;
    cbn in *; rewrite ?has_use_mkApps; cbn.
  - now apply Forall_existsb_false.
  - now rewrite no_use; apply Forall_existsb_false.
  - now apply Forall_existsb_false.
  - propify; split; [|now apply Forall_existsb_false].
    induction H; [easy|]; cbn in *; propify.
    now rewrite H, IHForall.
  - now rewrite Forall_existsb_false, Bool.orb_false_r, IHt.
  - rewrite Forall_existsb_false, Bool.orb_false_r by easy.
    propify.
    now split; [apply IHt1|apply IHt2].
  - propify.
    now rewrite IHt1.
  - now apply has_use_dearg_single.
  - now apply has_use_dearg_single.
  - destruct p.
    rewrite has_use_mkApps.
    rewrite Forall_existsb_false, Bool.orb_false_r by easy.
    rewrite has_use_dearg_case.
    propify.
    split; [now apply IHt|].
    induction X; [easy|]; cbn in *; propify.
    rewrite p by easy.
    split; [easy|].
    now apply IHX.
  - now rewrite IHt, Forall_existsb_false.
  - rewrite map_length.
    propify; split; [|now apply Forall_existsb_false].
    induction H in k, m, H, no_use |- *; [easy|].
    cbn in *; propify.
    rewrite <- !Nat.add_succ_r in *.
    rewrite H by easy.
    split; [easy|].
    now apply IHForall.
  - rewrite map_length.
    propify; split; [|now apply Forall_existsb_false].
    induction H in k, m, H, no_use |- *; [easy|].
    cbn in *; propify.
    rewrite <- !Nat.add_succ_r in *.
    rewrite H by easy.
    split; [easy|].
    now apply IHForall.
Qed.

Lemma valid_branch_mask_dearg mask t :
  valid_branch_mask mask t ->
  valid_branch_mask mask (dearg t).
Proof.
  intros valid.
  induction mask as [|b mask IH] in mask, t, valid |- *; cbn in *.
  - now destruct ?.
  - destruct t; try contradiction.
    cbn in *.
    split; [|easy].
    destruct b; [|easy].
    now apply has_use_dearg_aux.
Qed.

Lemma valid_branch_dearg mm ind c br :
  valid_branch mm ind c br ->
  valid_branch mm ind c (dearg br).
Proof.
  intros valid.
  unfold valid_branch in *.
  destruct (find _ _) as [((? & ?) & ?)|]; [|easy].
  now apply valid_branch_mask_dearg.
Qed.

Lemma Alli_map {A B} (P : nat -> B -> Type) n (f : A -> B) (l : list A) :
  Alli (fun n a => P n (f a)) n l ->
  Alli P n (map f l).
Proof. now induction 1; cbn; constructor. Qed.

Lemma valid_case_masks_dearg_branches ind npars brs :
  valid_case_masks ind npars brs ->
  valid_case_masks ind npars (map (on_snd dearg) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  destruct valid as (? & [?]).
  split; [easy|].
  constructor.
  apply Alli_map.
  cbn.
  eapply Alli_impl; [eassumption|].
  cbn.
  intros n [].
  intros valid.
  now apply valid_branch_dearg.
Qed.

Lemma dearg_aux_subst s k t args :
  valid_cases t ->
  Forall (fun s => is_expanded s) s ->
  dearg_aux (map (subst (map dearg s) k ∘ dearg) args) (subst s k t) =
  subst (map dearg s) k (dearg_aux (map dearg args) t).
Proof.
  intros vcases es.
  induction t using term_forall_list_ind in s, k, t, args, vcases, es |- *; cbn in *; refold'.
  - now rewrite subst_mkApps, map_map.
  - rewrite subst_mkApps, map_map.
    cbn in *.
    destruct (_ <=? _) eqn:?; propify; [|easy].
    rewrite nth_error_map.
    destruct (nth_error _ _) eqn:nth; cbn.
    + rewrite dearg_expanded, lift_dearg; [easy|].
      rewrite is_expanded_lift.
      now eapply nth_error_forall in nth; [|eassumption].
    + now rewrite map_length.
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
    rewrite subst_dearg_case by (now apply valid_case_masks_dearg_branches).
    rewrite map_map.
    cbn.
    f_equal.
    + now apply (IHt _ _ []).
    + destruct vcases as (_ & vcases & _).
      clear -X vcases es X.
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
Qed.

Lemma dearg_subst s k t :
  valid_cases t ->
  Forall (fun s => is_expanded s) s ->
  dearg (subst s k t) = subst (map dearg s) k (dearg t).
Proof. now intros; apply (dearg_aux_subst _ _ _ []). Qed.

Lemma dearg_subst1 s k t :
  valid_cases t ->
  is_expanded s ->
  dearg (subst [s] k t) = subst [dearg s] k (dearg t).
Proof. now intros; apply (dearg_subst [s]). Qed.

Lemma Forall_snoc {A} (P : A -> Prop) (l : list A) (a : A) :
  Forall P (l ++ [a]) ->
  Forall P l /\ P a.
Proof.
  intros all.
  apply Forall_app in all.
  intuition.
  now inversion H0.
Qed.

Lemma valid_cases_mkApps_inv hd args :
  valid_cases (mkApps hd args) ->
  valid_cases hd /\ Forall valid_cases args.
Proof.
  intros valid.
  induction args using List.rev_ind; [easy|].
  rewrite mkApps_app in *.
  cbn in *.
  intuition auto.
  apply Forall_app_inv; intuition.
Qed.

Lemma is_expanded_aux_mkApps n hd args :
  is_expanded_aux n (mkApps hd args) =
  is_expanded_aux (n + #|args|) hd && forallb is_expanded args.
Proof.
  induction args in args, n |- * using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, forallb_app.
    cbn.
    rewrite IHargs.
    rewrite app_length, Bool.andb_true_r.
    cbn in *.
    rewrite !Bool.andb_assoc.
    symmetry; rewrite Bool.andb_comm; symmetry.
    rewrite <- !Bool.andb_assoc.
    f_equal.
    f_equal.
    f_equal.
    lia.
Qed.

Lemma is_expanded_mkApps hd args :
  is_expanded (mkApps hd args) = is_expanded_aux #|args| hd && forallb is_expanded args.
Proof. now apply is_expanded_aux_mkApps. Qed.

Lemma is_expanded_aux_mkApps_true n hd args :
  is_expanded_aux (n + #|args|) hd ->
  Forall (fun a => is_expanded a) args ->
  is_expanded_aux n (mkApps hd args).
Proof.
  intros exp_hd exp_args.
  rewrite is_expanded_aux_mkApps.
  rewrite exp_hd.
  now apply forallb_Forall.
Qed.

Lemma is_expanded_aux_upwards n t n' :
  is_expanded_aux n t ->
  n <= n' ->
  is_expanded_aux n' t.
Proof.
  intros exp l.
  induction t in n, t, n', l, exp |- * using term_forall_list_ind; cbn in *; propify; easy.
Qed.

Lemma is_expanded_csubst_true s n t k :
  is_expanded_aux 0 s ->
  is_expanded_aux n t ->
  is_expanded_aux n (csubst s k t).
Proof.
  intros exps expt.
  induction t in s, n, t, k, exps, expt |- * using term_forall_list_ind; cbn in *.
  - easy.
  - destruct (Nat.compare_spec k n0) as [<-| |].
    + now eapply is_expanded_aux_upwards.
    + easy.
    + easy.
  - easy.
  - induction H; [easy|].
    cbn in *; propify.
    now rewrite H, IHForall.
  - now apply IHt.
  - now propify.
  - now propify.
  - easy.
  - easy.
  - propify.
    rewrite IHt by easy.
    split; [easy|].
    induction X; [easy|].
    cbn in *.
    propify.
    now rewrite p0, IHX.
  - easy.
  - induction H in m, H, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite H, IHForall.
  - induction H in m, H, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite H, IHForall.
Qed.

Lemma is_expanded_subst_true s n t k :
  is_expanded_aux 0 s ->
  is_expanded_aux n t ->
  is_expanded_aux n (subst [s] k t).
Proof.
  intros exps expt.
  induction t in s, n, t, k, exps, expt |- * using term_forall_list_ind; cbn in *.
  - easy.
  - destruct (_ <=? _); [|easy].
    destruct (nth_error _ _) eqn:nth; [|easy].
    destruct (_ - _); cbn in *.
    + noconf nth.
      rewrite is_expanded_aux_lift.
      now eapply is_expanded_aux_upwards.
    + now rewrite nth_error_nil in nth.
  - easy.
  - induction H; [easy|].
    cbn in *; propify.
    now rewrite H, IHForall.
  - now apply IHt.
  - now propify.
  - now propify.
  - easy.
  - easy.
  - propify.
    rewrite IHt by easy.
    split; [easy|].
    induction X; [easy|].
    cbn in *.
    propify.
    now rewrite p0, IHX.
  - easy.
  - induction H in m, H, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite H, IHForall.
  - induction H in m, H, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite H, IHForall.
Qed.

Lemma Forall_repeat {A} (P : A -> Prop) (a : A) (n : nat) :
  P a ->
  Forall P (repeat a n).
Proof.
  intros pa.
  now induction n; constructor.
Qed.

Lemma is_expanded_substl_true s n t :
  Forall (fun s => is_expanded s) s ->
  is_expanded_aux n t ->
  is_expanded_aux n (substl s t).
Proof.
  intros all exp.
  unfold substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_snoc in all.
  now apply is_expanded_csubst_true.
Qed.

Lemma is_expanded_cunfold_fix defs i narg f :
  cunfold_fix defs i = Some (narg, f) ->
  Forall (fun d => is_expanded (dbody d)) defs ->
  is_expanded f.
Proof.
  intros cuf all.
  unfold cunfold_fix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply is_expanded_substl_true; [|easy].
  unfold fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHm.
Qed.

Lemma is_expanded_cunfold_cofix defs i narg f :
  cunfold_cofix defs i = Some (narg, f) ->
  Forall (fun d => is_expanded (dbody d)) defs ->
  is_expanded f.
Proof.
  intros cuf all.
  unfold cunfold_cofix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply is_expanded_substl_true; [|easy].
  unfold cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHm.
Qed.

Lemma is_expanded_constant Σ kn cst body :
  is_expanded_env Σ ->
  ETyping.declared_constant (trans Σ) kn cst ->
  EAst.cst_body cst = Some body ->
  is_expanded body.
Proof.
  intros exp_env decl body_eq.
  unfold is_expanded_env in *.
  apply forallb_Forall in exp_env.
  eapply declared_constant_trans in decl as (? & ? & nth).
  eapply nth_error_forall in nth; [|eassumption].
  cbn in *.
  now rewrite body_eq in nth.
Qed.

Lemma eval_is_expanded_aux Σ t v k :
  trans Σ ⊢ t ▷ v ->
  is_expanded_env Σ ->
  is_expanded_aux k t ->
  is_expanded_aux k v .
Proof.
  intros ev exp_env exp_t.
  induction ev in t, v, k, ev, exp_t |- *; auto; cbn in *; propify.
  - apply IHev3.
    apply is_expanded_csubst_true; intuition auto.
    now eapply is_expanded_aux_upwards.
  - apply IHev2.
    apply is_expanded_csubst_true; intuition auto.
    now eapply is_expanded_aux_upwards.
  - apply IHev2.
    unfold ETyping.iota_red.
    specialize (IHev1 0 ltac:(easy)).
    rewrite is_expanded_aux_mkApps in *.
    propify.
    split.
    + rewrite nth_nth_error.
      destruct (nth_error _ _) eqn:nth; [|easy].
      eapply nth_error_forall in nth; [|now eapply forallb_Forall].
      now eapply is_expanded_aux_upwards.
    + now apply forallb_Forall, Forall_skipn, forallb_Forall.
  - apply IHev2.
    rewrite is_expanded_aux_mkApps.
    propify.
    split.
    + subst brs.
      cbn in *.
      now propify; eapply is_expanded_aux_upwards.
    + apply forallb_Forall.
      now apply Forall_repeat.
  - apply IHev3; clear IHev3.
    specialize (IHev1 (S k)).
    specialize (IHev2 0).
    rewrite is_expanded_aux_mkApps in *.
    cbn in *; propify.
    intuition auto.
    eapply is_expanded_aux_upwards.
    + eapply is_expanded_cunfold_fix; [eassumption|].
      now apply forallb_Forall.
    + easy.
  - easy.
  - apply IHev; clear IHev.
    rewrite is_expanded_aux_mkApps in *.
    cbn in *; propify.
    intuition auto.
    eapply is_expanded_aux_upwards.
    + eapply is_expanded_cunfold_cofix; [eassumption|].
      now apply forallb_Forall.
    + easy.
  - apply IHev; clear IHev.
    rewrite is_expanded_aux_mkApps in *.
    cbn in *; propify.
    intuition auto.
    eapply is_expanded_aux_upwards.
    + eapply is_expanded_cunfold_cofix; [eassumption|].
      now apply forallb_Forall.
    + easy.
  - apply IHev.
    eapply is_expanded_aux_upwards.
    + now eapply is_expanded_constant.
    + easy.
  - apply IHev2; clear IHev2.
    specialize (IHev1 _ exp_t).
    rewrite is_expanded_aux_mkApps in IHev1; propify.
    rewrite nth_nth_error.
    destruct (nth_error _ _) eqn:nth; [|easy].
    eapply nth_error_forall in nth; [|now apply forallb_Forall].
    now eapply is_expanded_aux_upwards.
  - easy.
Qed.

Lemma closedn_dearg_true n t :
  closedn n t = true ->
  closedn n (dearg t) = true.
Proof.
  Admitted.

Lemma valid_case_masks_lift ind c brs n k :
  valid_case_masks ind c brs ->
  valid_case_masks ind c (map (on_snd (lift n k)) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  split; [easy|].
  destruct valid as (_ & [valid]).
  constructor.
  apply Alli_map.
  eapply Alli_impl; [eassumption|].
  intros ? [] val_branch.
  cbn in *.
  unfold valid_branch in *.
  destruct (find _ _); [|easy].
  destruct p as ((? & ?) & ?).
  now apply valid_branch_mask_lift.
Qed.

Lemma valid_case_masks_subst ind c brs s k :
  valid_case_masks ind c brs ->
  valid_case_masks ind c (map (on_snd (subst s k)) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  split; [easy|].
  destruct valid as (_ & [valid]).
  constructor.
  apply Alli_map.
  eapply Alli_impl; [eassumption|].
  intros ? [] val_branch.
  cbn in *.
  unfold valid_branch in *.
  destruct (find _ _); [|easy].
  destruct p as ((? & ?) & ?).
  now apply valid_branch_mask_subst.
Qed.

Lemma valid_cases_lift t n k :
  valid_cases t ->
  valid_cases (lift n k t).
Proof.
  intros valid_t.
  induction t in t, k, valid_t |- * using term_forall_list_ind; cbn in *; auto.
  - now destruct (_ <=? _).
  - induction H; [easy|].
    now cbn in *.
  - easy.
  - easy.
  - destruct p.
    split; [easy|].
    split; [|now apply valid_case_masks_lift].
    destruct valid_t as (_ & valid & _).
    induction X; [easy|].
    now cbn in *.
  - induction H in H, k, valid_t |- *; [easy|].
    cbn in *.
    now rewrite <- !Nat.add_succ_r.
  - induction H in H, k, valid_t |- *; [easy|].
    cbn in *.
    now rewrite <- !Nat.add_succ_r.
Qed.

Lemma valid_cases_subst s k t :
  valid_cases s ->
  valid_cases t ->
  valid_cases (subst [s] k t).
Proof.
  intros valid_s valid_t.
  induction t in k, t, valid_t |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _); [|easy].
    destruct (nth_error _ _) eqn:nth; [|easy].
    destruct (_ - _); cbn in *.
    + noconf nth.
      now apply valid_cases_lift.
    + now rewrite nth_error_nil in nth.
  - induction H; [easy|].
    now cbn in *.
  - easy.
  - easy.
  - destruct p.
    split; [easy|].
    split; [|now apply valid_case_masks_subst].
    destruct valid_t as (_ & valid & _).
    induction X; [easy|].
    now cbn in *.
  - induction H in H, k, valid_t |- *; [easy|].
    cbn in *.
    now rewrite <- !Nat.add_succ_r.
  - induction H in H, k, valid_t |- *; [easy|].
    cbn in *.
    now rewrite <- !Nat.add_succ_r.
Qed.

Hint Resolve
     closedn_subst0 closed_mkApps closedn_dearg_true closed_iota_red
     is_expanded_subst_true is_expanded_aux_mkApps_true
     valid_cases_subst : dearg.
Hint Constructors Forall : dearg.

Lemma valid_cases_mkApps hd args :
  valid_cases hd ->
  Forall valid_cases args ->
  valid_cases (mkApps hd args).
Proof.
  intros valid_hd valid_args.
  induction args as [|a args IH] using List.rev_ind; [easy|].
  rewrite mkApps_app.
  cbn.
  now apply Forall_snoc in valid_args.
Qed.

Lemma valid_cases_iota_red pars c args brs :
  Forall valid_cases args ->
  Forall (fun t => valid_cases t.2) brs ->
  valid_cases (iota_red pars c args brs).
Proof.
  intros valid_args valid_brs.
  unfold iota_red.
  apply valid_cases_mkApps.
  - rewrite nth_nth_error.
    destruct (nth_error _ _) eqn:nth; [|easy].
    now eapply nth_error_forall in nth; [|eassumption].
  - now eapply Forall_skipn.
Qed.

Hint Resolve valid_cases_iota_red : dearg.

Lemma fold_right_Forall {A} (P : A -> Prop) l :
  fold_right and True (map P l) <-> Forall P l.
Proof.
  split; intros all; induction l; try easy; cbn in *.
  - now constructor.
  - now depelim all.
Qed.

Hint Resolve -> fold_right_Forall : dearg.

Lemma valid_cases_substl s t :
  Forall (fun s => closed s) s ->
  Forall valid_cases s ->
  valid_cases t ->
  valid_cases (substl s t).
Proof.
  intros clos_s valid_s valid_t.
  unfold substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_snoc in clos_s as (? & ?).
  apply Forall_snoc in valid_s as (? & ?).
  rewrite closed_subst by easy.
  now apply valid_cases_subst.
Qed.

Lemma Forall_conj {A} (P Q : A -> Prop) (l : list A) :
  (Forall P l /\ Forall Q l) <-> Forall (fun a => P a /\ Q a) l.
Proof.
  split; induction l; try easy; cbn in *.
  - intros (allp & allq).
    depelim allp.
    depelim allq.
    now constructor.
  -  intros all.
     depelim all.
     now split; constructor.
Qed.

Lemma valid_cases_cunfold_fix defs i narg f :
  cunfold_fix defs i = Some (narg, f) ->
  closed (tFix defs i) ->
  valid_cases (tFix defs i) ->
  valid_cases f.
Proof.
  intros cuf clos_defs valid_defs.
  unfold cunfold_fix in *.
  cbn in *.
  apply forallb_Forall in clos_defs.
  apply fold_right_Forall in valid_defs.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in clos_defs as ?; [|eassumption].
  eapply nth_error_forall in valid_defs as ?; [|eassumption].
  cbn in *.
  noconf cuf.
  enough (Forall (fun t => closed t /\ valid_cases t) (fix_subst defs)).
  { apply Forall_conj in H1.
    now apply valid_cases_substl. }
  unfold fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now rewrite fold_right_Forall, <- forallb_Forall.
  - now apply IHm.
Qed.

Lemma valid_cases_cunfold_cofix defs i narg f :
  cunfold_cofix defs i = Some (narg, f) ->
  closed (tCoFix defs i) ->
  valid_cases (tCoFix defs i) ->
  valid_cases f.
Proof.
  intros cuf clos_defs valid_defs.
  unfold cunfold_cofix in *.
  cbn in *.
  apply forallb_Forall in clos_defs.
  apply fold_right_Forall in valid_defs.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in clos_defs as ?; [|eassumption].
  eapply nth_error_forall in valid_defs as ?; [|eassumption].
  cbn in *.
  noconf cuf.
  enough (Forall (fun t => closed t /\ valid_cases t) (cofix_subst defs)).
  { apply Forall_conj in H1.
    now apply valid_cases_substl. }
  unfold cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now rewrite fold_right_Forall, <- forallb_Forall.
  - now apply IHm.
Qed.

Lemma valid_cases_constant Σ kn cst body :
  valid_masks_env Σ ->
  ETyping.declared_constant (trans Σ) kn cst ->
  EAst.cst_body cst = Some body ->
  valid_cases body.
Proof.
  intros valid_env decl_const body_eq.
  eapply declared_constant_trans in decl_const as (? & ? & nth).
  eapply nth_error_forall in nth; [|eassumption].
  cbn in *.
  now rewrite body_eq in nth.
Qed.

Lemma eval_valid_cases Σ t v :
  trans Σ ⊢ t ▷ v ->

  env_closed (trans Σ) ->
  closed t ->

  valid_masks_env Σ ->
  valid_cases t ->

  valid_cases v.
Proof with auto with dearg.
  intros ev clos_env clos_t valid_env valid_t.
  induction ev in t, v, ev, clos_t, valid_t |- *; auto; cbn in *; propify.
  - easy.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply eval_closed in ev2 as ?...
    rewrite closed_subst in * by easy.
    apply IHev3...
    apply closedn_subst0...
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    rewrite closed_subst in * by easy.
    apply IHev2; auto with dearg.
    apply closedn_subst0...
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    apply closed_mkApps_inv in H2 as (? & ?).
    assert (closed (iota_red pars c args brs)).
    { apply closed_iota_red; auto.
      now apply forallb_Forall. }
    eapply eval_closed in ev2 as ?...
    eapply valid_cases_mkApps_inv in H5 as (? & ?).
    apply IHev2...
  - subst brs.
    cbn in *.
    propify.
    intuition auto.
    apply IHev2.
    + apply closed_mkApps...
      now apply Forall_repeat.
    + apply valid_cases_mkApps...
      now apply Forall_repeat.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply eval_closed in ev2 as ?...
    apply closed_mkApps_inv in H6 as (? & ?).
    apply valid_cases_mkApps_inv in H5 as (? & ?).
    apply H4...
    + apply closed_mkApps...
      now eapply closed_cunfold_fix.
    + split; [|easy].
      apply valid_cases_mkApps...
      eapply valid_cases_cunfold_fix; [eassumption| |]...
  - easy.
  - destruct ip.
    intuition auto.
    apply closed_mkApps_inv in H as (? & ?).
    apply valid_cases_mkApps_inv in H1 as (? & ?).
    assert (closed fn) by (now eapply closed_cunfold_cofix).
    assert (closed (mkApps fn args)) by (now apply closed_mkApps).
    eapply eval_closed in ev as ?...
    + apply H2...
      intuition auto...
      apply valid_cases_mkApps...
      now eapply valid_cases_cunfold_cofix.
    + now cbn; propify.
  - apply closed_mkApps_inv in clos_t as (? & ?).
    apply valid_cases_mkApps_inv in valid_t as (? & ?).
    assert (closed fn) by (now eapply closed_cunfold_cofix).
    apply IHev.
    + now apply closed_mkApps.
    + apply valid_cases_mkApps...
      now eapply valid_cases_cunfold_cofix.
  - apply IHev.
    + now eapply closed_constant.
    + now eapply valid_cases_constant.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply closed_mkApps_inv in H as (? & ?).
    eapply valid_cases_mkApps_inv in H0 as (? & ?).
    rewrite (nth_nth_error (pars + arg) args tDummy) in *.
    destruct (nth_error _ _) eqn:nth; [|now apply IHev2].
    eapply nth_error_forall in H1; [|eassumption].
    eapply nth_error_forall in H2; [|eassumption].
    now apply IHev2.
  - easy.
Qed.

Ltac transfer_elim :=
  match goal with
  | [clos_hd : is_true (closed (mkApps ?f (firstn ?n ?l))),
     clos_args : Forall (fun t => is_true (closed t)) (skipn ?n ?l),
     valid_hd : valid_cases (mkApps ?f (firstn ?n ?l)),
     valid_args : Forall valid_cases (skipn ?n ?l),
     exp_hd : is_true (is_expanded_aux #|skipn ?n ?l| (mkApps ?f (firstn ?n ?l))),
     exp_args : Forall (fun a => is_true (is_expanded a)) (skipn ?n ?l) |- _] =>
    apply closed_mkApps_inv in clos_hd as (clos_hd & clos_args');
    eapply Forall_app_inv in clos_args; [|exact clos_args'];

    apply valid_cases_mkApps_inv in valid_hd as (valid_hd & valid_args');
    eapply Forall_app_inv in valid_args; [|exact valid_args'];

    rewrite is_expanded_aux_mkApps, Nat.add_comm, <- app_length, firstn_skipn in exp_hd;
    apply Bool.andb_true_iff in exp_hd as (exp_hd & exp_args');
    apply forallb_Forall in exp_args';
    eapply Forall_app_inv in exp_args; [|exact exp_args'];

    rewrite firstn_skipn in clos_args, valid_args, exp_args;

    clear clos_args' valid_args' exp_args'
  end.

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
  | eval_proj _ _ _ _ _ _ _ ev1 ev2
  | eval_app_cong _ _ _ _ ev1 _ ev2 => S (deriv_length ev1 + deriv_length ev2)
  | eval_beta _ _ _ _ _ _ ev1 ev2 ev3
  | eval_fix _ _ _ _ _ _ _ _ _ ev1 ev2 _ _ _ ev3 =>
    S (deriv_length ev1 + deriv_length ev2 + deriv_length ev3)
  end.

Lemma deriv_length_min {Σ t v} (ev : Σ ⊢ t ▷ v) :
  1 <= deriv_length ev.
Proof. destruct ev; cbn in *; lia. Qed.

Lemma declared_constant_dearg Σ k cst :
  ETyping.declared_constant (trans Σ) k cst ->
  exists cst',
    ETyping.declared_constant (trans (dearg_env Σ)) k cst' /\
    EAst.cst_body cst' = option_map (dearg ∘ dearg_cst_body_top (get_const_mask k))
                                    (EAst.cst_body cst).
Proof.
  unfold ETyping.declared_constant.
  intros typ.
  induction Σ as [|(kn, decl) Σ IH]; [easy|].
  cbn in *.
  destruct decl; cbn in *.
  - destruct (kername_eq_dec k kn) as [->|].
    + noconf typ.
      eexists.
      now split; [reflexivity|].
    + now apply IH.
  - now apply IH.
Qed.

Inductive dearg_spec : term -> term -> Type :=
| dearg_spec_const kn args :
    dearg_spec (mkApps (tConst kn) args)
               (dearg_single (get_const_mask kn) (tConst kn) (map dearg args))
| dearg_spec_ctor ind c args :
    dearg_spec (mkApps (tConstruct ind c) args)
               (dearg_single (get_ctor_mask ind c) (tConstruct ind c) (map dearg args))
| dearg_spec_case ind npars discr brs args :
    dearg_spec (mkApps (tCase (ind, npars) discr brs) args)
               (mkApps (dearg_case ind npars (dearg discr) (map (on_snd dearg) brs))
                       (map dearg args))
| dearg_spec_other hd args :
    match hd with
    | tConst _
    | tConstruct _ _
    | tCase _ _ _
    | tApp _ _ => False
    | _ => True
    end ->
    dearg_spec (mkApps hd args) (mkApps (map_subterms dearg hd) (map dearg args)).

Lemma dearg_elim t :
  dearg_spec t (dearg t).
Proof.
  destruct (mkApps_elim t []).
  generalize (firstn n l) as args.
  clear n.
  intros args.
  rewrite dearg_mkApps.
  destruct f; try solve [now econstructor].
  - easy.
  - cbn in *.
    destruct p.
    eapply dearg_spec_case.
Qed.

Lemma dearg_dearg_cst_body_top mask t :
  dearg (dearg_cst_body_top mask t) = dearg_cst_body_top mask (dearg t).
Proof.
  Admitted.

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

(*
Lemma All2_split
      {A B}
      {T : A -> B -> Type}
      {la lb la' lb'}
      (a : All2 T (la ++ la') (lb ++ lb')) :
  exists (l : All2 T la lb) (r : All2 T la' lb'),
    a = app_All2 l r.
Proof.
  exists
    (fix
  depind a.
  -*)

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

Section dearg.
  Context (n : nat).
  Context (Σ : global_env).
  Context (IH : forall t v : term,
        closed t ->
        valid_cases t ->
        is_expanded t ->
        forall ev : trans Σ ⊢ t ▷ v,
        deriv_length ev <= n ->
        exists ev' : trans (dearg_env Σ) ⊢ dearg t ▷ dearg v,
          deriv_length ev' <= deriv_length ev).

  Lemma dearg_single_construct mask ind c args argsv
        (ev_args : All2 (eval (trans Σ)) args argsv) :
    #|mask| <= #|args| ->
    sum_deriv_lengths ev_args <= n ->
    exists (ev :
              trans (dearg_env Σ) ⊢ dearg_single mask (tConstruct ind c) (map dearg args)
                    ▷ dearg_single mask (tConstruct ind c) (map dearg argsv)),
      deriv_length ev <= S (#|args| + sum_deriv_lengths ev_args).
  Proof.
    (*
    intros mask_len deriv_len.
    induction args in mask, args, argsv, ev_args, mask_len, deriv_len |- * using List.rev_ind; cbn in *.
    - destruct mask; [|easy].
      cbn in *.
      depelim ev_args.
      unshelve eexists _; [now constructor|cbn].
      lia.
    - destruct argsv as [|? ? _] using List.rev_ind.
      { apply All2_length in ev_args as contra.
        rewrite app_length in contra.
        now cbn in *. }
      rewrite app_length in *; cbn in *.
      apply All2_app_r in ev_args as ?.
      destruct H as (ev_args_hd & ev_x).
      assert (sum_deriv_lengths ev_args_hd + deriv_length ev_x <= n) by admit.
      rewrite !map_app, !dearg_single_app.
      rewrite !map_length, <- (All2_length _ _ ev_args_hd).
      destruct (Nat.leb_spec #|mask| #|args|).
      + rewrite firstn_all2, skipn_all2 by easy.
        cbn.
        destruct (IHargs _ argsv ev_args_hd H0); [lia|].
        unshelve epose proof (IH _ _ _ _ _ ev_x _) as (ev_dearg_x & deriv_dearg_x).
        * admit.
        * admit.
        * admit.
        * lia.
        * unshelve eexists _.
          -- eapply eval_app_cong.
             ++ exact x1.
             ++ admit.
             ++ exact ev_dearg_x.
          -- cbn in *.
             lia.
          -- exact x1.
          -- admit.
          -- exact
      destruct mask.
      + cbn in *.
        admit.
      + cbn in *.
    induction ev_args in mask, args, argsv, ev_args, exp, len |- *; cbn in *.
    - destruct mask; [|easy].
      cbn.
      unshelve eexists _.
      + now constructor.
      + easy.
    - destruct mask.
      + cbn in *. *)
    Admitted.
End dearg.

Lemma dearg_correct Σ t v :
  env_closed (trans Σ) ->
  closed t ->

  valid_masks_env Σ ->
  valid_cases t ->

  is_expanded_env Σ ->
  is_expanded t ->

  ∥trans Σ ⊢ t ▷ v∥ ->
  ∥trans (dearg_env Σ) ⊢ dearg t ▷ dearg v∥.
Proof.
  intros clos_env clos_t valid_env valid_t exp_env exp_t.
  enough (forall n (ev : trans Σ ⊢ t ▷ v),
             deriv_length ev <= n ->
             exists (ev' : trans (dearg_env Σ) ⊢ dearg t ▷ dearg v),
               deriv_length ev' <= deriv_length ev).
  { intros ev.
    destruct ev as [ev].
    edestruct (H _ ev (le_refl _)).
    now constructor. }
  induction n in t, v, clos_t, valid_t, exp_t |- *; [admit|].
  intros ev len.
  destruct (dearg_elim t).
  - rewrite is_expanded_mkApps in exp_t.
    cbn in *; propify.
    eapply eval_mkApps_head in ev as ev_const.
    destruct ev_const as (constv & ev_const).
    depelim ev_const; [|easy].
    eapply declared_constant_dearg in isdecl as isdecl_dearg.
    destruct isdecl_dearg as (cst_dearg & decl_dearg & body_dearg).
    rewrite e in body_dearg.
    cbn in *.
    admit.
  - rewrite is_expanded_mkApps in exp_t.
    cbn in *; propify.
    induction args in v, args, clos_t, valid_t, exp_t, ev, len |- * using List.rev_ind; cbn in *.
    + depelim ev.
      cbn in *.
      destruct (get_ctor_mask ind c); [|easy].
      cbn in *.
      unshelve eexists _; [now constructor|easy].
    + rewrite app_length in *; cbn in *.
      revert ev len.
      rewrite mkApps_app.
      cbn.
      intros ev len.
      rewrite map_app, dearg_single_app, map_length.
      specialize (eval_tApp_deriv ev) as (constrv & ev_constr & xv & ev_x & ev_app_len).
      revert ev len ev_app_len.
      replace v with (tApp constrv xv) by admit.
      intros ev len ev_app_len.
      destruct (Nat.leb_spec #|get_ctor_mask ind c| #|args|).
      * rewrite firstn_all2, skipn_all2 by easy.
        cbn.
        unshelve epose proof (IHargs v _ _ _ ev_constrv
      apply All2_app_r in ev_args as ?.
      destruct H as (ev_args_hd & ev_x).
      assert (sum_deriv_lengths ev_args_hd + deriv_length ev_x <= n) by admit.
      rewrite !map_app, !dearg_single_app.
      rewrite !map_length, <- (All2_length _ _ ev_args_hd).
      destruct (Nat.leb_spec #|mask| #|args|).
      + rewrite firstn_all2, skipn_all2 by easy.
        cbn.
        destruct (IHargs _ argsv ev_args_hd H0); [lia|].
        unshelve epose proof (IH _ _ _ _ _ ev_x _) as (ev_dearg_x & deriv_dearg_x).
        * admit.
        * admit.
        * admit.
        * lia.
        * unshelve eexists _.
          -- eapply eval_app_cong.
             ++ exact x1.
             ++ admit.
             ++ exact ev_dearg_x.
          -- cbn in *.
             lia.

    specialize (eval_mkApps_deriv ev) as (? & ? & argsv & ev_args & ?).
    pose proof (deriv_length_min x0).
    pose proof (dearg_single_construct _ _ IHn _ ind c _ _ ev_args (proj1 exp_t)).
    cbn in *.
    cbn in *.
    apply (dearg_single_construct (S n)).
    induction ev_args; cbn in *.
    + propify.
      depelim ev.
      cbn.
      destruct (get_ctor_mask _ _); [|easy].
      cbn.
      now constructor; constructor.
    +
      depelim ev.
      cbn in *.
    eapply eval_dearg_single_heads.
    + now rewrite map_length.
    + econstructor; eauto.
      unshelve eapply (IHn _ _ _ _ _ _ _).
      * shelve.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
    + admit.
    + admit.
  -
      rewrite dearg_dearg_cst_body_top.
    admit.
  - admit.
  - admit.
  -
  - replace v with (mkApps (tConstruct ind c) args); cycle 1.
    { eapply eval_deterministic; [|eassumption].
      clear.
      induction args using List.rev_ind.
      - now eapply eval_atom.
      - rewrite mkApps_app.
        cbn.
        eapply eval_app_cong.
        3: {
  set (args := firstn n0 l) in *; clearbody args.
  rename f into hd.
  rewrite dearg_mkApps.
  destruct hd; cbn in *.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - easy.
  - rewrite is_expanded_mkApps in exp_t.
    eapply eval_mkApps_head in ev as ?.
    destruct H as (hdv & ev_hd).
    depelim ev_hd; [|easy].
    eapply declared_constant_dearg in isdecl as decl_cst_dearg.
    destruct decl_cst_dearg as (cst' & decl_dearg & dearg_body).
    rewrite H in dearg_body.
    cbn in *.
    assert (exists h, trans (dearg_env Σ) ⊢ tConst k ▷ h /\
                      trans (dearg_env Σ) ⊢ dearg_cst_body_top (get_const_mask k) (dearg body)
                            ▷ h).
    { admit. }
    destruct H0 as (cstv & ev_const & ev_inner).
    eapply eval_dearg_single_heads; [|exact ev_inner|eassumption|].
    + rewrite map_length.
      now propify.
    + apply dearg_single_correct.
      * admit.
      * admit.
      * admit.
      * admit.
      * rewrite map_length.
        now propify.
      *
        replace (mkApps (dearg body) (map dearg args)) with (dearg (mkApps body args)) by admit.
        unshelve eapply (IHn (mkApps body args) v _ _ _ _ _).
        -- admit.
        -- admit.
        -- admit.
        -- eapply eval_mkApps_heads.
           2: eassumption.
           2: exact ev.
           econstructor; eauto.
        --
    unshelve epose proof (IHn _ _ _ _ _ ev_hd _).
    + now eapply closed_constant; eauto.
    + now eapply valid_cases_constant; eauto.
    + now eapply is_expanded_constant; eauto.
    + admit.
    + eapply eval_dearg_single_heads.
      4: {
        eapply dearg_single_correct.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        -
    assert (trans (dearg_env Σ) ⊢ tConst k ▷ dearg (dearg_cst_body_top (get_const_mask k) body)).
    { econstructor; eauto.
      cbn.
      eapply IHn.
      - admit.
      - admit.
      - admit.
      - admit.
    eapply (eval_dearg_single_heads _ (
    1: { rewrite map_length.
         cbn in *.
         now propify. }
    2: { depelim ev_hd; [|easy].
         eapply declared_constant_dearg in isdecl as (cst' & decl_dearg & dearg_body).
         econstructor.
         - eassumption.
         - rewrite H in dearg_body.
           cbn in *.
           eassumption.
         - unshelve eapply (IHn body hdv).
           + admit.
           + admit.
           + admit.
           + admit.
           + admit.
    3: {
      econstructor.
    + admit.
    +
    2: econstructor.

Lemma foo :
  trans Σ ⊢ mkApps hd args ▷ v ->
  trans Σ ⊢ mkApps hd (map dearg args) ▷ dearg v
  -


Lemma dearg_correct Σ hd args v :
  env_closed (trans Σ) ->
  closed hd ->
  Forall (closedn 0) args ->

  valid_masks_env Σ ->
  valid_cases hd ->
  Forall valid_cases args ->

  is_expanded_env Σ ->
  is_expanded_aux #|args| hd ->
  Forall (fun a => is_expanded a) args ->

  trans Σ ⊢ mkApps hd args ▷ v ->

  trans (dearg_env Σ) ⊢ dearg_aux (map dearg args) hd ▷ dearg v.
Proof with auto using dearg.
  intros
    clos_env clos_hd clos_args
    valid_env valid_hd valid_args
    exp_env exp_hd exp_args ev.
  remember (mkApps hd args) as t eqn:eq.
  induction ev in hd, args, v,
                  clos_hd, clos_args,
                  valid_hd, valid_args,
                  exp_hd, exp_args,
                  t, eq, ev |- *.
  - destruct (mkApps_elim hd args); transfer_elim.
    destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite dearg_aux_mkApps, <- map_app, firstn_skipn.
    rewrite mkApps_app in *.
    cbn in *.
    noconf eq.
    apply Forall_snoc in clos_args as (clos_l & clos_t).
    apply Forall_snoc in valid_args as (valid_l & valid_t).
    apply Forall_snoc in exp_args as (exp_l & exp_t).
    rewrite map_app.
    specialize (IHev1 f l).
    specialize (IHev2 x []).
    destruct f;
      cbn in *;
      rewrite ?mkApps_app;
      cbn in *;
      try solve [econstructor; [apply IHev1; auto|apply IHev2; auto]].
    + easy.
    +
      eapply dearg_single_correct in ev1.
      rewrite dearg_single_app.
      rewrite map_length in *.
      apply dearg_single_mask_length in IHev1; auto.
      * admit.
      * propify.

      rewrite firstn_all2.
      econstructor.
      * apply (IHev1 tBox l); auto.
      * apply (IHev2 x []); auto.
    +
      eapply eval_box_apps.
    unshelve epose proof (IHev1 _ _ _ _ _ _ _ _ _ _ _ _ eq_refl) as IHev1; auto.
    admit.
    unshelve epose proof (IHev2 _ [] _ _ _ _ _ _ _ _ _ _ eq_refl) as IHev2; auto.
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
*)
  - destruct (mkApps_elim hd args); transfer_elim.
    destruct l as [|? ? _] using List.rev_ind; cbn in *; [now subst|].
    rewrite dearg_aux_mkApps, <- map_app, firstn_skipn, map_app.
    rewrite mkApps_app in *.
    cbn in *.
    noconf eq.
    apply Forall_snoc in clos_args as (clos_l & clos_t).
    apply Forall_snoc in valid_args as (valid_l & valid_t).
    apply Forall_snoc in exp_args as (exp_l & exp_t).
    assert (closed a') by (eapply eval_closed; eauto).
    assert (valid_cases a') by (eapply eval_valid_cases; eauto).
    assert (is_expanded a') by (eapply eval_is_expanded_aux; eauto).
    rewrite (closed_subst a' 0 b) in * by assumption.
    destruct f0; cbn in *.
    + admit.
    + admit.
    + admit.
    + admit.
    + rewrite ?mkApps_app.
      cbn in *.
      econstructor.
      * specialize (IHev1 (tLambda n0 f0) l).
        now apply IHev1.
      * specialize (IHev2 x []).
        now apply IHev2.
      * specialize (IHev3 (subst0 [a'] b) []).
        rewrite closed_subst by eauto with dearg.
        cbn in *; refold'.
        rewrite dearg_subst in IHev3.
        -- apply IHev3...
           ++ apply closedn_subst0...
              eapply eval_closed in ev1; eauto with dearg.
           ++ apply valid_cases_subst...
              eapply eval_valid_cases in ev1; eauto with dearg.
              eapply valid_cases_mkApps...
           ++ apply is_expanded_subst_true.
              ** now eapply eval_is_expanded_aux in ev2.
              ** eapply (eval_is_expanded_aux _ _ _ 0) in ev1; auto with dearg.
        -- eapply eval_valid_cases in ev1; eauto with dearg.
           eapply valid_cases_mkApps...
        -- constructor; [|easy].
           now eapply eval_is_expanded_aux in ev2.
    +
              eapply is_expanded_aux
        rewrite
        apply IHev3.
        eapply (IHev2 _ [] _ _ _ _ _ _ _ _ _ _ eq_refl).
      *
        specialize (IHev3 (subst0 [a'] b) []).
        cbn in *; refold'.
        rewrite dearg_subst in IHev3; eauto with dearg.
        -- eapply (IHev3 _ _ _ _ _ _ _ _ _ _ eq_refl).
        -- eapply closedn_subst0; eauto with dearg.
           eapply eval_closed in ev1; eauto with dearg.
        -- admit.
        -- apply is_expanded_subst_true.
           eauto with dearg.
    +
        auto.
        eapply (IHev3 _ [] _ _ _ _ _ _ _ _ _ _ eq_refl).
        unshelve epose proof () as IHev3.
        10: {
          cbn in *; refold'.
          rewrite dearg_subst in IHev3.
          apply IHev3.
        10: apply IHev3.
        apply IHev2.
        cbn in *.
        apply IHev1.
    admit.
    unshelve epose proof (IHev2 _ [] _ _ _ _ _ _ _ _ _ _ eq_refl) as IHev2; auto.
    unshelve epose proof (IHev3 _ [] _ _ _ _ _ _ _ _ _ _ eq_refl) as IHev3; auto.
    { apply closedn_subst0.
      - constructor; [eauto with closed|constructor].
      - eapply eval_closed in ev1; cbn in *; eauto.
        eapply closed_mkApps; eauto. }
    { admit. }
    { admit. }
    cbn in *; refold'.
    rewrite dearg_subst in IHev3; cycle 1.
    admit.
    constructor; [|auto].
    admit.
    cbn in *.
    destruct f0; cbn in *.
    + rewrite ?mkApps_app.
      cbn in *.
      econstructor.
      eassumption.
      eassumption.
      rewrite closed_subst; [easy|].
      apply closed_dearg_aux.
    rewrite dearg_subst0
    specialize (IHev1 _ _ _ clos_Σ clos_hd clos_l masks expanded eq_refl).
    specialize (IHev2 _ [] _ clos_Σ clos_a ltac:masks expanded clos_a ltac:(auto) eq_refl).
    unshelve epose proof (IHev3 _ [] _ masks expanded _ ltac:(auto) eq_refl).
    { eapply eval_closed in ev1.
    speciali
    specialize (IHev1 _ _ _ masks expanded eq_refl).
    specialize (IHev2 _ [] _ masks expanded eq_refl).
    specialize (IHev3 _ [] _ masks expanded eq_refl).
    cbn in *; refold'.
    destruct f0; cbn in *.
