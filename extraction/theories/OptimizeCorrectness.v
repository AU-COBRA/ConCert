From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Psatz.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.
Set Equations Transparent.

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

Local Notation "Σ ⊢ s ▷ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma eval_only_constants Σ s t :
  Σ ⊢ s ▷ t ->
  only_constants Σ ⊢ s ▷ t.
Proof.
  induction 1 using eval_evals_ind;
    eauto using eval, declared_constant_only_constants.
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

(*
Section eta_correctness.
Context (ctors : list (inductive * nat * nat)).
Context (consts : list (kername * nat)).

Notation eta_ctor := (eta_ctor ctors).
Notation eta_const := (eta_const consts).
Notation eta_expand_aux := (eta_expand_aux ctors consts).
Notation eta_expand := (eta_expand ctors consts).

Open Scope type.

Lemma wfe_term_eta_single Σ t args n :
  wfe_term Σ t ->
  Forall (wfe_term Σ) args ->
  wfe_term Σ (eta_single t args n).
Proof.
  intros wft wfall.
  unfold eta_single.
  induction (_ - _) at 3; [|easy].
  cbn in *.
  apply wfe_term_mkApps; [easy|].
  apply Forall_app_inv.
  - clear -wfall.
    generalize args at 1; intros.
    induction wfall; cbn in *; [easy|].
    constructor; [|easy].
    now apply wfe_term_lift.
  - clear.
    induction (seq _ _); [cbn; easy|].
    rewrite rev_map_cons.
    apply Forall_app_inv; [easy|].
    constructor; easy.
Qed.

Lemma wfe_term_eta_ctor Σ ind i args :
  wfe_term Σ (tConstruct ind i) ->
  Forall (wfe_term Σ) args ->
  wfe_term Σ (eta_ctor ind i args).
Proof.
  intros wft wfall.
  unfold eta_ctor.
  destruct (find _ _) as [((? & ?) & ?)|].
  - now apply wfe_term_eta_single.
  - now apply wfe_term_mkApps.
Qed.

Lemma wfe_term_eta_const Σ kn args :
  wfe_term Σ (tConst kn) ->
  Forall (wfe_term Σ) args ->
  wfe_term Σ (eta_const kn args).
Proof.
  intros wft wfall.
  unfold eta_const.
  destruct (find _ _) as [((? & ?) & ?)|].
  - now apply wfe_term_eta_single.
  - now apply wfe_term_mkApps.
Qed.

Lemma wfe_term_eta_expand_aux Σ args t :
  Forall (wfe_term Σ) args ->
  wfe_term Σ t ->
  wfe_term Σ (eta_expand_aux args t).
Proof.
  revert args.
  induction t using term_forall_list_ind; intros args wfall wft; cbn in *; auto.
  - now apply wfe_term_mkApps.
  - now apply wfe_term_mkApps.
  - now apply wfe_term_mkApps.
  - apply wfe_term_mkApps; [|easy].
    now induction H; cbn in *.
  - now apply wfe_term_mkApps.
  - apply wfe_term_mkApps; cbn; easy.
  - apply IHt1; [|easy].
    constructor; [|easy].
    now apply IHt2.
  - now apply wfe_term_eta_const.
  - now apply wfe_term_eta_ctor.
  - apply wfe_term_mkApps; [|easy].
    cbn.
    destruct p.
    split; [easy|].
    split; [easy|].
    destruct wft as (_ & (_ & allwf)).
    induction X; cbn in *; easy.
  - now apply wfe_term_mkApps.
  - apply wfe_term_mkApps; [|easy].
    induction H; cbn in *; easy.
  - apply wfe_term_mkApps; [|easy].
    induction H; cbn in *; easy.
Qed.

Lemma wfe_term_eta_expand Σ t :
  wfe_term Σ t ->
  wfe_term Σ (eta_expand t).
Proof. now apply wfe_term_eta_expand_aux. Qed.

Lemma decompose_app_rec_app t acc acc' :
  let (hd, args) := decompose_app_rec t acc in
  decompose_app_rec t (acc ++ acc') = (hd, args ++ acc').
Proof.
  revert acc.
  induction t using term_forall_list_ind; intros acc; try easy.
  cbn.
  specialize (IHt1 (t2 :: acc)).
  now rewrite <- app_comm_cons in IHt1.
Qed.

Lemma eta_expand_aux_unfold t args :
  eta_expand_aux args t =
  match decompose_app t with
  | (tConstruct ind c, args') => eta_ctor ind c (map (eta_expand_aux []) args' ++ args)
  | (tConst kn, args') => eta_const kn (map (eta_expand_aux []) args' ++ args)
  | (hd, args') => mkApps
                     (map_subterms (eta_expand_aux []) hd)
                     (map (eta_expand_aux []) args' ++ args)
  end.
Proof.
  revert args.
  induction t using term_forall_list_ind; intros args; cbn in *;
    try easy.
  rewrite IHt1.
  unfold decompose_app.
  pose proof (decompose_app_rec_app t1 [] [t2]).
  destruct (decompose_app_rec t1 []) as [hd args'].
  cbn in *.
  rewrite H.
  rewrite map_app.
  cbn.
  now rewrite <- app_assoc.
Qed.

Lemma eta_expand_unfold t :
  eta_expand t =
  match decompose_app t with
  | (tConstruct ind c, args) => eta_ctor ind c (map eta_expand args)
  | (tConst kn, args) => eta_const kn (map eta_expand args)
  | (hd, args) => mkApps (map_subterms eta_expand hd) (map eta_expand args)
  end.
Proof.
  unfold eta_expand at 1.
  rewrite eta_expand_aux_unfold.
  destruct (decompose_app _).
  now rewrite app_nil_r.
Qed.

End eta_correctness.
*)

Section dearg_correctness.
Context (ind_masks : list (kername * mib_masks)).
Context (const_masks : list (kername * bitmask)).

Fixpoint has_use (rel : nat) (t : term) : bool :=
  match t with
  | tRel i => i =? rel
  | tEvar _ ts => fold_right orb false (map (has_use rel) ts)
  | tLambda _ body => has_use (S rel) body
  | tLetIn _ val body => has_use rel val || has_use (S rel) body
  | tApp hd arg => has_use rel hd || has_use rel arg
  | tCase _ _ brs => fold_right orb false (map (has_use rel ∘ snd) brs)
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

Lemma dearg_single_0_mask mask args t :
  Forall (eq false) mask ->
  #|args| = #|mask| ->
  dearg_single mask t args = mkApps t args.
Proof.
  intros mask_zero.
  revert args t.
  induction mask_zero.
  - destruct args; easy.
  - intros [|a args] t len_eq; [easy|].
    subst.
    cbn in *.
    now apply IHmask_zero.
Qed.

Lemma dearg_single_snoc mask b t args a :
  #|mask| = #|args| ->
  dearg_single (mask ++ [b]) t (args ++ [a]) =
  if b then
    dearg_single mask t args
  else
    tApp (dearg_single mask t args) a.
Proof.
  revert t args b a.
  induction mask as [|b mask IH]; intros t args bend aend len_eq.
  - now destruct args as [|a args]; [|easy].
  - destruct args as [|a args]; [easy|].
    cbn in *.
    destruct b.
    + now apply IH.
    + now apply IH.
Qed.

Definition mkLambda_or_LetIn (cd : context_decl) (t : term) : term :=
  match decl_body cd with
  | None => tLambda (decl_name cd) t
  | Some body => tLetIn (decl_name cd) body t
  end.

Definition it_mkLambda_or_LetIn (Γ : context) (t : term) : term :=
  fold_left (fun t d => mkLambda_or_LetIn d t) Γ t.

Fixpoint decompose_body_masked (mask : bitmask) (Γ : context) (t : term) : context * term :=
  match mask, t with
  | _, tLetIn na val body => decompose_body_masked mask (Γ,, vdef na val) body
  | b :: mask, tLambda na body => decompose_body_masked mask (Γ,, vass na) body
  | _, _ => (Γ, t)
  end.

Definition vasses (Γ : context) : context :=
  filter (fun cd => match decl_body cd with
                    | Some _ => false
                    | None => true
                    end) Γ.

Ltac refold :=
  repeat
    match goal with
    | [H: context[fold_left _ ?Γ ?t] |- _] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [|- context[fold_left _ ?Γ ?t]] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [H: context[filter _ ?Γ] |- _] => progress (fold (vasses Γ) in * )
    | [|- context[filter _ ?Γ]] => progress (fold (vasses Γ) in * )
    end.

Lemma it_mkLambda_or_LetIn_app Γ Γ' t :
  it_mkLambda_or_LetIn (Γ ++ Γ') t =
  it_mkLambda_or_LetIn Γ' (it_mkLambda_or_LetIn Γ t).
Proof.
  revert Γ' t.
  induction Γ; [easy|]; intros Γ' t; cbn in *.
  refold.
  now rewrite IHΓ.
Qed.

Lemma vasses_app Γ Γ' :
  vasses (Γ ++ Γ') = vasses Γ ++ vasses Γ'.
Proof.
  unfold vasses.
  now rewrite filter_app.
Qed.

Lemma decompose_body_masked_spec mask Γ t Γ' t' :
  valid_dearg_mask mask t ->
  (Γ', t') = decompose_body_masked mask Γ t ->
  #|vasses Γ'| = #|vasses Γ| + #|mask| /\
  it_mkLambda_or_LetIn Γ t = it_mkLambda_or_LetIn Γ' t'.
Proof.
  revert Γ t' mask.
  induction t using term_forall_list_ind; intros Γ t' mask valid_mask eq.
  all: cbn in *.
  all: try solve [destruct mask; [|easy]; inversion eq; easy].
  - destruct mask as [|b mask]; inversion eq; subst; clear eq; [easy|].
    cbn in *.
    destruct (IHt _ _ _ (proj2 valid_mask) H0) as (-> & <-).
    now cbn.
  - now destruct (IHt2 _ _ _ valid_mask ltac:(destruct mask; eassumption)) as (-> & <-).
Qed.

Lemma valid_dearg_mask_spec mask t :
  valid_dearg_mask mask t ->
  exists Γ inner,
    #|vasses Γ| = #|mask| /\ t = it_mkLambda_or_LetIn Γ inner.
Proof.
  intros is_valid.
  destruct (decompose_body_masked mask [] t) as (Γ & inner) eqn:decomp.
  exists Γ, inner.
  change t with (it_mkLambda_or_LetIn [] t).
  change #|mask| with (#|vasses []| + #|mask|).
  now apply decompose_body_masked_spec.
Qed.

Definition fold_context f (Γ : context) : context :=
  List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

Definition subst_decl s k (d : context_decl) := map_decl (subst s k) d.

Definition subst_context n k (Γ : context) : context :=
  fold_context (fun k' => subst n (k' + k)) Γ.

Lemma subst_context_snoc s k Γ d :
  subst_context s k (d :: Γ) = subst_context s k Γ ,, subst_decl s (#|Γ| + k) d.
Proof.
  cbn.
  rewrite mapi_rec_app.
  cbn.
  rewrite List.rev_app_distr.
  cbn.
  unfold snoc.
  f_equal.
  rewrite List.rev_length.
  now rewrite Nat.add_0_r.
Qed.

Lemma subst_it_mkLambda_or_LetIn n k ctx t :
  subst n k (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (subst_context n k ctx) (subst n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; [easy|].
  pose (subst_context_snoc n k ctx a). unfold snoc in e. rewrite e. clear e.
  simpl. rewrite -> IHctx.
  pose (subst_context_snoc n k ctx a). simpl. now destruct a as [na [b|]].
Qed.

(* Close a term t that lives in a context Γ given args for each assumption in Γ *)
Fixpoint close_term_aux (Γ : context) (t : term) (args : list term) : term :=
  match Γ with
  | [] => t
  | cd :: Γ =>
    match decl_body cd with
    | Some val => close_term_aux Γ (t { 0 := val }) args
    | None =>
      match args with
      | a :: args => close_term_aux Γ (t { 0 := a }) args
      | [] => t
      end
    end
  end.

Definition close_term (Γ : context) (t : term) (args : list term) : term :=
  close_term_aux Γ t (List.rev args).

Lemma close_term_aux_app Γ Γ' inner args :
  #|vasses Γ| <= #|args| ->
  close_term_aux (Γ ++ Γ') inner args =
  close_term_aux Γ' (close_term_aux Γ inner args) (skipn #|vasses Γ| args).
Proof.
  revert Γ' inner args.
  induction Γ; intros Γ' inner args le.
  - cbn.
    now rewrite skipn_0.
  - cbn in *.
    refold.
    destruct (decl_body a).
    + easy.
    + destruct args; cbn in *; [abstract lia|].
      apply IHΓ.
      abstract lia.
Qed.

Lemma filter_rev {A} f (l : list A) :
  filter f (List.rev l) = List.rev (filter f l).
Proof.
  induction l; [easy|].
  cbn.
  rewrite filter_app.
  cbn.
  destruct (f a); cbn.
  - now f_equal.
  - now rewrite app_nil_r.
Qed.

Lemma vasses_rev Γ : vasses (List.rev Γ) = List.rev (vasses Γ).
Proof. apply filter_rev. Qed.

Lemma close_term_app Γ Γ' inner args :
  #|vasses Γ| <= #|args| ->
  close_term (Γ ++ Γ') inner args =
  close_term Γ' (close_term Γ inner args) (List.rev (skipn #|vasses Γ| (List.rev args))).
Proof.
  intros le.
  unfold close_term.
  rewrite close_term_aux_app by (now rewrite List.rev_length).
  now rewrite List.rev_involutive.
Qed.

(*
Lemma subst_context_app Γ Γ' inner args :
  #|vasses Γ'| <= #|args| ->
  subst_context (Γ ++ Γ') inner args =
  subst_context Γ (subst_context Γ' inner args) (skipn #|vasses Γ'| args).
Proof.
  intros len.
  unfold subst_context.
  rewrite List.rev_app_distr.
  rewrite subst_context_aux_app.
  - now rewrite vasses_rev, List.rev_length.
  - now rewrite vasses_rev, List.rev_length.
Qed.

Lemma subst_context_aux_enough_args Γ inner args :
  subst_context_aux Γ inner args =
  subst_context_aux Γ inner (firstn #|vasses Γ| args).
Proof.
  revert inner args.
  induction Γ; intros inner args; [easy|].
  cbn.
  refold.
  destruct (decl_body a).
  - easy.
  - destruct args; [easy|].
    apply IHΓ.
Qed.

Lemma subst_context_enough_args Γ inner args :
  subst_context Γ inner args =
  subst_context Γ inner (firstn #|vasses Γ| args).
Proof.
  unfold subst_context.
  replace #|vasses Γ| with #|vasses (List.rev Γ)|.
  - apply subst_context_aux_enough_args.
  - now rewrite vasses_rev, List.rev_length.
Qed.

Lemma firstn_all_app_eq {A} n (l l' : list A) :
  n = #|l| ->
  firstn n (l ++ l') = l.
Proof.
  intros ->.
  replace #|l| with (#|l| + 0) by lia.
  rewrite firstn_app_2.
  cbn.
  apply app_nil_r.
Qed.
*)

Derive Signature for eval.
Derive NoConfusionHom for term.

Lemma eval_LetIn Σ na val body res :
  Σ ⊢ tLetIn na val body ▷ res ->
  exists val_res,
    Σ ⊢ val ▷ val_res /\
    Σ ⊢ csubst val_res 0 body ▷ res.
Proof.
  intros ev.
  depind ev; try easy.
  - destruct args using List.rev_ind; [easy|].
    rewrite mkApps_app in *.
    cbn in *.
    congruence.
  - destruct args using List.rev_ind.
    + cbn in *.
      depelim H.
      subst f.
      now eapply IHev.
    + rewrite mkApps_app in *.
      cbn in *.
      congruence.
Qed.

(*
Lemma mkApps_inv h f args :
  h = mkApps f args ->
  (h = f /\ args = []) \/
  (exists args' a h',
      args = args' ++ [a] /\
      h = tApp (mkApps h' args') a).
Proof.
  intros ->.
  destruct args using List.rev_ind.
  - left; easy.
  - right.
    rewrite mkApps_app.
    cbn.
    exists args, x.
Qed.
*)

Lemma eval_tApp_head Σ hd args v :
  Σ ⊢ tApp hd args ▷ v ->
  exists v', Σ ⊢ hd ▷ v'.
Proof.
  intros ev.
  depind ev.
  - easy.
  - easy.
  - destruct args using List.rev_ind; [easy|].
    clear IHargs.
    rewrite mkApps_app in H3.
    cbn in *.
    apply Forall2_length in H2 as args_len.
    rewrite !app_length in *.
    cbn in *.
    destruct args' as [|a' args' _] using List.rev_ind; [cbn in *; abstract lia|].
    exists (mkApps (tFix mfix idx) args').
    inversion H3; subst; clear H3.
    apply eval_fix_value.
    + easy.
    + apply Forall2_app_r in H2.
      easy.
    + unfold isStuckFix, cunfold_fix, ETyping.unfold_fix in *.
      destruct (nth_error mfix idx) as [f'|]; [|easy].
      replace (rarg f') with narg by congruence.
      unfold ETyping.is_constructor.
      rewrite !app_length in *.
      cbn in *.
      rewrite (proj2 (nth_error_None _ _)) by abstract lia.
      easy.
  - destruct args as [|a args _] using List.rev_ind.
    + cbn in *.
      eapply IHev.
      now f_equal.
    + rewrite mkApps_app in H1.
      apply Forall2_length in H as args_len.
      rewrite !app_length in *.
      cbn in *.
      destruct args' as [|a' args' _] using List.rev_ind; [cbn in *; abstract lia|].
      exists (mkApps (tFix mfix idx) args').
      inversion H1; subst; clear H1.
      apply eval_fix_value.
      * easy.
      * apply Forall2_app_r in H.
        easy.
      * unfold isStuckFix.
        destruct (ETyping.unfold_fix mfix idx) as [(? & ?)|]; [|easy].
        unfold ETyping.is_constructor in H0.
        destruct (Nat.ltb_spec n #|args'|).
        -- rewrite nth_error_app_lt in H0 by easy.
           apply H0.
        -- unfold ETyping.is_constructor.
           now rewrite (proj2 (nth_error_None _ _)) by abstract lia.
  - easy.
  - easy.
Qed.

Lemma eval_tApp_arg Σ hd arg res :
  Σ ⊢ tApp hd arg ▷ res ->
  exists arg_res,
    Σ ⊢ arg ▷ arg_res.
Proof.
  intros ev.
  depind ev; try easy.
  - destruct args using List.rev_ind; [easy|].
    destruct args' using List.rev_ind.
    + unfold ETyping.is_constructor_or_box in *.
      now rewrite nth_error_nil in H0.
    + rewrite mkApps_app in *.
      cbn in *.
      exists x0.
      apply Forall2_app_r in H2.
      destruct H2.
      congruence.
  - destruct args using List.rev_ind.
    + cbn in *.
      subst f.
      easy.
    + rewrite mkApps_app in *.
      cbn in *.
      destruct args' using List.rev_ind.
      * depelim H.
        apply (f_equal (@List.length term)) in H.
        rewrite app_length in H.
        now cbn in H.
      * apply Forall2_app_r in H.
        exists x0.
        destruct H.
        congruence.
Qed.

(*
(*
Lemma eval_App Σ na body arg res :
  Σ ⊢ tApp (tLambda na body) arg ▷ res ->
  exists arg_res,
    Σ ⊢ arg  ▷ arg_res /\
    Σ ⊢ csubst arg_res 0 body ▷ res.
Proof.
  intros ev.
  depind ev.
  - depelim ev1.
    + destruct args using List.rev_ind; [easy|].
      rewrite mkApps_app in *.
      cbn in *.
      congruence.
    + destruct args' using List.rev_ind; [easy|].
      rewrite mkApps_app in *.
      cbn in *.
      congruence.
  - exists a'.
    split; [easy|].
    depelim ev1.
    + admit.
    + admit.
    + easy.
  - SearchAbout mkApps.
    pose proof (mkApps_elim f args).
    rewrite <- H3 in H4.
    cbn in H4.
    depelim H4.
    destruct n.
    + rewrite skipn_0 in H1, H2.
      cbn in *.
      admit.
    + rewrite skipn_S, skipn_nil in H1.
      easy.
  - admit.
  - apply eval_to_value in ev1.
    depelim ev1.
    + unfold atom in H.
    exists a'.
    split; [easy|].
    SearchAbout eval.
    rewrite mkApps_nested in H3.
    cbn in *.
    inversion H4.
    change (tApp (tLambda na body) arg) with (mkApps (tLambda na body) [arg]) in H3.
    apply mkApps_eq_inj in H3; try easy.
    2: {
*)

(*
Lemma eval_mkApps_subst_context Σ Γ inner args res :
  #|args| = #|vasses Γ| ->
  Σ ⊢ mkApps (it_mkLambda_or_LetIn Γ inner) args ▷ res ->
  Σ ⊢ subst_context Γ inner (List.rev args) ▷ res.
Proof.
  revert inner args res.
  induction Γ as [|cd Γ IH] using List.rev_ind; intros inner args res len_eq ev.
  - cbn in *.
    now destruct args.
  - rewrite vasses_app, app_length in len_eq; cbn in *.
    destruct (decl_body cd) eqn:decl_eq.
    + cbn in *.
      rewrite subst_context_app by (abstract (rewrite List.rev_length; lia)).
      rewrite it_mkLambda_or_LetIn_app in *.
      cbn in *.
      unfold mkLambda_or_LetIn in *.
      rewrite decl_eq in *.
      assert (exists args_res, Forall2 (eval Σ) args args_res) by admit.
      assert (exists let_in_res,
                 Σ ⊢ tLetIn (decl_name cd) t (it_mkLambda_or_LetIn Γ inner) ▷ let_in_res)
        by admit.
      destruct H0 as (let_in_res & eval_let_in).
      apply eval_LetIn in eval_let_in.
      destruct eval_let_in as (val_res & eval_t & eval_subst).
Lemma eval_csubst_congr t tn b res :
  Σ ⊢ t ▷ tn ->
  Σ ⊢ csubst tn 0 b ▷ res ->
  Σ ⊢ csubst t 0 b ▷ res.

      epose proof (IH inner args _ ltac:(abstract lia)).
      eapply eval_LetIn.
    destruct args as [|a args] using List.rev_ind.
    + cbn in *.
*)

(*
Lemma eval_mkApps_it_mkLambda_or_LetIn Σ Γ inner args res :
  #|args| = #|vasses Γ| ->
  Σ ⊢ subst_context Γ inner (List.rev args) ▷ res ->
  Σ ⊢ mkApps (it_mkLambda_or_LetIn Γ inner) args ▷ res.
Proof.
  revert inner args res.
  induction Γ as [|cd Γ IH] using List.rev_ind; intros inner args res len_eq eval_res.
  - cbn in *.
    now destruct args.
  - rewrite it_mkLambda_or_LetIn_app.
    unfold vasses in len_eq; rewrite filter_app in len_eq; refold.
    rewrite app_length in len_eq.
    rewrite subst_context_app in eval_res by (abstract (rewrite List.rev_length; lia)).
    cbn in *.
    unfold mkLambda_or_LetIn.
    destruct (decl_body cd) as [body|].
    +
    + destruct args as [|a args]; [cbn in *; abstract lia|].
      cbn in *.
      rewrite skipn_all_app_eq in eval_res by (abstract (rewrite List.rev_length; lia)).
      rewrite subst_context_enough_args in eval_res.
      rewrite firstn_all_app_eq in eval_res by (abstract (rewrite List.rev_length; lia)).
      admit.
Admitted.
*)

Fixpoint subst_in_let_values (ts : list term) (k : nat) (Γ : context) : context :=
  match Γ with
  | [] => []
  | cd :: Γ =>
    {| decl_name := decl_name cd; decl_body := option_map (subst ts k) (decl_body cd) |}
       :: subst_in_let_values ts (S k) Γ
  end.

Fixpoint deass_context (mask : bitmask) (Γ : context) : context :=
  match Γ with
  | [] => []
  | cd :: Γ =>
    match decl_body cd with
    | Some val => cd :: deass_context mask Γ
    | None =>
      match mask with
      | true :: mask => subst_in_let_values [tBox] 0 (deass_context mask Γ)
      | false :: mask => cd :: deass_context mask Γ
      | [] => []
      end
    end
  end.
*)

(*
Lemma deass_context_app mask Γ Γ' :
  #|vasses Γ| = #|mask| ->
  deass_context mask (Γ ++ Γ') =
  deass_context mask Γ ++ deass_context (skipn #|vasses Γ| mask) Γ'.
Proof.
  revert mask Γ'.
  induction Γ as [|cd Γ IH]; intros mask Γ' len_le.
  - cbn.
    destruct mask; easy.
  - cbn in *.
    destruct (decl_body cd).
    + cbn.
      refold.
      now f_equal.
    + cbn.
      refold.
      destruct mask as [|b mask]; [cbn in *; abstract lia|].
      destruct b.
      *
        rewrite <- plus_Snm_nSm.
        apply IH.
        cbn in *.
        abstract lia.
      * cbn in *.
        unfold skipn; fold (skipn #|vasses Γ| mask). (* wtf *)
        f_equal.
        now apply IH.
Qed.
*)

(*
Lemma deass_context_enough mask Γ :
  deass_context mask Γ = deass_context (firstn #|vasses Γ| mask) Γ.
Proof.
  revert mask.
  induction Γ; intros mask; [easy|].
  cbn.
  destruct (decl_body a).
  - f_equal.
    easy.
  - refold.
    destruct mask as [|b mask]; [easy|].
    destruct b; cbn; [easy|].
    now f_equal.
Qed.

Local Set Keyed Unification.
Lemma dearg_cst_body_top_it_mkLambda_or_LetIn mask Γ inner ts k :
  #|vasses Γ| = #|mask| ->
  subst ts k (dearg_cst_body_top mask (it_mkLambda_or_LetIn Γ inner)) =
  it_mkLambda_or_LetIn
    (subst_in_let_values ts k (deass_context mask Γ))
    (subst (List.repeat tBox #|filter id mask| ++ ts) (#|Γ| + k) inner).
Proof.
  revert inner mask ts k.
  induction Γ as [|cd Γ IH]; intros inner mask ts k len_eq.
  - destruct mask; [|easy].
    cbn.
    now rewrite dearg_cst_body_top_nil.
  - cbn in *; refold.
    unfold mkLambda_or_LetIn.
    destruct (decl_body cd) eqn:body_eq.
    + cbn.
      refold.
      unfold mkLambda_or_LetIn.
      rewrite body_eq.
      cbn.
      f_equal.
      replace (S (#|Γ| + k)) with (#|Γ| + S k) by abstract lia.
      now apply IH.
    + cbn in *.
      destruct mask as [|b mask]; [cbn in *; abstract lia|].
      cbn in *.
      destruct b; cbn.
      * rewrite distr_subst.
        cbn.
        rewrite IH by easy.
        change (tBox :: ?a) with ([tBox] ++ a) at 3.
        rewrite subst_app_simpl.
        cbn.
        SearchAbout (subst _ _ (subst _ _ _)).
        replace (S k) with (k + #|[tBox]|) by (cbn; lia).
        rewrite <- subst_app_simpl.

        rewrite IH by easy.
        rewrite unlift_unlift.
        SearchAbout (lift _ _ (lift _ _ _)).
        rewrite IH by easy.
        rewrite IH by easy.

      * cbn.
        unfold mkLambda_or_LetIn.
        rewrite body_eq.
        f_equal.
        rewrite deass_context_enough.
        rewrite firstn_all_app_eq by (rewrite List.rev_length; abstract lia).
        now apply IHΓ.
Admitted.
*)

Fixpoint eval_lambdas Σ (t : term) (args : list term) : Prop :=
  match args with
  | [] => exists res, Σ ⊢ t ▷ res
  | a :: args =>
    exists na body,
      Σ ⊢ t ▷ tLambda na body /\
      eval_lambdas Σ (tApp (tLambda na body) a) args
  end.

Lemma eval_lambdas_LetIn Σ na val val_res body args :
  Σ ⊢ val ▷ val_res ->
  eval_lambdas Σ (csubst val_res 0 body) args ->
  eval_lambdas Σ (tLetIn na val body) args.
Proof.
  revert na val val_res body.
  induction args; intros na val val_res body ev_val ev; cbn in *.
  - intros.
    destruct ev as (res & ev).
    exists res.
    econstructor; easy.
  - destruct ev as (na_lam & lam_body & ev_lam_val & ev).
    exists na_lam, lam_body.
    split.
    + econstructor; easy.
    + easy.
Qed.

Lemma eval_mkApps_head Σ hd args v :
  Σ ⊢ mkApps hd args ▷ v ->
  exists v', Σ ⊢ hd ▷ v'.
Proof.
  revert hd v.
  induction args using List.rev_ind; [easy|]; intros hd v ev.
  rewrite mkApps_app in *.
  cbn in *.
  apply eval_tApp_head in ev.
  destruct ev as (v' & ev).
  now apply (IHargs _ v').
Qed.

Lemma valid_dearg_mask_eval_lambdas mask body Σ args t :
  valid_dearg_mask mask body ->
  #|args| = #|mask| ->
  Σ ⊢ mkApps body args ▷ t ->
  eval_lambdas Σ body args.
Proof.
  intros valid_mask len_eq ev.
  destruct (valid_dearg_mask_spec _ _ valid_mask) as (Γ & inner & Γlen & ->).
  revert args t inner len_eq ev Γlen valid_mask.
  induction Γ as [|cd Γ IH] using List.rev_ind; intros args t inner len_eq ev Γlen valid_mask.
  - cbn in *.
    destruct mask; [|easy].
    destruct args; [|easy].
    cbn in *.
    easy.
  - rewrite it_mkLambda_or_LetIn_app in *.
    rewrite vasses_app in *.
    cbn in *.
    unfold mkLambda_or_LetIn in *.
    destruct (decl_body cd) eqn:decl_eq.
    + apply eval_mkApps_head in ev as (let_in_res & ev_let_in).
      apply eval_LetIn in ev_let_in as (val_res & ev_val_res & subst_body_eval).
      eapply eval_lambdas_LetIn; [eassumption|].
      SearchAbout (_ ⊢ mkApps _ _ ▷ _).
      eapply eval_lambdas_LetIn; cycle 1.

      kcbn in *.
      rewrite app_nil_r in Γlen.
      specialize
Admitted.

(*
Lemma dearg_single_correct_full Σ body args t mask :
  eval_lambdas Σ body args ->
  Σ ⊢ mkApps body args ▷ t ->
  valid_dearg_mask mask body ->
  length args = length mask ->
  Σ ⊢ dearg_single mask (dearg_cst_body_top mask body) args ▷ t.
Proof.
*)

Lemma dearg_single_correct mask body args Σ t :
  Σ ⊢ mkApps body args ▷ t ->
  valid_dearg_mask mask body ->
  #|args| = #|mask| ->
  Σ ⊢ dearg_single mask (dearg_cst_body_top mask body) args ▷ t.
Proof.
  intros eval valid_mask len_eq.
  destruct (valid_dearg_mask_spec _ _ valid_mask) as (Γ & inner & Γlen & ->).
  revert mask args t inner valid_mask eval len_eq Γlen.
  induction Γ as [|cd Γ IH] using List.rev_ind; intros mask args t inner valid_mask ev len_eq Γlen.
  - cbn in *.
    destruct mask; [|easy].
    destruct args; [|easy].
    cbn.
    now rewrite dearg_cst_body_top_nil.
  - rewrite vasses_app, app_length in Γlen.
    rewrite it_mkLambda_or_LetIn_app in *.
    cbn in *.
    unfold mkLambda_or_LetIn in *.
    destruct (decl_body cd) eqn:decl_eq.
    + cbn in *.
      admit.
    + cbn in *.
      destruct mask as [|b mask]; [easy|].
      destruct args as [|a args]; [easy|].
      destruct b.
      * cbn.
      cbn.


Lemma foo :
  #|mask| = #|args| ->
  Σ ⊢ dearg_single mask  args ▷ res

Inductive eval_apps Σ res : term -> list term -> Prop :=
| eval_apps_nil t : Σ ⊢ t ▷ res -> eval_apps_nil Σ res t []
| eval_apps_cons t args :
    eval_apps Σ res t args ->
    Σ ⊢ tApp t

Fixpoint mkApps_eval_spine :
  -> mkApps t


      Σ ⊢ mkApps hd args ▷ res
  apply eval_mkApps_subst_context in eval; [|congruence].

  induction Γ.
  - cbn in *.
    destruct mask; [|easy].
    destruct args; [|easy].
    now rewrite dearg_cst_body_top_nil.
  - cbn in *; refold.


    rewrite <- it_mkLambda_or_LetIn_unfold in *.
  revert mask body t.
  induction args as [|a args IH] using List.rev_ind; intros mask body t eval valid_mask len_eq.
  - destruct mask as [|b mask]; [|easy].
    now rewrite dearg_cst_body_top_nil.
  - rewrite mkApps_app.
    rewrite app_length in len_eq.
    destruct mask as [|b mask] using List.rev_ind.
    + rewrite dearg_cst_body_top_nil.
      cbn.
      now rewrite Prelim.emkApps_snoc.
    + clear IHmask.
      rewrite app_length in len_eq.
      rewrite dearg_single_snoc by (cbn in *; abstract lia).
      destruct b.
      * destruct (dearg_cst_body_top_snoc_true mask body valid_mask)
          as (na & Γ & inner & -> & ->).

        destruct (valid_dearg_mask_snoc_true mask body valid_mask)
          as (na & inner_body & -> & no_use & valid_inner & ->).
        apply IH; [|easy|cbn in *; abstract lia].
      admit.
      unfold dearg_single.
      intros
    inversion eval; subst; clear eval.
    +
      destruct b.
      *
  intros eval valid_mask.
  revert args t eval mask valid_mask.
  induction body using term_forall_list_ind; intros args t eval mask valid_mask len_eq;
    try solve [
          cbn in *;
          destruct mask as [|[] ?];
          now rewrite ?dearg_single_0_mask].
  - cbn in *.
    clear IHbody.
    revert mask valid_mask len_eq.
    induction args as [|a args IH]; cbn in *; intros mask valid_mask len_eq.
    + destruct mask; easy.
    + destruct mask as [|b mask]; [easy|].
      destruct b; cbn in *.
      *
    admit.
  - cbn in *.
    induction mask as [|b mask]; [easy|].
    destruct args as [|a args]; [easy|].
    destruct b; cbn in *.
    + (* Arg was removed, use the fact that there is no use to show that unlift
         commutes with beta application in this case. *)

    destruct mask as [|[] ?].
    + cbn in *.

  - cbn in *.
    destruct mask as [|[] ?].
    + easy.
    + now rewrite dearg_single_0_mask by easy.
    + now rewrite dearg_single_0_mask by easy.
  - cbn in *.
    assert (Forall (eq false) mask).
    { destruct mask as [|[] ?]; auto. }
    rewrite dearg_single_0_mask by easy.

  - cbn in *.
    destruct mask; [|easy].
    cbn.
    now rewrite dearg_cst_body_top_nil.
  - destruct mask as [|b mask]; [easy|].
    cbn in *.
    destruct b.
    + induction body using term_forall_list_ind;
        try solve [cbn in *; inversion_clear valid_mask; congruence].
      * cbn in *.
        inversion_clear valid_mask; try congruence.
      * cbn in *.
        inversion_clear valid_mask.

Definition const_mask_wf_top Σ (p : kername * bitmask) : Prop :=
  exists cst,
    declared_constant Σ p.1 cst /\
    match cst_body cst with
    | Some body => valid_dearg_mask p.2 body
    | None => False
    end.

Definition const_masks_wf_top Σ : Prop :=
  Forall (const_mask_wf_top Σ) const_masks.

Fixpoint enough_lambdas (mask : bitmask) (body : term) : Prop :=
  match mask, body with
  | _ :: mask, tLambda _ body => enough_lambdas mask body
  | mask, _ => Forall (eq false) mask
  end.

Definition case_shape
           (ind : inductive) (npars : nat)
           (brs : list (nat * term)) : Prop :=
  match get_mib_masks ind_masks (inductive_mind ind) with
  | Some mib_masks =>
    npars = length (param_mask mib_masks) /\
    ∥ Alli (fun c '(_, br) =>
            match find (fun '(ind', c', _) => (ind' =? inductive_ind ind) && (c' =? c))
                       (ctor_masks mib_masks) with
            | Some (_, _, mask) => enough_lambdas mask br
            | None => True
            end)
         0 brs ∥
  | None => True
  end.

(* Proposition representing that all case branches have the correct shapes
   (iterated lambdas) to be dearged. *)
Fixpoint case_shapes (t : term) : Prop :=
  match t with
  | tBox => True
  | tRel _ => True
  | tVar _ => True
  | tEvar _ ts => fold_right and True (map case_shapes ts)
  | tLambda _ body => case_shapes body
  | tLetIn _ val body => case_shapes val /\ case_shapes body
  | tApp hd arg => case_shapes arg /\ case_shapes hd
  | tConst kn => True
  | tConstruct ind c => True
  | tCase (ind, npars) discr brs => case_shape ind npars brs /\
                                    fold_right and True (map (case_shapes ∘ snd) brs)
  | tProj p t => case_shapes t
  | tFix defs _
  | tCoFix defs _ => fold_right and True (map (case_shapes ∘ dbody) defs)
  end.

Notation dearg_ctor := (dearg_ctor ind_masks).
Notation dearg_consts := (dearg_const const_masks).
Notation dearg_case := (dearg_case ind_masks).
Notation dearg_aux := (dearg_aux ind_masks const_masks).
Notation dearg := (dearg ind_masks const_masks).
Notation dearg_cst := (dearg_cst ind_masks const_masks).
Notation dearg_mib := (dearg_mib ind_masks).
Notation dearg_decl := (dearg_decl ind_masks const_masks).
Notation dearg_env := (dearg_env ind_masks const_masks).

Theorem dearg_env_eval Σ s t :
  trans Σ ⊢ s ▷ t ->
  const_masks_wf_top Σ ->
  trans (dearg_env Σ) ⊢ dearg s ▷ dearg t.
Proof.
