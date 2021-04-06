From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import ExAst.
From ConCert.Utils Require Import StringExtra.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require VectorDef.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EArities.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import Prelim.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.PCUIC Require Import PCUICArities.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICCanonicity.
From MetaCoq.PCUIC Require Import PCUICConfluence.
From MetaCoq.PCUIC Require Import PCUICContextConversion.
From MetaCoq.PCUIC Require Import PCUICContexts.
From MetaCoq.PCUIC Require Import PCUICConversion.
From MetaCoq.PCUIC Require Import PCUICCumulativity.
From MetaCoq.PCUIC Require Import PCUICElimination.
From MetaCoq.PCUIC Require Import PCUICGeneration.
From MetaCoq.PCUIC Require Import PCUICInductiveInversion.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require Import PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICNormal.
From MetaCoq.PCUIC Require Import PCUICPrincipality.
From MetaCoq.PCUIC Require Import PCUICReduction.
From MetaCoq.PCUIC Require Import PCUICSN.
From MetaCoq.PCUIC Require Import PCUICSR.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICSubstitution.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICValidity.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.
From MetaCoq.Template Require TemplateMonad.

Import PCUICEnvTyping.
Import PCUICLookup.
Import PCUICErrors.

Local Open Scope string_scope.
Import VectorDef.VectorNotations.
Import ListNotations.
Import MonadNotation.
Set Equations Transparent.

Module P := PCUICAst.
Module Ex := ExAst.

Import PCUICAst.

Section FixSigmaExt.
Local Existing Instance extraction_checker_flags.
Context (Σ : global_env_ext).
Context (wfextΣ : ∥wf_ext Σ∥).
Let wfΣ : ∥wf Σ∥ := ltac:(now sq).

Opaque ErasureFunction.wf_reduction.
Opaque reduce_term.

Notation term_rel := (ErasureFunction.term_rel Σ).
Instance WellFounded_term_rel : WellFounded term_rel :=
  (ErasureFunction.wf_reduction Σ wfΣ).

Lemma sq_red_transitivity {Γ A} B {C} :
  ∥red Σ Γ A B∥ ->
  ∥red Σ Γ B C∥ ->
  ∥red Σ Γ A C∥ .
Proof.
  intros.
  sq.
  now transitivity B.
Qed.

Lemma isArity_red Γ u v :
  isArity u ->
  red Σ Γ u v ->
  isArity v.
Proof.
  intros arity_u r.
  induction r using red_rect'; [easy|].
  eapply isArity_red1; eassumption.
Qed.

Lemma isType_red_sq Γ t t' :
  ∥isType Σ Γ t∥ ->
  ∥red Σ Γ t t'∥ ->
  ∥isType Σ Γ t'∥.
Proof.
  intros [(s & typ)] [r].
  destruct wfΣ.
  constructor.
  exists s.
  red in typ |- *.
  eapply subject_reduction; eauto.
Qed.

Hint Resolve isType_red_sq : erase.

Lemma isType_prod_dom Γ na A B :
  ∥isType Σ Γ (tProd na A B)∥ ->
  ∥isType Σ Γ A∥.
Proof.
  intros [(s & typ)].
  destruct wfΣ.
  apply inversion_Prod in typ as (s' & ? & ? & ? & ?); [|now eauto].
  constructor.
  now exists s'.
Qed.

Hint Resolve isType_prod_dom : erase.

Lemma isType_prod_cod Γ na A B :
  ∥isType Σ Γ (tProd na A B)∥ ->
  ∥isType Σ (Γ,, vass na A) B∥.
Proof.
  intros [(s & typ)].
  destruct wfΣ.
  apply inversion_Prod in typ as (s' & ? & ? & ? & ?); [|now eauto].
  constructor.
  now exists x.
Qed.

Hint Resolve isType_prod_cod : erase.

Lemma Is_conv_to_Arity_red Γ T T' :
  Is_conv_to_Arity Σ Γ T ->
  ∥ red Σ Γ T T' ∥ ->
  Is_conv_to_Arity Σ Γ T'.
Proof.
  unfold Is_conv_to_Arity.
  intros [T'' (redT'' & is_arity)] red.
  sq.
  destruct (red_confluence wfΣ red redT'') as (a & reda' & reda'').
  exists a.
  split; [easy|].
  clear -is_arity reda''.
  eapply isArity_red; eauto.
Qed.

Hint Resolve Is_conv_to_Arity_red : erase.

Hint Resolve reduce_term_sound sq existT pair : erase.

Definition is_prod_or_sort (t : term) : bool :=
  match t with
  | tProd _ _ _
  | tSort _ => true
  | _ => false
  end.

Lemma not_prod_or_sort_hnf {Γ t wf} :
  negb (is_prod_or_sort (hnf wfΣ Γ t wf)) ->
  ~Is_conv_to_Arity Σ Γ t.
Proof.
  intros nar car.
  unfold hnf in nar.
  pose proof (reduce_term_sound RedFlags.default Σ wfΣ Γ t wf) as [r].
  pose proof (reduce_term_complete RedFlags.default Σ wfΣ Γ t wf) as wh.
  destruct wfΣ.
  apply Is_conv_to_Arity_inv in car as [(?&?&?&[r'])|(?&[r'])]; auto.
  - eapply red_confluence in r' as (?&r1&r2); eauto.
    apply invert_red_prod in r2 as (?&?&(->&?)&?); auto.
    destruct wh as [wh].
    eapply whnf_red_inv in wh; eauto.
    depelim wh.
    rewrite H in nar.
    now cbn in nar.
  - eapply red_confluence in r' as (?&r1&r2); eauto.
    apply invert_red_sort in r2 as ->; auto.
    destruct wh as [wh].
    eapply whnf_red_inv in wh; eauto.
    depelim wh.
    rewrite H in nar.
    now cbn in nar.
Qed.

Inductive term_sub_ctx : context * term -> context * term -> Prop :=
| sub_prod_dom Γ na A B : term_sub_ctx (Γ, A) (Γ, tProd na A B)
| sub_prod_cod Γ na A B : term_sub_ctx (Γ,, vass na A, B) (Γ, tProd na A B)
| sub_app_arg Γ arg hd arg1 :
    In arg (decompose_app (tApp hd arg1)).2 ->
    term_sub_ctx (Γ, arg) (Γ, tApp hd arg1).

Derive Signature for term_sub_ctx.

Lemma In_app_inv {X} (x : X) xs ys :
  In x (xs ++ ys) ->
  In x xs \/ In x ys.
Proof.
  intros isin.
  induction xs; [easy|].
  cbn in *.
  destruct isin as [->|]; [easy|].
  apply IHxs in H.
  now destruct H.
Qed.

Lemma well_founded_term_sub_ctx : well_founded term_sub_ctx.
Proof.
  intros (Γ & t).
  induction t in Γ |- *; constructor; intros (Γs & ts) rel; try solve [inversion rel].
  - now depelim rel.
  - depelim rel.
    destruct (mkApps_elim t1 []).
    cbn in *.
    rewrite decompose_app_rec_mkApps, atom_decompose_app in H by easy.
    cbn in *.
    apply In_app_inv in H.
    destruct H as [|[|]]; cbn in *; subst; [|easy|easy].
    apply (IHt1 Γ).
    destruct (firstn n l) using List.rev_ind; [easy|].
    rewrite <- mkApps_nested.
    constructor.
    cbn.
    now rewrite decompose_app_rec_mkApps, atom_decompose_app by easy.
Qed.

Definition erase_rel : Relation_Definitions.relation (∑ Γ t, welltyped Σ Γ t) :=
  fun '(Γs; ts; wfs) '(Γl; tl; wfl) =>
    ∥∑m, red Σ Γl tl m × term_sub_ctx (Γs, ts) (Γl, m)∥.

Lemma cored_prod_l Γ na A A' B :
  cored Σ Γ A A' ->
  cored Σ Γ (tProd na A B) (tProd na A' B).
Proof.
  intros cor.
  depelim cor.
  - eapply cored_red_trans; [easy|].
    now constructor.
  - apply cored_red in cor as [cor].
    eapply cored_red_trans.
    2: now apply prod_red_l.
    now apply red_prod_l.
Qed.

Lemma cored_prod_r Γ na A B B' :
  cored Σ (Γ,, vass na A) B B' ->
  cored Σ Γ (tProd na A B) (tProd na A B').
Proof.
  intros cor.
  depelim cor.
  - eapply cored_red_trans; [easy|].
    now constructor.
  - apply cored_red in cor as [cor].
    eapply cored_red_trans.
    2: now apply prod_red_r.
    now apply red_prod_r.
Qed.

Lemma well_founded_erase_rel : well_founded erase_rel.
Proof.
  intros (Γl & l & wfl).
  destruct wfΣ as [wfΣu].
  induction (normalisation Σ Γl l wfl) as [l _ IH].
  remember (Γl, l) as p.
  revert wfl IH.
  replace Γl with (fst p) by (now subst).
  replace l with (snd p) by (now subst).
  clear Γl l Heqp.
  intros wfl IH.
  induction (well_founded_term_sub_ctx p) as [p _ IH'] in p, wfl, IH |- *.
  constructor.
  intros (Γs & s & wfs) [(m & mred & msub)].
  inversion msub; subst; clear msub.
  - eapply Relation_Properties.clos_rt_rtn1 in mred. inversion mred; subst.
    + rewrite H0 in *.
      apply (IH' (p.1, s)).
      { replace p with (p.1, tProd na s B) by (now destruct p; cbn in *; congruence).
        cbn.
        constructor. }
      intros y cor wfly.
      cbn in *.
      unshelve eapply (IH (tProd na y B)).
      3: now repeat econstructor.
      1: { eapply red_welltyped in wfl; eauto.
           eapply cored_red in cor as [cor].
           constructor.
           now apply red_prod_l. }
      now apply cored_prod_l.
    + apply Relation_Properties.clos_rtn1_rt in X0.
      unshelve eapply (IH (tProd na s B)).
      3: now repeat econstructor.
      1: { eapply red_welltyped in wfl; eauto.
           constructor.
           etransitivity; [exact X0|].
           now apply red1_red. }
      eapply red_neq_cored.
      { etransitivity; [exact X0|].
        now apply red1_red. }
      intros eq.
      rewrite eq in *.
      eapply cored_red_trans in X0; eauto.
      eapply ErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalisation; eauto.
  - eapply Relation_Properties.clos_rt_rtn1 in mred; inversion mred; subst.
    + apply (IH' (p.1,, vass na A, s)).
      { replace p with (p.1, tProd na A s) by (destruct p; cbn in *; congruence).
        cbn.
        now constructor. }
      intros y cor wfly.
      cbn in *.
      unshelve eapply IH.
      4: { constructor.
           eexists.
           split; try easy.
           constructor. }
      1: { eapply red_welltyped; eauto.
           eapply cored_red in cor as [cored].
           constructor.
           rewrite H0.
           now apply red_prod. }
      rewrite H0.
      now apply cored_prod_r.
    + apply Relation_Properties.clos_rtn1_rt in X0.
      unshelve eapply IH.
      4: { constructor.
           eexists.
           split; try easy.
           constructor. }
      1: { eapply red_welltyped; eauto.
           constructor.
           etransitivity; [exact X0|].
           now apply red1_red. }
      apply red_neq_cored.
      { etransitivity; [exact X0|].
        now apply red1_red. }
      intros eq.
      rewrite eq in *.
      eapply cored_red_trans in X0; eauto.
      eapply ErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalisation; eauto.
  - eapply Relation_Properties.clos_rt_rtn1 in mred; inversion mred; subst.
    + apply (IH' (p.1, s)).
      { replace p with (p.1, tApp hd arg1) by (destruct p; cbn in *; congruence).
        now constructor. }
      intros y cor wfly.
      destruct (mkApps_elim hd []).
      cbn in *.
      rewrite decompose_app_rec_mkApps, atom_decompose_app in H0 by easy.
      change (tApp ?hd ?arg) with (mkApps hd [arg]) in *.
      rewrite mkApps_nested in *.
      set (args := (firstn n l ++ [arg1])%list) in *.
      clearbody args.
      cbn in *.
      apply In_split in H0 as (args_pref & args_suf & ->).
      unshelve eapply (IH (mkApps f (args_pref ++ y :: args_suf))).
      3: { constructor.
           econstructor.
           split; [easy|].
           destruct args_suf using rev_ind.
           - rewrite <- mkApps_nested.
             constructor.
             cbn.
             rewrite decompose_app_rec_mkApps, atom_decompose_app by easy.
             cbn.
             now apply in_or_app; right; left.
           - rewrite <- app_tip_assoc, app_assoc.
             rewrite <- mkApps_nested.
             constructor.
             cbn.
             rewrite decompose_app_rec_mkApps, atom_decompose_app by easy.
             cbn.
             apply in_or_app; left.
             apply in_or_app; left.
             now apply in_or_app; right; left. }
      1: { eapply red_welltyped in wfl; eauto.
           eapply cored_red in cor as [cor].
           constructor.
           rewrite H1.
           apply red_mkApps; [easy|].
           apply All2_app; [now apply All2_refl|].
           constructor; [easy|].
           now apply All2_refl. }
      depelim cor; cycle 1.
      * apply cored_red in cor as [cor].
        eapply cored_red_trans.
        2: apply PCUICSubstitution.red1_mkApps_r.
        2: eapply OnOne2_app.
        2: now constructor.
        rewrite H1.
        apply red_mkApps; [easy|].
        apply All2_app; [now apply All2_refl|].
        constructor; [easy|].
        now apply All2_refl.
      * rewrite H1.
        constructor.
        apply PCUICSubstitution.red1_mkApps_r.
        eapply OnOne2_app.
        now constructor.
    + apply Relation_Properties.clos_rtn1_rt in X0.
      unshelve eapply (IH (tApp hd arg1)).
      3: { constructor.
           eexists.
           split; try easy.
           now constructor. }
      1: { eapply red_welltyped in wfl; eauto.
           constructor.
           etransitivity; [exact X0|].
           now apply red1_red. }
      apply red_neq_cored.
      { etransitivity; [exact X0|].
        now apply red1_red. }
      intros eq.
      rewrite eq in *.
      eapply cored_red_trans in X0; eauto.
      eapply ErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalisation; eauto.
Qed.

Instance WellFounded_erase_rel : WellFounded erase_rel :=
  Wf.Acc_intro_generator 1000 well_founded_erase_rel.
Opaque WellFounded_erase_rel.

Hint Constructors term_sub_ctx : erase.

Inductive fot_view : term -> Type :=
| fot_view_prod na A B : fot_view (tProd na A B)
| fot_view_sort univ : fot_view (tSort univ)
| fot_view_other t : negb (is_prod_or_sort t) -> fot_view t.

Equations fot_viewc (t : term) : fot_view t :=
fot_viewc (tProd na A B) := fot_view_prod na A B;
fot_viewc (tSort univ) := fot_view_sort univ;
fot_viewc t := fot_view_other t _.

Lemma tywt {Γ T} (isT : ∥isType Σ Γ T∥) : welltyped Σ Γ T.
Proof. destruct isT. now apply isType_welltyped. Qed.

(* Definition of normalized arities *)
Definition arity_ass := aname * term.

Fixpoint mkNormalArity (l : list arity_ass) (s : Universe.t) : term :=
  match l with
  | [] => tSort s
  | (na, A) :: l => tProd na A (mkNormalArity l s)
  end.

Lemma isArity_mkNormalArity l s :
  isArity (mkNormalArity l s).
Proof.
  induction l as [|(na & A) l IH]; cbn; auto.
Qed.

Record conv_arity {Γ T} : Type := build_conv_arity {
  conv_ar_context : list arity_ass;
  conv_ar_univ : Universe.t;
  conv_ar_red : ∥red Σ Γ T (mkNormalArity conv_ar_context conv_ar_univ)∥
}.

Global Arguments conv_arity : clear implicits.

Definition conv_arity_or_not Γ T : Type :=
  (conv_arity Γ T) + (~∥conv_arity Γ T∥).

Definition Is_conv_to_Sort Γ T : Prop :=
  exists univ, ∥red Σ Γ T (tSort univ)∥.

Definition is_sort {Γ T} (c : conv_arity_or_not Γ T) : option (Is_conv_to_Sort Γ T).
Proof.
  destruct c as [c|not_conv_ar].
  - destruct c as [[|(na & A) ctx] univ r].
    + apply Some.
      eexists.
      eassumption.
    + exact None.
  - exact None.
Defined.

Lemma red_it_mkProd_or_LetIn_smash_context Γ Δ t :
  red Σ Γ
      (it_mkProd_or_LetIn Δ t)
      (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ t)).
Proof.
  induction Δ in Γ, t |- * using ctx_length_rev_ind; cbn.
  - now rewrite expand_lets_nil.
  - change (Γ0 ++ [d]) with ([d],,, Γ0).
    rewrite smash_context_app_expand.
    destruct d as [na [b|] ty]; cbn.
    + unfold app_context.
      rewrite expand_lets_vdef, it_mkProd_or_LetIn_app, app_nil_r.
      cbn.
      rewrite lift0_context, lift0_id, subst_empty.
      rewrite subst_context_smash_context.
      cbn.
      etransitivity.
      { apply red1_red.
        apply red_zeta. }
      unfold subst1.
      rewrite subst_it_mkProd_or_LetIn.
      rewrite Nat.add_0_r.
      apply X.
      now rewrite subst_context_length.
    + unfold app_context.
      rewrite expand_lets_vass, !it_mkProd_or_LetIn_app.
      cbn.
      apply red_prod_r.
      rewrite subst_context_lift_id.
      now apply X.
Qed.

Lemma conv_arity_Is_conv_to_Arity {Γ T} :
  conv_arity Γ T ->
  Is_conv_to_Arity Σ Γ T.
Proof.
  intros [asses univ r].
  eexists.
  split; [eassumption|].
  apply isArity_mkNormalArity.
Qed.

Lemma Is_conv_to_Arity_conv_arity {Γ T} :
  Is_conv_to_Arity Σ Γ T ->
  ∥conv_arity Γ T∥.
Proof.
  intros (t & [r] & isar).
  eexists.
  destruct (destArity [] t) as [(ctx & univ)|] eqn:dar.
  + set (ctx' := rev_map (fun d => (decl_name d, decl_type d)) (smash_context [] ctx)).
    apply (build_conv_arity _ _ ctx' univ).
    constructor.
    transitivity t; [auto|].
    apply PCUICArities.destArity_spec_Some in dar.
    cbn in dar.
    subst.
    replace (mkNormalArity ctx' univ) with (it_mkProd_or_LetIn (smash_context [] ctx) (tSort univ)).
    { apply red_it_mkProd_or_LetIn_smash_context. }
    subst ctx'.
    pose proof (@smash_context_assumption_context [] ctx assumption_context_nil).
    clear -H.
    induction (smash_context [] ctx) using List.rev_ind; [easy|].
    rewrite it_mkProd_or_LetIn_app in *.
    rewrite rev_map_app.
    cbn.
    apply assumption_context_app in H as (? & ass_x).
    depelim ass_x.
    cbn.
    f_equal.
    now apply IHc.
  + exfalso.
    clear -isar dar.
    revert dar.
    generalize ([] : context).
    induction t; intros ctx; cbn in *; eauto; try congruence.
Qed.

Definition is_arity {Γ T} (c : conv_arity_or_not Γ T) :
  {Is_conv_to_Arity Σ Γ T} + {~Is_conv_to_Arity Σ Γ T}.
Proof.
  destruct c; [left|right].
  - apply (conv_arity_Is_conv_to_Arity c).
  - abstract (intros conv; apply Is_conv_to_Arity_conv_arity in conv; tauto).
Defined.

(* type_flag of a term indexed by the term's type. For example, for
      t    :   T
   eq_refl : 5 = 5 : Prop
   we would pass T to flag_of_type below, and it would give
   is_logical = true, conv_ar = right _. On the other hand, for
   (fun (X : Type) => X) : Type -> Type
   we would pass Type -> Type and get is_logical = false, conv_ar = left _.
*)
Record type_flag {Γ T} :=
  build_flag
    { (* Type is proposition when fully applied, i.e. either
         (T : Prop, or T a0 .. an : Prop). If this is an arity,
         indicates whether this is a logical arity (i.e. into Prop). *)
      is_logical : bool;
      (* Arity that this type is convertible to *)
      conv_ar : conv_arity_or_not Γ T;
    }.

Global Arguments type_flag : clear implicits.

Equations(noeqns) flag_of_type (Γ : context) (T : term) (isT : ∥isType Σ Γ T∥)
  : type_flag Γ T
  by wf ((Γ;T; (tywt isT)) : (∑ Γ t, welltyped Σ Γ t)) erase_rel :=
flag_of_type Γ T isT with inspect (hnf wfΣ Γ T (tywt isT)) :=
  | exist T is_hnf with fot_viewc T := {
    | fot_view_prod na A B with flag_of_type (Γ,, vass na A) B _ := {
      | flag_cod := {| is_logical := is_logical flag_cod;
                       conv_ar := match conv_ar flag_cod with
                                  | inl car =>
                                    inl {| conv_ar_context := (na, A) :: conv_ar_context car;
                                           conv_ar_univ := conv_ar_univ car |}
                                  | inr notar => inr _
                                  end |}
      };
    | fot_view_sort univ := {| is_logical := Universe.is_prop univ;
                               conv_ar := inl {| conv_ar_context := [];
                                                 conv_ar_univ := univ; |} |};
    | fot_view_other T discr with infer Σ wfΣ _ Γ T _ := {
      | exist K princK with inspect (reduce_to_sort wfΣ Γ K _) := {
        | exist (Checked (existT _ univ red_univ)) eq :=
          {| is_logical := Universe.is_prop univ;
             conv_ar := inr _ |};
        | exist (TypeError t) eq := !
        }
    }
  }.

Ltac reduce_term_sound :=
  unfold hnf in *;
  match goal with
  | [H: ?a = reduce_term ?flags ?Σ ?wfΣ ?Γ ?t ?wft |- _] =>
    let r := fresh "r" in
    pose proof (reduce_term_sound flags Σ wfΣ Γ t wft) as [r];
    rewrite <- H in r
  end.

Next Obligation. reduce_term_sound; eauto with erase. Qed.
Next Obligation. reduce_term_sound; eauto with erase. Qed.
Next Obligation.
  reduce_term_sound.
  destruct car as [ctx univ [r']].
  cbn.
  constructor.
  transitivity (tProd na A B); auto.
  now apply red_prod_r.
Qed.
Next Obligation.
  reduce_term_sound.
  contradiction notar.
  apply Is_conv_to_Arity_conv_arity.
  destruct H as [car].
  apply conv_arity_Is_conv_to_Arity in car.
  assert (prod_conv: Is_conv_to_Arity Σ Γ (tProd na A B)).
  { eapply Is_conv_to_Arity_red with T; [easy|].
    rewrite is_hnf.
    apply hnf_sound. }
  destruct prod_conv as [tm [[redtm] ar]].
  destruct wfΣ.
  apply invert_red_prod in redtm; [|easy].
  destruct redtm as (A' & B' & (-> & redAA') & redBB').
  exists B'; easy.
Qed.
Next Obligation. reduce_term_sound; eauto with erase. Qed.
Next Obligation.
  case wfextΣ.
  now intros [].
Qed.
Next Obligation.
  apply tywt; auto.
Qed.
Next Obligation.
  destruct princK as [(typK & princK)].
  destruct isT as [isT].
  destruct wfΣ.
  eapply isType_welltyped.
  eapply validity_term; eauto.
Qed.
Next Obligation.
  clear eq.
  apply not_prod_or_sort_hnf in discr.
  destruct H as [car].
  now apply conv_arity_Is_conv_to_Arity in car.
Qed.
Next Obligation.
  pose proof (PCUICSafeReduce.reduce_to_sort_complete _ _ (eq_sym eq)).
  clear eq.
  apply not_prod_or_sort_hnf in discr.
  destruct isT as [(u&typ)].
  destruct princK as [(typK & princK)].
  specialize (princK _ typ).
  eapply invert_cumul_sort_r in princK as (? & ? & ?).
  eauto.
Qed.

Equations erase_type_discr (t : term) : Prop := {
  | tRel _ := False;
  | tSort _ := False;
  | tProd _ _ _ := False;
  | tApp _ _ := False;
  | tConst _ _ := False;
  | tInd _ _ := False;
  | _ := True
  }.

Inductive erase_type_view : term -> Type :=
| et_view_rel i : erase_type_view (tRel i)
| et_view_sort u : erase_type_view (tSort u)
| et_view_prod na A B : erase_type_view (tProd na A B)
| et_view_app hd arg : erase_type_view (tApp hd arg)
| et_view_const kn u : erase_type_view (tConst kn u)
| et_view_ind ind u : erase_type_view (tInd ind u)
| et_view_other t : erase_type_discr t -> erase_type_view t.

Equations erase_type_viewc (t : term) : erase_type_view t := {
  | tRel i := et_view_rel i;
  | tSort u := et_view_sort u;
  | tProd na A B := et_view_prod na A B;
  | tApp hd arg := et_view_app hd arg;
  | tConst kn u := et_view_const kn u;
  | tInd ind u := et_view_ind ind u;
  | t := et_view_other t _
  }.

Inductive tRel_kind :=
(* tRel refers to type variable n in the list of type vars *)
| RelTypeVar (n : nat)
(* tRel refers to an inductive type (used in constructors of inductives) *)
| RelInductive (ind : inductive)
(* tRel refers to something else, for example something logical or a value *)
| RelOther.

Equations(noeqns) erase_type_aux
          (Γ : context)
          (erΓ : Vector.t tRel_kind #|Γ|)
          (t : term)
          (isT : ∥isType Σ Γ t∥)
          (* The index of the next type variable that is being
             produced, or None if no more type variables should be
             produced (when not at the top level).  For example, in
             Type -> nat we should erase to nat with one type var,
             while in (Type -> nat) -> nat we should erase to (TBox ->
             nat) -> nat with no type vars. *)
          (next_tvar : option nat) : list name × box_type
  by wf ((Γ; t; (tywt isT)) : (∑ Γ t, welltyped Σ Γ t)) erase_rel :=
erase_type_aux Γ erΓ t isT next_tvar
  with inspect (reduce_term RedFlags.nodelta Σ wfΣ Γ t (tywt isT)) :=

  | exist t eq_hnf with is_logical (flag_of_type Γ t _) := {

    | true := ([], TBox);

    | false with erase_type_viewc t := {

      | et_view_rel i with @Vector.nth_order _ _ erΓ i _ := {
        | RelTypeVar n := ([], TVar n);
        | RelInductive ind := ([], TInd ind);
        | RelOther := ([], TAny)
        };

      | et_view_sort _ := ([], TBox);

      | et_view_prod na A B with flag_of_type Γ A _ := {
          (* For logical things we just box and proceed *)
        | {| is_logical := true |} =>
          on_snd
            (TArr TBox)
            (erase_type_aux (Γ,, vass na A) (RelOther :: erΓ)%vector B _ next_tvar);

          (* If the type isn't an arity now, then the domain is a "normal" type like nat. *)
        | {| conv_ar := inr _ |} :=
          let '(_, dom) := erase_type_aux Γ erΓ A _ None in
          on_snd
            (TArr dom)
            (erase_type_aux (Γ,, vass na A) (RelOther :: erΓ)%vector B _ next_tvar);

        (* Ok, so it is an arity. We add type variables for all
           arities (even non-sorts) because more things are typable without
           coercions this way. In particular, type schemes only used
           in contravariant positions extract to something typable
           even without higher-kinded types. For example:
           Definition test (T : Type -> Type) (x : T nat) (y : T bool) : nat := 0.
           Definition bar := test option None None.
           Here [bar] is perfectly extractable without coercions if T becomes a type
           variable. *)

        | _ =>
          let var :=
              match next_tvar with
              | Some i => RelTypeVar i
              | None => RelOther
              end in
          let '(tvars, cod) :=
              erase_type_aux
                (Γ,, vass na A) (var :: erΓ)%vector
                B _
                (option_map S next_tvar) in
          (if next_tvar then binder_name na :: tvars else tvars, TArr TBox cod)
        };

      | et_view_app orig_hd orig_arg with inspect (decompose_app (tApp orig_hd orig_arg)) := {
        | exist (hd, decomp_args) eq_decomp :=

          let hdbt :=
              match hd as h return h = hd -> _ with
              | tRel i =>
                fun _ =>
                  match @Vector.nth_order _ _ erΓ i _ with
                  | RelInductive ind => TInd ind
                  | RelTypeVar i => TVar i
                  | RelOther => TAny
                  end
              | tConst kn _ => fun _ => TConst kn
              | tInd ind _ => fun _ => TInd ind
              | _ => fun _ => TAny
              end eq_refl in

          (* Now for heads that can take args, add args.
             Otherwise drop all args. *)
          if can_have_args hdbt then
            let erase_arg (a : term) (i : In a decomp_args) : box_type :=
                let (aT, princaT) := infer Σ wfΣ _ Γ a _ in
                match flag_of_type Γ aT _ with
                | {| is_logical := true |} => TBox
                | {| conv_ar := car |} =>
                  match is_sort car with
                  | Some conv_sort => snd (erase_type_aux Γ erΓ a _ None)
                  | None => TAny (* non-sort arity or value *)
                  end
                end in
            ([], mkTApps hdbt (map_In decomp_args erase_arg))
          else
            ([], hdbt)
        };

      | et_view_const kn _ := ([], TConst kn);

      | et_view_ind ind _ := ([], TInd ind);

      | et_view_other t _ := ([], TAny)

      }
    }.
Solve All Obligations with
    Tactics.program_simplify;
    CoreTactics.equations_simpl;
    try reduce_term_sound;
    eauto with erase.
Next Obligation.
  reduce_term_sound.
  assert (∥isType Σ Γ (tRel i)∥) as [(s & typ)] by eauto with erase.
  red in typ.
  clear eq_hnf.
  destruct wfΣ.
  eapply subject_reduction in typ; eauto.
  apply inversion_Rel in typ as (? & _ & ? & _); [|easy].
  now apply nth_error_Some.
Qed.
Next Obligation.
  reduce_term_sound; clear eq_hnf.
  destruct isT as [(? & typ)].
  destruct wfΣ.
  eapply subject_reduction in typ; eauto.
  replace (tApp orig_hd orig_arg) with (mkApps (tRel i) decomp_args) in typ; cycle 1.
  { symmetry. apply decompose_app_inv.
    now rewrite <- eq_decomp. }
  apply inversion_mkApps in typ; [|easy].
  destruct typ as (rel_type & rel_typed & spine).
  apply inversion_Rel in rel_typed; [|easy].
  apply nth_error_Some.
  destruct rel_typed as (? & _ & ? & _).
  congruence.
Qed.
Next Obligation. now case wfextΣ; intros [[]]. Qed.
Next Obligation.
  reduce_term_sound; clear eq_hnf.
  destruct isT as [(? & typ)].
  destruct wfΣ.
  eapply subject_reduction in typ; eauto.
  replace (tApp orig_hd orig_arg) with (mkApps hd decomp_args) in typ; cycle 1.
  { symmetry. apply decompose_app_inv.
    now rewrite <- eq_decomp. }
  apply inversion_mkApps in typ; [|easy].
  destruct typ as (? & ? & spine).
  clear -spine i.
  induction spine; [easy|].
  destruct i.
  + subst a.
    econstructor; easy.
  + easy.
Qed.
Next Obligation.
  destruct princaT as [(typ & princaT)].
  destruct wfΣ.
  sq.
  eapply validity_term; [easy|exact typ].
Qed.
Next Obligation.
  destruct princaT as [(typ & princaT)].
  destruct conv_sort as (univ & reduniv).
  destruct wfΣ as [wfΣu].
  sq.
  exists univ.
  eapply type_reduction; [exact typ|easy].
Qed.
Next Obligation.
  reduce_term_sound; clear eq_hnf.
  sq.
  exists (tApp orig_hd orig_arg).
  split; [easy|].
  constructor.
  rewrite <- eq_decomp.
  easy.
Qed.

Definition erase_type (t : term) (isT : ∥isType Σ [] t∥) : list name × box_type :=
  erase_type_aux [] []%vector t isT (Some 0).

Lemma typwt {Γ t T} :
  ∥Σ;;; Γ |- t : T∥ ->
  welltyped Σ Γ t.
Proof.
  intros [typ].
  econstructor; eauto.
Qed.

Inductive erase_type_scheme_view : term -> Type :=
| erase_type_scheme_view_lam na A B : erase_type_scheme_view (tLambda na A B)
| erase_type_scheme_view_other t : negb (isLambda t) -> erase_type_scheme_view t.

Equations erase_type_scheme_viewc (t : term) : erase_type_scheme_view t :=
erase_type_scheme_viewc (tLambda na A B) := erase_type_scheme_view_lam na A B;
erase_type_scheme_viewc t := erase_type_scheme_view_other t _.

Definition type_var_info_of_flag (na : aname) {Γ t} (f : type_flag Γ t) : type_var_info :=
  {| tvar_name := binder_name na;
     tvar_is_logical := is_logical f;
     tvar_is_arity := if is_arity (conv_ar f) then true else false;
     tvar_is_sort := if is_sort (conv_ar f) then true else false; |}.

(* For a non-lambda type scheme, i.e.
   t : T1 -> T2 -> ... -> Tn -> Type
   where t is not a lambda, finish erasing it as a type scheme
   by repeatedly eta expanding it *)
Equations? (noeqns) erase_type_scheme_eta
          (Γ : context)
          (erΓ : Vector.t tRel_kind #|Γ|)
          (t : term)
          (ar_ctx : list arity_ass)
          (ar_univ : Universe.t)
          (typ : ∥Σ;;; Γ |- t : mkNormalArity ar_ctx ar_univ∥)
          (next_tvar : nat) : list type_var_info × box_type :=
erase_type_scheme_eta Γ erΓ t [] univ typ next_tvar => ([], (erase_type_aux Γ erΓ t _ None).2);
erase_type_scheme_eta Γ erΓ t ((na, A) :: ar_ctx) univ typ next_tvar =>
let inf := type_var_info_of_flag na (flag_of_type Γ A _) in
let (kind, new_next_tvar) :=
    if tvar_is_arity inf then
      (RelTypeVar next_tvar, S next_tvar)
    else
      (RelOther, next_tvar) in
let '(infs, bt) := erase_type_scheme_eta
                     (Γ,, vass na A)
                     (kind :: erΓ)%vector
                     (tApp (lift0 1 t) (tRel 0))
                     ar_ctx univ _
                     new_next_tvar in
(inf :: infs, bt).
Proof.
  - destruct typ.
    constructor.
    eexists; eassumption.
  - destruct typ as [typ].
    destruct wfΣ.
    assert (wf_local Σ Γ) by (eapply typing_wf_local; eauto).
    apply validity in typ; auto.
    apply isType_tProd in typ; auto.
    now constructor.
  - clear inf.
    destruct wfΣ.
    destruct typ as [typ].
    apply typing_wf_local in typ as wfl.
    assert (wflext: wf_local Σ (Γ,, vass na A)).
    { apply validity in typ; auto.
      apply isType_tProd in typ as (_ & typ); auto.
      eapply isType_wf_local; eauto. }
    constructor.
    rewrite <- (PCUICSpine.subst_rel0_lift_id 0 (mkNormalArity ar_ctx univ)).
    eapply validity in typ as typ_valid;auto.
    destruct typ_valid as [u Hty].
    eapply type_App.
    + eapply validity in typ as typ;auto.
      eapply (PCUICWeakening.weakening _ _ [_] _ _ _ wflext Hty).
    + eapply (PCUICWeakening.weakening _ _ [_] _ _ _ wflext typ).
    + fold lift.
      eapply (type_Rel _ _ _ (vass na A)); auto.
Qed.

Equations? (noeqns) erase_type_scheme
          (Γ : context)
          (erΓ : Vector.t tRel_kind #|Γ|)
          (t : term)
          (ar_ctx : list arity_ass)
          (ar_univ : Universe.t)
          (typ : ∥Σ;;; Γ |- t : mkNormalArity ar_ctx ar_univ∥)
          (next_tvar : nat) : list type_var_info × box_type :=
erase_type_scheme Γ erΓ t [] univ typ next_tvar => ([], (erase_type_aux Γ erΓ t _ None).2);
erase_type_scheme Γ erΓ t ((na', A') :: ar_ctx) univ typ next_tvar
  with inspect (reduce_term RedFlags.nodelta Σ wfΣ Γ t (typwt typ)) := {
  | exist thnf eq_hnf with erase_type_scheme_viewc thnf := {
    | erase_type_scheme_view_lam na A body =>
      let inf := type_var_info_of_flag na (flag_of_type Γ A _) in
      let (kind, new_next_tvar) :=
          if tvar_is_arity inf then
            (RelTypeVar next_tvar, S next_tvar)
          else
            (RelOther, next_tvar) in
      let '(infs, bt) := erase_type_scheme
                          (Γ,, vass na A) (kind :: erΓ)%vector
                          body ar_ctx univ _ new_next_tvar in
      (inf :: infs, bt);
    | erase_type_scheme_view_other thnf _ =>
      erase_type_scheme_eta Γ erΓ t ((na', A') :: ar_ctx) univ typ next_tvar
    }
  }.
Proof.
  - destruct typ.
    constructor; eexists; eauto.
  - destruct typ as [typ].
    reduce_term_sound.
    destruct wfΣ.
    eapply subject_reduction in r; eauto.
    apply inversion_Lambda in r as (?&?&?&?&?); auto.
    constructor.
    eexists; eassumption.
  - clear inf.
    destruct typ as [typ].
    reduce_term_sound.
    destruct wfΣ.
    eapply subject_reduction in r; eauto.
    apply inversion_Lambda in r as (?&?&?&?&?); auto.
    assert (wf_local Σ Γ) by (eapply typing_wf_local; eauto).
    apply cumul_Prod_inv_l in c as ((?&?)&?); auto.
    constructor.
    clear eq_hnf.
    eapply validity in typ as typ; auto.
    apply isType_tProd in typ as (_ & (u&?)); auto.
    assert (conv_context Σ (Γ,, vass na A) (Γ,, vass na' A')).
    { constructor; [reflexivity|].
      constructor; assumption. }
    eapply type_Cumul.
    + eassumption.
    + eapply context_conversion; eauto.
      eapply typing_wf_local; eassumption.
      now apply conv_context_sym.
    + now eapply cumul_conv_ctx; eauto.
Qed.

Import ExAst.
Equations? (noeqns) erase_constant_decl
          (cst : P.constant_body)
          (wt : ∥on_constant_decl (lift_typing typing) Σ cst∥)
  : constant_body + option (list type_var_info × box_type) :=
erase_constant_decl cst wt with flag_of_type [] (P.cst_type cst) _ := {
  | {| conv_ar := inl car |} with inspect (P.cst_body cst) := {
    | exist (Some body) body_eq =>
      inr (Some (erase_type_scheme [] []%vector body (conv_ar_context car) (conv_ar_univ car) _ 0));
    | exist None _ => inr None
    };
  | {| conv_ar := inr notar |} =>
    inl {| cst_type := erase_type (P.cst_type cst) _; cst_body := erased_body |}
    where erased_body : option term := {
    erased_body with inspect (P.cst_body cst) := {
      | exist (Some body) body_eq => Some (ErasureFunction.erase Σ wfextΣ [] body _);
      | exist None _ => None
      }
    }
  }.
Proof.
  - sq.
    unfold on_constant_decl in wt.
    destruct (P.cst_body cst); cbn in *.
    + eapply validity_term; [easy|exact wt].
    + destruct wt.
      eexists; eassumption.
  - unfold on_constant_decl in wt.
    rewrite <- body_eq in wt.
    cbn in *.
    destruct wt as [wt].
    destruct car as [ctx univ [r]].
    destruct wfΣ.
    eapply type_reduction in wt; eauto.
    constructor; eauto.
  - destruct wt as [wt].
    unfold on_constant_decl in wt.
    rewrite <- body_eq in wt.
    cbn in *.
    econstructor.
    eassumption.
  - clear erased_body.
    destruct wt as [wt].
    destruct wfΣ.
    unfold on_constant_decl in wt.
    destruct (P.cst_body cst).
    + now eapply validity_term in wt; [|now eauto].
    + cbn in wt.
      destruct wt as (s & ?).
      constructor.
      now exists s.
Qed.

Import P.

Equations? (noeqns) erase_ind_arity
          (Γ : context)
          (t : term)
          (isT : ∥isType Σ Γ t∥) : list type_var_info
  by wf ((Γ; t; tywt isT) : (∑ Γ t, welltyped Σ Γ t)) erase_rel :=
erase_ind_arity Γ t isT with inspect (hnf wfΣ Γ t (tywt isT)) := {
  | exist (tProd na A B) hnf_eq =>
    let hd := type_var_info_of_flag na (flag_of_type Γ A _) in
    let tl := erase_ind_arity (Γ,, vass na A) B _ in
    hd :: tl;
  | exist _ _ := []
  }.
Proof.
  all: reduce_term_sound; eauto with erase.
Qed.

Definition ind_aname (oib : P.one_inductive_body) :=
  {| binder_name := nNamed (P.ind_name oib);
     binder_relevance := P.ind_relevance oib |}.

Definition arities_contexts
         (mind : kername)
         (oibs : list P.one_inductive_body) : ∑Γ, Vector.t tRel_kind #|Γ| :=
  (fix f (oibs : list P.one_inductive_body)
       (i : nat)
       (Γ : context) (erΓ : Vector.t tRel_kind #|Γ|) :=
    match oibs with
    | [] => (Γ; erΓ)
    | oib :: oibs =>
      f oibs
        (S i)
        (Γ,, vass (ind_aname oib) (P.ind_type oib))
        (RelInductive {| inductive_mind := mind;
                         inductive_ind := i |} :: erΓ)%vector
    end) oibs 0 [] []%vector.

Lemma arities_contexts_cons_1 mind oib oibs :
  (arities_contexts mind (oib :: oibs)).π1 =
  (arities_contexts mind oibs).π1 ++ [vass (ind_aname oib) (P.ind_type oib)].
Proof.
  unfold arities_contexts.
  match goal with
  | |- (?f' _ _ _ _).π1 = _ => set (f := f')
  end.
  assert (H: forall oibs n Γ erΓ, (f oibs n Γ erΓ).π1 = (f oibs 0 [] []%vector).π1 ++ Γ).
  { clear.
    intros oibs.
    induction oibs as [|oib oibs IH]; [easy|].
    intros n Γ erΓ.
    cbn.
    rewrite IH; symmetry; rewrite IH.
    now rewrite <- List.app_assoc. }
  now rewrite H.
Qed.

Lemma arities_contexts_1 mind oibs :
  (arities_contexts mind oibs).π1 = arities_context oibs.
Proof.
  induction oibs as [|oib oibs IH]; [easy|].
  rewrite arities_contexts_cons_1.
  unfold arities_context.
  rewrite rev_map_cons.
  f_equal.
  apply IH.
Qed.

Inductive view_prod : term -> Type :=
| view_prod_prod na A B : view_prod (tProd na A B)
| view_prod_other t : negb (isProd t) -> view_prod t.

Equations view_prodc (t : term) : view_prod t :=
| tProd na A B => view_prod_prod na A B;
| t => view_prod_other t _.

(* Constructors are treated slightly differently to types as we always
   generate type variables for parameters *)
Equations? (noeqns) erase_ind_ctor
          (Γ : context)
          (erΓ : Vector.t tRel_kind #|Γ|)
          (t : term)
          (isT : ∥isType Σ Γ t∥)
          (next_par : nat)
          (tvars : list type_var_info) : box_type
  by struct tvars :=
erase_ind_ctor Γ erΓ t isT next_par [] := (erase_type_aux Γ erΓ t isT None).2;

erase_ind_ctor Γ erΓ t isT next_par (tvar :: tvars)
  with inspect (reduce_term RedFlags.nodelta Σ wfΣ Γ t (tywt isT)) :=
  | exist t eq_red with view_prodc t := {
    | view_prod_prod na A B =>
      let rel_kind := if tvar_is_arity tvar then RelTypeVar next_par else RelOther in
      let '(_, dom) := erase_type_aux Γ erΓ A _ None in
      let cod := erase_ind_ctor (Γ,, vass na A) (rel_kind :: erΓ)%vector B _ (S next_par) tvars in
      TArr dom cod;
    | view_prod_other _ _ => TAny (* unreachable *)
    }.
Proof. all: reduce_term_sound; eauto with erase. Qed.

Import ExAst.
Definition erase_ind_body
        (mind : kername)
        (mib : P.mutual_inductive_body)
        (oib : P.one_inductive_body)
        (wt : ∥∑i, on_ind_body (lift_typing typing) Σ mind mib i oib∥) : one_inductive_body.
Proof.
  unshelve refine (
  let is_propositional :=
      match destArity [] (ind_type oib) with
      | Some (_, u) => is_propositional u
      | None => false
      end in
  let oib_tvars := erase_ind_arity [] (P.ind_type oib) _ in

  let ctx := inspect (arities_contexts mind (P.ind_bodies mib)) in

  let ind_params := firstn (P.ind_npars mib) oib_tvars in
  let erase_ind_ctor (p : (ident × P.term) × nat) (is_in : In p (P.ind_ctors oib)) :=
      let bt := erase_ind_ctor (proj1_sig ctx).π1 (proj1_sig ctx).π2 p.1.2 _ 0 ind_params in
      let '(ctor_args, _) := decompose_arr bt in
      let fix decomp_names ty :=
          match ty with
          | P.tProd na A B => binder_name na :: decomp_names B
          | P.tLetIn na a A b => decomp_names b
          | _ => []
          end in
      (p.1.1, combine (decomp_names p.1.2) ctor_args) in

  let ctors := map_In (P.ind_ctors oib) erase_ind_ctor in

  let erase_ind_proj (p : ident × P.term) (is_in : In p (P.ind_projs oib)) :=
      (p.1, TBox) (* todo *) in

  let projs := map_In (P.ind_projs oib) erase_ind_proj in

  {| ind_name := P.ind_name oib;
     ind_propositional := is_propositional;
     ind_kelim := P.ind_kelim oib;
     ind_type_vars := oib_tvars;
     ind_ctors := ctors;
     ind_ctor_original_arities := map snd (P.ind_ctors oib);
     ind_projs := projs |}).

  - abstract (
        destruct wt as [wt];
        sq;
        exact (onArity wt.π2)).
  - abstract (
        destruct p as ((?&?)&?);
        cbn in *;
        destruct wt as [[ind_index wt]];
        pose proof (onConstructors wt) as on_ctors;
        unfold on_constructors in *;
        induction on_ctors; [easy|];
        destruct is_in as [->|later]; [|easy];
        constructor;
        destruct (on_ctype r) as (s & typ);
        rewrite <- (arities_contexts_1 mind) in typ;
        cbn in *;
        now exists s).
Defined.

Program Definition erase_ind
        (kn : kername)
        (mib : P.mutual_inductive_body)
        (wt : ∥on_inductive (lift_typing typing) Σ kn mib∥) : mutual_inductive_body :=
  let inds := map_In (P.ind_bodies mib) (fun oib is_in => erase_ind_body kn mib oib _) in
  {| ind_npars := P.ind_npars mib; ind_bodies := inds |}.
Next Obligation.
  apply In_nth_error in is_in.
  destruct is_in as (i & nth_some).
  destruct wt as [wt].
  constructor.
  exists i.
  specialize (onInductives wt).

  change i with (0 + i).
  generalize 0 as n.
  revert i nth_some.

  induction (P.ind_bodies mib) as [|? oibs IH]; intros i nth_some n inds_wt.
  - now rewrite nth_error_nil in nth_some.
  - inversion inds_wt; subst; clear inds_wt.
    destruct i; cbn in *.
    + replace a with oib in * by congruence.
      now rewrite Nat.add_0_r.
    + specialize (IH _ nth_some (S n)).
      now rewrite Nat.add_succ_r.
Qed.

End FixSigmaExt.

Section EraseEnv.
Local Existing Instance extraction_checker_flags.

Import ExAst.

Program Definition erase_global_decl
        (Σext : P.global_env_ext) (wfΣext : ∥wf_ext Σext∥)
        (kn : kername)
        (decl : P.global_decl)
        (wt : ∥on_global_decl (lift_typing typing) Σext kn decl∥) : global_decl :=
  match decl with
  | P.ConstantDecl cst =>
    match erase_constant_decl Σext _ cst _ with
    | inl cst => ConstantDecl cst
    | inr ta => TypeAliasDecl ta
    end
  | P.InductiveDecl mib => InductiveDecl (erase_ind Σext _ kn mib _)
  end.

Fixpoint box_type_deps (t : box_type) : KernameSet.t :=
  match t with
  | TBox
  | TAny
  | TVar _ => KernameSet.empty
  | TArr t1 t2
  | TApp t1 t2 => KernameSet.union (box_type_deps t1) (box_type_deps t2)
  | TInd ind => KernameSet.singleton (inductive_mind ind)
  | TConst kn => KernameSet.singleton kn
  end.

Definition decl_deps (decl : global_decl) : KernameSet.t :=
  match decl with
  | ConstantDecl body =>
    let seen :=
        match cst_body body with
        | Some body => term_global_deps body
        | None => KernameSet.empty
        end in
    KernameSet.union (box_type_deps (cst_type body).2) seen
  | InductiveDecl mib =>
    let one_inductive_body_deps oib :=
        let seen := fold_left (fun seen '(_, bt) => KernameSet.union seen (box_type_deps bt))
                              (flat_map snd (ind_ctors oib))
                              KernameSet.empty in
        fold_left (fun seen bt => KernameSet.union seen (box_type_deps bt))
                  (map snd (ind_projs oib)) seen in
    fold_left (fun seen oib => KernameSet.union seen (one_inductive_body_deps oib))
              (ind_bodies mib)
              KernameSet.empty
  | TypeAliasDecl (Some (nms, ty)) => box_type_deps ty
  | _ => KernameSet.empty
  end.

(* Erase the global declarations by the specified names and their
   non-erased dependencies recursively. Ignore dependencies for which
   [ignore_deps] returnes [true] *)
Program Fixpoint erase_global_decls_deps_recursive
        (Σ : P.global_env)
        (wfΣ : ∥wf Σ∥)
        (include : KernameSet.t)
        (ignore_deps : kername -> bool) : global_env :=
  match Σ with
  | [] => []
  | (kn, decl) :: Σ =>
    let Σext := (Σ, universes_decl_of_decl decl) in
    if KernameSet.mem kn include then
      (* We still erase ignored inductives and constants for two reasons:
         1. For inductives, we want to allow pattern matches on them and we need
         information about them to print names.
         2. For constants, we use their type to do deboxing. *)
      let decl := erase_global_decl Σext _ kn decl _ in
      let with_deps := negb (ignore_deps kn) in
      let new_deps := if with_deps then decl_deps decl else KernameSet.empty in
      let Σer := erase_global_decls_deps_recursive
                   Σ _
                   (KernameSet.union new_deps include) ignore_deps in
      (kn, with_deps, decl) :: Σer
    else
      erase_global_decls_deps_recursive Σ _ include ignore_deps
  end.
Solve Obligations with try now cbn;intros;subst; sq; inversion wfΣ.

End EraseEnv.

Global Arguments is_logical {_ _ _}.
Global Arguments conv_ar {_ _ _}.
Global Arguments is_sort {_ _ _}.
Global Arguments is_arity {_ _ _}.
