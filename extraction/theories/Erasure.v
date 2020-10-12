From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import StringExtra.
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
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICConfluence.
From MetaCoq.PCUIC Require Import PCUICConversion.
From MetaCoq.PCUIC Require Import PCUICCumulativity.
From MetaCoq.PCUIC Require Import PCUICElimination.
From MetaCoq.PCUIC Require Import PCUICGeneration.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require Import PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICNormal.
From MetaCoq.PCUIC Require Import PCUICPrincipality.
From MetaCoq.PCUIC Require Import PCUICReduction.
From MetaCoq.PCUIC Require Import PCUICSN.
From MetaCoq.PCUIC Require Import PCUICSR.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
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

Opaque SafeErasureFunction.wf_reduction.
Opaque reduce_term.

Notation term_rel := (SafeErasureFunction.term_rel Σ).
Instance WellFounded_term_rel : WellFounded term_rel :=
  (SafeErasureFunction.wf_reduction Σ wfΣ).

Definition Is_conv_to_Sort Γ T : Prop :=
  exists univ, ∥red Σ Γ T (tSort univ)∥.

(* type_flag of a term indexed by the term's type. For example, for
      t    :   T
   eq_refl : 5 = 5 : Prop
   we would pass T to flag_of_type below, and it would give
   is_logical = true, is_arity = false. On the other hand, for
   (fun (X : Type) => X) : Type -> Type
   we would pass Type -> Type and get is_logical = false, is_arity = true.
*)
Record type_flag {Γ T} :=
  build_flag
    { (* Type is proposition when fully applied, i.e. either
         (T : Prop, or T a0 .. an : Prop). If this is an arity,
         indicates whether this is a logical arity (i.e. into Prop). *)
      is_logical : bool;
      (* Term is a type scheme, i.e. type is an arity.
         T = SProp/Type/Prop or ... -> SProp/Type/Prop *)
      is_arity : {Is_conv_to_Arity Σ Γ T} + {~Is_conv_to_Arity Σ Γ T};
      (* Term is a type, i.e. type is a sort. *)
      is_sort : {Is_conv_to_Sort Γ T} + {~Is_conv_to_Sort Γ T};
    }.

Global Arguments type_flag : clear implicits.

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

Lemma isType_red Γ t t' :
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

Hint Resolve isType_red : erase.

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

Lemma isType_isWfArity_or_Type Γ t :
  ∥isType Σ Γ t∥ ->
  ∥isWfArity_or_Type Σ Γ t∥.
Proof.
  intros [isT].
  now constructor; right.
Qed.

Hint Resolve isType_isWfArity_or_Type : erase.

Lemma isWfArity_or_Type_red Γ t t' :
  ∥isWfArity_or_Type Σ Γ t∥ ->
  ∥red Σ Γ t t'∥ ->
  ∥isWfArity_or_Type Σ Γ t'∥.
Proof.
  intros.
  sq.
  eapply isWfArity_or_Type_red; eauto.
Qed.

Hint Resolve isWfArity_or_Type_red : erase.

Lemma isWfArity_or_Type_prod_dom Γ na A B :
  ∥ isWfArity_or_Type Σ Γ (tProd na A B) ∥ ->
  ∥ isType Σ Γ A ∥.
Proof.
  destruct wfΣ as [wfΣu].
  intros [[ar|isT]].
  - constructor.
    apply isWfArity_prod_inv in ar as ((s & ?) & _).
    now exists s.
  - pose proof (isType_prod_dom _ _ _ _ (sq isT)).
    now sq.
Qed.

Hint Resolve isWfArity_or_Type_prod_dom : erase.

Lemma isWfArity_or_Type_prod_cod Γ na A B :
  ∥ isWfArity_or_Type Σ Γ (tProd na A B) ∥ ->
  ∥ isWfArity_or_Type Σ (Γ,, vass na A) B ∥.
Proof.
  destruct wfΣ as [wfΣu].
  intros [[ar|isT]].
  - constructor; left.
    apply isWfArity_prod_inv in ar.
    now destruct ar as ((s & typ) & ar).
  - pose proof (isType_prod_cod _ _ _ _ (sq isT)).
    sq.
    now right.
Qed.

Hint Resolve isWfArity_or_Type_prod_cod : erase.

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
  (* We need to use the fact that hnf produces a normal form,
     but this is not proven in MetaCoq yet, so we admit this for now. *)
  Admitted.

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

Definition erase_rel : Relation_Definitions.relation (∑ Γ t, wellformed Σ Γ t) :=
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
  induction (normalisation' Σ Γl l wfΣu wfl) as [l _ IH].
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
      1: { eapply red_wellformed in wfl; eauto.
           eapply cored_red in cor as [cor].
           constructor.
           now apply red_prod_l. }
      now apply cored_prod_l.
    + apply Relation_Properties.clos_rtn1_rt in X0.
      unshelve eapply (IH (tProd na s B)).
      3: now repeat econstructor.
      1: { eapply red_wellformed in wfl; eauto.
           constructor.
           etransitivity; [exact X0|].
           now apply red1_red. }
      eapply red_neq_cored.
      { etransitivity; [exact X0|].
        now apply red1_red. }
      intros eq.
      rewrite eq in *.
      eapply cored_red_trans in X0; eauto.
      eapply SafeErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalisation'; eauto.
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
      1: { eapply red_wellformed; eauto.
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
      1: { eapply red_wellformed; eauto.
           constructor.
           etransitivity; [exact X0|].
           now apply red1_red. }
      apply red_neq_cored.
      { etransitivity; [exact X0|].
        now apply red1_red. }
      intros eq.
      rewrite eq in *.
      eapply cored_red_trans in X0; eauto.
      eapply SafeErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalisation'; eauto.
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
      1: { eapply red_wellformed in wfl; eauto.
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
      1: { eapply red_wellformed in wfl; eauto.
           constructor.
           etransitivity; [exact X0|].
           now apply red1_red. }
      apply red_neq_cored.
      { etransitivity; [exact X0|].
        now apply red1_red. }
      intros eq.
      rewrite eq in *.
      eapply cored_red_trans in X0; eauto.
      eapply SafeErasureFunction.Acc_no_loop in X0; [easy|].
      eapply @normalisation'; eauto.
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

Lemma watwf {Γ T} (wat : ∥isWfArity_or_Type Σ Γ T∥) : wellformed Σ Γ T.
Proof. now apply wat_wellformed. Qed.

Equations(noeqns) flag_of_type (Γ : context) (T : term) (wat : ∥isWfArity_or_Type Σ Γ T∥)
  : type_flag Γ T
  by wf ((Γ;T; (watwf wat)) : (∑ Γ t, wellformed Σ Γ t)) erase_rel :=
flag_of_type Γ T wat with inspect (hnf wfΣ Γ T (watwf wat)) :=
  | exist T is_hnf with fot_viewc T := {
    | fot_view_prod na A B with flag_of_type (Γ,, vass na A) B _ := {
      | flag_cod := {| is_logical := is_logical flag_cod;
                       is_arity := match is_arity flag_cod with
                                   | left isar => left _
                                   | right notar => right _
                                   end;
                       is_sort := right _ |}
      };
    | fot_view_sort univ := {| is_logical := Universe.is_prop univ;
                               is_arity := left _;
                               is_sort := left _; |};
    | fot_view_other T discr with infer Σ wfΣ _ Γ T _ := {
      | exist K princK with inspect (reduce_to_sort wfΣ Γ K _) := {
        | exist (Checked (existT _ univ red_univ)) eq :=
          {| is_logical := Universe.is_prop univ;
             is_arity := right _;
             is_sort := right _; |};
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
  destruct isar as [Bconv [Bred Bar]].
  exists (tProd na A Bconv).
  split; [|easy].
  apply (sq_red_transitivity (tProd na A B)); [rewrite is_hnf; apply hnf_sound|].
  sq.
  now apply red_prod_alt.
Qed.
Next Obligation.
  contradiction notar.
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
Next Obligation.
  destruct H as [univ [red_sort]].
  pose proof (@hnf_sound _ _ wfΣ Γ T (watwf wat)) as [red_prod].
  rewrite <- is_hnf in red_prod.
  destruct wfΣ as [wfΣu].
  pose proof (red_confluence wfΣu red_sort red_prod) as (v' & redv'1 & redv'2).
  apply invert_red_sort in redv'1.
  subst.
  apply invert_red_prod in redv'2 as (? & ? & (? & ?) & ?); easy.
Qed.
Next Obligation.
  exists (tSort univ).
  split; [|easy].
  rewrite is_hnf.
  apply hnf_sound.
Qed.
Next Obligation.
  exists univ.
  rewrite is_hnf.
  apply hnf_sound.
Qed.
Next Obligation.
  case wfextΣ.
  now intros [].
Qed.
Next Obligation.
  destruct wat as [[ar|isT]].
  - apply not_prod_or_sort_hnf in discr.
    now apply nIs_conv_to_Arity_isWfArity_elim in discr.
  - destruct isT as [[]].
    now econstructor.
Qed.
Next Obligation.
  destruct princK as [(typK & princK)].
  apply wat_wellformed; [easy|].
  destruct wfΣ.
  sq.
  eapply validity; [easy|exact typK].
Qed.
Next Obligation.
  clear eq.
  now apply not_prod_or_sort_hnf in discr.
Qed.
Next Obligation.
  clear eq.
  apply not_prod_or_sort_hnf in discr.
  contradiction discr.
  destruct H.
  exists (tSort x).
  now split.
Qed.
Next Obligation.
  pose proof (SafeErasureFunction.reduce_to_sort_complete _ (eq_sym eq)).
  clear eq.
  apply not_prod_or_sort_hnf in discr.
  destruct wat as [[|]].
  - now apply nIs_conv_to_Arity_isWfArity_elim in discr.
  - destruct i.
    red in t0.
    destruct princK as [(typK & princK)].
    specialize (princK _ t0).
    eapply invert_cumul_sort_r in princK as (? & ? & ?).
    eauto.
Qed.

Definition redβιζ : RedFlags.t :=
  {| RedFlags.beta := true;
     RedFlags.iota := true;
     RedFlags.zeta := true;
     RedFlags.delta := false;
     RedFlags.fix_ := true;
     RedFlags.cofix_ := true |}.

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

Lemma isTwf {Γ t} (isT: ∥isType Σ Γ t∥) :
  wellformed Σ Γ t.
Proof.
  destruct isT.
  now apply isType_wellformed.
Qed.

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
  by wf ((Γ; t; (isTwf isT)) : (∑ Γ t, wellformed Σ Γ t)) erase_rel :=
erase_type_aux Γ erΓ t isT next_tvar
  with inspect (reduce_term redβιζ Σ wfΣ Γ t (isTwf isT)) :=

  | exist t eq_hnf with (is_logical (flag_of_type Γ t _)) := {

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
        | {| is_arity := right _ |} :=
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
          (if next_tvar then na :: tvars else tvars, TArr TBox cod)
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
                | {| is_sort := left conv_sort |} => snd (erase_type_aux Γ erΓ a _ None)
                | _ => TAny (* Arity or value *)
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
  eapply type_reduction; [easy|exact typ|easy].
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

Inductive erase_constant_decl_error :=
| TypeAliasWithoutBody
| CannotHandleTypeScheme.

Definition string_of_erase_constant_decl_error (err : erase_constant_decl_error) : string :=
  match err with
  | TypeAliasWithoutBody => "Type alias does not have a body"
  | CannotHandleTypeScheme => "Cannot handle type schemes yet"
  end.

Import ExAst.
Equations? (noeqns) erase_constant_decl
          (cst : P.constant_body)
          (wt : ∥on_constant_decl (lift_typing typing) Σ cst∥)
  : result (constant_body + (list name × box_type)) erase_constant_decl_error :=
erase_constant_decl cst wt with flag_of_type [] (P.cst_type cst) _ := {
  | {| is_arity := left isar; is_sort := left issort |} with inspect (P.cst_body cst) := {
    | exist (Some body) body_eq => Ok (inr (erase_type body _));
    | exist None _ => Err (TypeAliasWithoutBody)
    };
  | {| is_arity := left isar; is_sort := right notsort |} => Err CannotHandleTypeScheme;
  | {| is_arity := right notar |} =>
    Ok (inl {| cst_type := erase_type (P.cst_type cst) _;
               cst_body := erased_body |})
    where erased_body : option term := {
    erased_body with inspect (P.cst_body cst) := {
      | exist (Some body) body_eq => Some (SafeErasureFunction.erase Σ wfextΣ [] body _);
      | exist None _ => None
      }
    }
  }.
Proof.
  - sq.
    unfold on_constant_decl in wt.
    destruct (P.cst_body cst).
    + cbn in wt.
      eapply validity_term; [easy|exact wt].
    + cbn in wt.
      destruct wt as (s & ?).
      right.
      now exists s.
  - destruct cst; cbn in *.
    subst cst_body.
    cbn in *.
    destruct issort as (s & [r]).
    sq.
    exists s.
    red.
    eapply type_reduction; eauto.
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
    + eapply validity_term in wt; [|now eauto].
      destruct wt.
      * now apply nIs_conv_to_Arity_isWfArity_elim in notar.
      * now constructor.
    + cbn in wt.
      destruct wt as (s & ?).
      constructor.
      now exists s.
Qed.

Import P.

Definition fot_to_oib_tvar (na : name) {Γ t} (f : type_flag Γ t) : oib_type_var :=
  {| tvar_name := na;
     tvar_is_logical := is_logical f;
     tvar_is_arity := if is_arity f then true else false;
     tvar_is_sort := if is_sort f then true else false; |}.

Equations? (noeqns) erase_ind_arity
          (Γ : context)
          (t : term)
          (wat : ∥isWfArity_or_Type Σ Γ t∥)
  : list oib_type_var
  by wf ((Γ; t; watwf wat) : (∑ Γ t, wellformed Σ Γ t)) erase_rel :=
erase_ind_arity Γ t wat with inspect (hnf wfΣ Γ t (watwf wat)) := {
  | exist (tProd na A B) hnf_eq =>
    let hd := fot_to_oib_tvar na (flag_of_type Γ A _) in
    let tl := erase_ind_arity (Γ,, vass na A) B _ in
    hd :: tl;
  | exist _ _ := []
  }.
Proof.
  all: reduce_term_sound; eauto with erase.
Qed.

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
        (Γ,, vass (nNamed (P.ind_name oib)) (P.ind_type oib))
        (RelInductive {| inductive_mind := mind;
                         inductive_ind := i |} :: erΓ)%vector
    end) oibs 0 [] []%vector.

Lemma arities_contexts_cons_1 mind oib oibs :
  (arities_contexts mind (oib :: oibs)).π1 =
  (arities_contexts mind oibs).π1 ++ [vass (nNamed (P.ind_name oib)) (P.ind_type oib)].
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
          (tvars : list oib_type_var) : box_type
  by struct tvars :=
erase_ind_ctor Γ erΓ t isT next_par [] := (erase_type_aux Γ erΓ t isT None).2;

erase_ind_ctor Γ erΓ t isT next_par (tvar :: tvars)
  with inspect (reduce_term redβιζ Σ wfΣ Γ t (isTwf isT)) :=
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
Program Definition erase_ind_body
        (mind : kername)
        (mib : P.mutual_inductive_body)
        (oib : P.one_inductive_body)
        (wt : ∥∑i, on_ind_body (lift_typing typing) Σ mind mib i oib∥) : one_inductive_body :=
  let oib_tvars := erase_ind_arity [] (P.ind_type oib) _ in

  let '(Γ; erΓ) := arities_contexts mind (P.ind_bodies mib) in

  let ind_params := firstn (P.ind_npars mib) oib_tvars in
  let erase_ind_ctor (p : (ident × P.term) × nat) (is_in : In p (P.ind_ctors oib)) :=
      let '((name, t), _) := p in
      let bt := erase_ind_ctor Γ erΓ t _ 0 ind_params in
      let '(ctor_args, _) := decompose_arr bt in
      (name, ctor_args) in

  let ctors := map_In (P.ind_ctors oib) erase_ind_ctor in

  {| ind_name := P.ind_name oib;
     ind_type_vars := oib_tvars;
     ind_ctors := ctors;
     ind_projs := [] (* todo *) |}.
Next Obligation.
  destruct wt as [wt].
  sq.
  right.
  exact (onArity wt.π2).
Qed.
Next Obligation.
  destruct wt as [[ind_index wt]].
  pose proof (onConstructors wt) as on_ctors.
  unfold on_constructors in *.
  induction on_ctors; [easy|].
  destruct is_in as [->|later]; [|easy].
  constructor.
  destruct (on_ctype r) as (s & typ).
  rewrite <- (arities_contexts_1 mind) in typ.
  rewrite <- Heq_anonymous in typ.
  now exists s.
Qed.

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
  specialize (onInductives _ _ _ _ wt).

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

Inductive erase_global_decl_error :=
| ErrConstant (kn : kername) (err : erase_constant_decl_error).

Definition string_of_erase_global_decl_error (e : erase_global_decl_error) : string :=
  match e with
  | ErrConstant kn err => "Error while erasing constant "
                              ++ string_of_kername kn ++ ": "
                              ++ string_of_erase_constant_decl_error err
  end.

Program Definition erase_global_decl
        (Σext : P.global_env_ext) (wfΣext : ∥wf_ext Σext∥)
        (kn : kername)
        (decl : P.global_decl)
        (wt : ∥on_global_decl (lift_typing typing) Σext kn decl∥)
  : result global_decl erase_global_decl_error :=
  match decl with
  | P.ConstantDecl cst =>
    cst_or_ty_alias <- map_error (ErrConstant kn)
                                 (erase_constant_decl Σext _ cst _);;
    match cst_or_ty_alias with
    | inl cst => ret (ConstantDecl cst)
    | inr ta => ret (TypeAliasDecl ta)
    end
  | P.InductiveDecl mib =>
    ret (InductiveDecl (erase_ind Σext _ kn mib _))
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
        let seen := fold_left (fun seen bt => KernameSet.union seen (box_type_deps bt))
                              (flat_map snd (ind_ctors oib))
                              KernameSet.empty in
        fold_left (fun seen bt => KernameSet.union seen (box_type_deps bt))
                  (map snd (ind_projs oib)) seen in
    fold_left (fun seen oib => KernameSet.union seen (one_inductive_body_deps oib))
              (ind_bodies mib)
              KernameSet.empty
  | TypeAliasDecl (nms, ty) => box_type_deps ty
  end.

(* Erase the global declarations by the specified names and their
   non-erased dependencies recursively. Ignore dependencies for which
   [ignore_deps] returnes [true] *)
Program Fixpoint erase_global_decls_deps_recursive
        (Σ : P.global_env)
        (wfΣ : ∥wf Σ∥)
        (include : KernameSet.t)
        (ignore_deps : kername -> bool)
  : result global_env erase_global_decl_error :=
  match Σ with
  | [] => ret []
  | (kn, decl) :: Σ =>
    let Σext := (Σ, universes_decl_of_decl decl) in
    if KernameSet.mem kn include then
      (* We still erase ignored inductives and constants for two reasons:
         1. For inductives, we want to allow pattern matches on them and we need
         information about them to print names.
         2. For constants, we use their type to do deboxing.
         This is a little hacky as we might fail to erase these and then fail erasure.
         On the other hand, it is unlikely that something remapped has a higher-kinded type
         as we wouldn't be able to remap it to something sane, so this is probably ok. *)
      decl <- erase_global_decl Σext _ kn decl _;;
      let with_deps := negb (ignore_deps kn) in
      let new_deps := if with_deps then decl_deps decl else KernameSet.empty in
      Σer <- erase_global_decls_deps_recursive Σ _ (KernameSet.union new_deps include) ignore_deps;;
      ret ((kn, with_deps, decl) :: Σer)
    else
      erase_global_decls_deps_recursive Σ _ include ignore_deps
  end.
Solve Obligations with try now cbn;intros;subst; sq; inversion wfΣ.

End EraseEnv.

Global Arguments is_logical {_ _ _}.
Global Arguments is_sort {_ _ _}.
Global Arguments is_arity {_ _ _}.
