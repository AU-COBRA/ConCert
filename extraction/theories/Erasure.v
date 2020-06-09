From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
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
From MetaCoq.PCUIC Require Import PCUICNormal.
From MetaCoq.PCUIC Require Import PCUICPrincipality.
From MetaCoq.PCUIC Require Import PCUICSN.
From MetaCoq.PCUIC Require Import PCUICSR.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICValidity.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.
From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.

Import PCUICEnvTyping.
Import PCUICLookup.

Local Open Scope string_scope.
Import ListNotations.
Import MonadNotation.
Set Equations Transparent.

Module P := PCUICAst.

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
  intros arity_u red.
  induction red; [easy|].
  eapply isArity_red1; eassumption.
Qed.

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

Lemma isWfArity_or_Type_prod_cod Γ na A B :
  ∥ isWfArity_or_Type Σ Γ (tProd na A B) ∥ ->
  ∥ isWfArity_or_Type Σ (Γ,, vass na A) B ∥.
Proof.
  destruct wfΣ as [wfΣu].
  intros [[ar|isT]]; constructor.
  - left.
    apply isWfArity_prod_inv in ar.
    now destruct ar as ((s & typ) & ar).
  - destruct isT as [univ typ].
    apply inversion_Prod in typ; [|easy].
    destruct typ as (? & s & ? & ? & ?).
    right.
    exists s.
    easy.
Qed.

Equations fot_discr (T : term) : Prop :=
fot_discr (tProd _ _ _) := False;
fot_discr (tSort _) := False;
fot_discr _ := True.

Inductive fot_view : term -> Type :=
| fot_view_prod na A B : fot_view (tProd na A B)
| fot_view_sort univ : fot_view (tSort univ)
| fot_view_other t : fot_discr t -> fot_view t.

Equations fot_viewc (t : term) : fot_view t :=
fot_viewc (tProd na A B) := fot_view_prod na A B;
fot_viewc (tSort univ) := fot_view_sort univ;
fot_viewc t := fot_view_other t _.

Lemma watwf {Γ T} (wat : ∥isWfArity_or_Type Σ Γ T∥) : wellformed Σ Γ T.
Proof. now apply wat_wellformed. Qed.

Equations(noeqns) flag_of_type (Γ : context) (T : term) (wat : ∥isWfArity_or_Type Σ Γ T∥)
  : typing_result (type_flag Γ T)
  by wf ((Γ;T; (watwf wat)) : (∑ Γ t, wellformed Σ Γ t)) term_rel :=
flag_of_type Γ T wat with inspect (hnf wfΣ Γ T (watwf wat)) :=
  | exist T is_hnf with fot_viewc T := {
    | fot_view_prod na A B with flag_of_type (Γ,, vass na A) B _ := {
      | Checked flag_cod := ret {| is_logical := is_logical flag_cod;
                                   is_arity := match is_arity flag_cod with
                                               | left isar => left _
                                               | right notar => right _
                                               end;
                                   is_sort := right _ |};
      | TypeError t := TypeError t
      };
    | fot_view_sort univ := ret {| is_logical := Universe.is_prop univ;
                                   is_arity := left _;
                                   is_sort := left _; |};
    | fot_view_other T discr with type_of Σ wfΣ _ Γ T _ := {
      | Checked (existT _ K typK) with reduce_to_sort wfΣ Γ K _ := {
        | Checked (existT _ univ red_univ) :=
          ret {| is_logical := Universe.is_prop univ;
                 is_arity := right _;
                 is_sort := right _; |};
        | TypeError t := TypeError t
        };
      | TypeError t := TypeError t
      }
    }.
Next Obligation.
  pose proof (@hnf_sound _ _ wfΣ _ _ (watwf wat)) as [red_hnf].
  apply isWfArity_or_Type_prod_cod.
  rewrite is_hnf.
  destruct wfΣ, wat.
  sq.
  eapply isWfArity_or_Type_red; [easy|exact red_hnf|easy].
Qed.
Next Obligation.
  pose proof (@hnf_sound _ _ wfΣ Γ T (watwf wat)) as [sound].
  sq.
  exists na, A.
  rewrite is_hnf.
  easy.
Qed.
Next Obligation.
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
  - (* We need to show that T is not convertible to an arity under
       the assumption that hnf of T is neither tProd nor tSort.
       To do this we will need to use some completeness fact about hnf,
       which is not proved in MetaCoq yet, so we defer this proof for now. *)
    exact (todo "not an arity because of discr").
  - destruct isT as [[]].
    now econstructor.
Qed.
Next Obligation.
  destruct typK as [typK].
  apply wat_wellformed; [easy|].
  destruct wfΣ.
  sq.
  eapply validity; [easy|exact typK].
Qed.
Next Obligation.
  exact (todo "also needs discr like above").
Qed.
Next Obligation.
  exact (todo "also needs discr like above").
Qed.

Definition redβιζ : RedFlags.t :=
  {| RedFlags.beta := true;
     RedFlags.iota := true;
     RedFlags.zeta := true;
     RedFlags.delta := false;
     RedFlags.fix_ := true;
     RedFlags.cofix_ := true |}.

Inductive term_sub_ctx : context * term -> context * term -> Prop :=
| sub_prod_dom Γ na A B : term_sub_ctx (Γ, A) (Γ, tProd na A B)
| sub_prod_cod Γ na A B : term_sub_ctx (Γ,, vass na A, B) (Γ, tProd na A B)
| sub_app_arg Γ arg hd arg1 :
    In arg (decompose_app (tApp hd arg1)).2 ->
    term_sub_ctx (Γ, arg) (Γ, tApp hd arg1).

Lemma well_founded_term_sub_ctx : well_founded term_sub_ctx.
Proof.
  Admitted.

Definition erase_type_rel : Relation_Definitions.relation (∑ Γ t, wellformed Σ Γ t) :=
  fun '(Γs; ts; wfs) '(Γl; tl; wfl) =>
    ∥∑m, red Σ Γl tl m × term_sub_ctx (Γs, ts) (Γl, m)∥.

Lemma well_founded_erase_type_rel : well_founded erase_type_rel.
Proof.
  Admitted.
(*
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
  - admit.
  - inversion mred; subst.
    + apply (IH' (p.1,, vass na A, s)).
      * replace p with (p.1, tProd na A s) by (destruct p; cbn in *; congruence).
        cbn.
        constructor.
      * intros y cored wfly.
        cbn in *.
        inversion cored; subst.
        -- eapply IH.
           ++ econstructor.
              rewrite H0.
              apply prod_red_r.
              exact X.
           ++ cbn.
              sq.
              exists (tProd na A y).
              split; [easy|].
              constructor.
        -- eapply IH.
           ++ eapply red_neq_cored; [exact mred|].
        eapply IH.
*)

Instance WellFounded_erase_type_rel : WellFounded erase_type_rel :=
  Wf.Acc_intro_generator 1000 well_founded_erase_type_rel.
Opaque WellFounded_erase_type_rel.

Lemma reduce_term_sr {Γ t red wft s} :
  s = reduce_term red Σ wfΣ Γ t wft ->
  ∥isWfArity_or_Type Σ Γ t∥ ->
  ∥isWfArity_or_Type Σ Γ s∥.
Proof.
  intros -> [wat].
  pose proof (reduce_term_sound red Σ wfΣ Γ t wft) as [redt].
  destruct wfΣ.
  sq.
  eapply isWfArity_or_Type_red; [easy|exact redt|easy].
Qed.

Lemma isWfArity_or_Type_prod_dom_eq Γ t na A B red wft :
  ∥ isWfArity_or_Type Σ Γ t ∥ ->
  tProd na A B = reduce_term red Σ wfΣ Γ t wft ->
  ∥ isWfArity_or_Type Σ Γ A ∥.
Proof.
  intros wat eq.
  pose proof (reduce_term_sr eq wat) as [wat_prod].
  clear wat eq.
  destruct wfΣ as [wfΣu].
  constructor.
  right.
  destruct wat_prod as [ar|isT].
  - apply isWfArity_prod_inv in ar.
    destruct ar as ((s & typ) & ar).
    now econstructor.
  - destruct isT as [univ typ].
    apply inversion_Prod in typ; [|easy].
    destruct typ as (s & ? & ? & ? & ?).
    exists s.
    easy.
Qed.

Lemma isWfArity_or_Type_prod_cod_eq Γ t na A B red wft :
  ∥ isWfArity_or_Type Σ Γ t ∥ ->
  tProd na A B = reduce_term red Σ wfΣ Γ t wft ->
  ∥ isWfArity_or_Type Σ (Γ,, vass na A) B ∥.
Proof.
  intros wat eq.
  pose proof (reduce_term_sr eq wat) as [wat_prod].
  clear wat eq.
  destruct wfΣ as [wfΣu].
  destruct wat_prod as [ar|isT]; constructor.
  - apply isWfArity_prod_inv in ar.
    destruct ar as ((s & typ) & ar).
    now left.
  - destruct isT as [univ typ].
    apply inversion_Prod in typ; [|easy].
    destruct typ as (? & s & ? & ? & ?).
    right.
    exists s.
    easy.
Qed.

Lemma rec_prod_dom Γ t na A B rf wft :
  tProd na A B = reduce_term rf Σ wfΣ Γ t wft ->
  ∥ ∑ r, red Σ Γ t r × term_sub_ctx (Γ, A) (Γ, r) ∥.
Proof.
  intros eq.
  pose proof (reduce_term_sound rf Σ wfΣ Γ t wft) as [red].
  sq.
  exists (tProd na A B).
  split; [rewrite eq; easy|].
  constructor.
Qed.

Lemma rec_prod_cod Γ t na A B rf wft :
  tProd na A B = reduce_term rf Σ wfΣ Γ t wft ->
  ∥ ∑ r, red Σ Γ t r × term_sub_ctx (Γ,, vass na A, B) (Γ, r) ∥.
Proof.
  intros eq.
  pose proof (reduce_term_sound rf Σ wfΣ Γ t wft) as [red].
  sq.
  exists (tProd na A B).
  split; [rewrite eq; easy|].
  constructor.
Qed.

Import VectorDef.VectorNotations.
Open Scope list.

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
(* tRel refers to something else, for example something logical or a
   non-nullary type scheme or a value *)
| RelOther.

Inductive erase_type_error :=
| NotPrenex
| TypingError (te : type_error)
| GeneralError (msg : string).

Definition string_of_erase_type_error (err : erase_type_error) : string :=
  match err with
  | NotPrenex => "Type is not in prenex form"
  | TypingError te => string_of_type_error Σ te
  | GeneralError err => err
  end.

Definition wrap_typing_result
           {T E}
           (tr : typing_result T)
           (f : type_error -> E)
  : result T E :=
  match tr with
  | Checked a => ret a
  | TypeError te => Err (f te)
  end.

(* Marked noeqns until we need to prove things about it to make its
definition faster *)
Equations(noeqns) erase_type
          (Γ : context)
          (erΓ : Vector.t tRel_kind (List.length Γ))
          (t : term)
          (wat : ∥isWfArity_or_Type Σ Γ t∥)
          (tvars : list name)
  : result (list name × box_type) erase_type_error
  by wf ((Γ; t; (watwf wat)) : (∑ Γ t, wellformed Σ Γ t)) erase_type_rel :=
erase_type Γ erΓ t wat tvars with inspect (reduce_term redβιζ Σ wfΣ Γ t (watwf wat)) :=
  | exist t eq_hnf with (f <- flag_of_type Γ t _;; ret (is_logical f)) := {
    | TypeError te := Err (TypingError te);

    | Checked true := ret (tvars, TBox);

    | Checked false with erase_type_viewc t := {

      | et_view_rel i with @Vector.nth_order _ _ erΓ i _ := {
        | RelTypeVar n := ret (tvars, TVar n);
        | RelInductive ind := ret (tvars, TInd ind);
        | RelOther := ret (tvars, TBox)
        };

      | et_view_sort _ := ret (tvars, TBox);

      | et_view_prod na A B with flag_of_type Γ A _ := {
          (* For logical things just box and proceed *)
        | Checked {| is_logical := true |} :=
          '(tvars, bt) <- erase_type (Γ,, vass na A) (RelOther :: erΓ)%vector B _ tvars;;
          ret (tvars, TArr TBox bt);

          (* If the type isn't an arity now, then it's a "normal" type like nat. *)
        | Checked {| is_arity := right _ |} :=
          '(tvars_dom, dom) <- erase_type Γ erΓ A _ tvars;;

          (* If domain added new type vars then it is not in prenex form.
             TODO: We can probably produce something nicer by just erasing to TAny
             in this situation. *)
          (if List.length tvars <? List.length tvars_dom then
             Err NotPrenex
           else
             ret tt);;

          '(tvars, cod) <- erase_type (Γ,, vass na A) (RelOther :: erΓ)%vector B _ tvars;;
          ret (tvars, TArr dom cod);

        (* Ok, so it is an arity. If it is a sort then add a type variable. *)
        | Checked {| is_sort := left _ |} :=
          '(tvars, cod) <- erase_type
                             (Γ,, vass na A) (RelTypeVar (List.length tvars) :: erΓ)%vector
                             B _
                             (tvars ++ [na]);;
          ret (tvars, TArr TBox cod);

        (* Finally this must be a non-nullary non-logical arity.
           This is not in prenex form. *)
        | Checked _ := Err NotPrenex;

        | TypeError te := Err (TypingError te)

        };

      | et_view_app orig_hd orig_arg with inspect (decompose_app (tApp orig_hd orig_arg)) := {
        | exist (hd, decomp_args) eq_decomp :=

          hdbt <- match hd as h return h = hd -> _ with
                  | tRel i =>
                    fun _ =>
                      match @Vector.nth_order _ _ erΓ i _ with
                      | RelInductive ind => ret (TInd ind)
                      | _ => Err (GeneralError ("Unexpected tRel in application in type: "
                                                  ++ string_of_term hd))
                      end
                  | tConst kn _ => fun _ => ret (TConst kn)
                  | tInd ind _ => fun _ => ret (TInd ind)
                  | hd => fun _ => Err (GeneralError ("Unexpected head of application in type: "
                                                        ++ string_of_term hd))
                  end eq_refl;;

          let erase_arg (a : term) (i : In a decomp_args) : result box_type erase_type_error :=
              '(aT; typ) <- wrap_typing_result (type_of Σ wfΣ _ Γ a _) TypingError;;
              ft <- wrap_typing_result (flag_of_type Γ aT _) TypingError;;
              match ft with
              | {| is_logical := true |} => ret TBox
              | {| is_sort := left conv_sort |} =>
                '(tvars_arg, bt) <- erase_type Γ erΓ a _ tvars;;
                if List.length tvars <? List.length tvars_arg then
                  Err NotPrenex
                else
                  ret bt
              | _ => ret TAny (* Arity or value *)
              end in

          let fix erase_args
                  (args : list term) (inc : incl args decomp_args)
                  (r : box_type) : result (list name * box_type) erase_type_error :=
              match args return incl args decomp_args ->
                                result (list name * box_type) erase_type_error with
              | [] => fun _ => ret (tvars, r)
              | a :: args =>
                fun inc =>
                  abt <- erase_arg a _;;
                  erase_args args _ (TApp r abt)
              end inc in

          erase_args decomp_args _ hdbt

        };

      | et_view_const kn _ := ret (tvars, TConst kn);

      | et_view_ind ind _ := ret (tvars, TInd ind);

      | et_view_other t _ := Err (GeneralError ("Unsupported type " ++ string_of_term t))

      }
    }.
Next Obligation. now eapply reduce_term_sr. Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf wat) as [wat_rel].
  destruct wfΣ as [wfΣu].
  destruct wat_rel as [isar|(univ & typ)].
  - now destruct isar as (? & ? & ? & ?).
  - apply inversion_Rel in typ; [|easy].
    apply nth_error_Some.
    destruct typ as (? & _ & ? & _).
    congruence.
Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_dom_eq. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_cod_eq. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_cod_eq. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_dom_eq. Qed.
Next Obligation. now eapply rec_prod_dom. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_cod_eq. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf wat) as [[isar|(univ & typ)]].
  - now destruct isar as (? & ? & ? & ?).
  - unfold PCUICTypingDef.typing in typ.
    replace (tApp orig_hd orig_arg) with (mkApps (tRel i) decomp_args) in typ; cycle 1.
    { symmetry. apply decompose_app_inv.
      now rewrite <- eq_decomp. }
    destruct wfΣ as [wfΣu].
    apply inversion_mkApps in typ; [|easy].
    destruct typ as (rel_type & rel_typed & spine).
    apply inversion_Rel in rel_typed; [|easy].
    apply nth_error_Some.
    destruct rel_typed as (? & _ & ? & _).
    congruence.
Qed.
Next Obligation. now case wfextΣ; intros [[]]. Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf wat) as [[isar|(univ & typ)]].
  - now destruct isar as (? & ? & ? & ?).
  - unfold PCUICTypingDef.typing in typ.
    replace (tApp orig_hd orig_arg) with (mkApps hd decomp_args) in typ; cycle 1.
    { symmetry. apply decompose_app_inv.
      now rewrite <- eq_decomp. }
    destruct wfΣ as [wfΣu].
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
  destruct typ as [typ].
  destruct wfΣ.
  sq.
  eapply validity_term; [easy|exact typ].
Qed.
Next Obligation.
  destruct conv_sort as (univ & reduniv).
  destruct wfΣ as [wfΣu].
  sq.
  right.
  exists univ.
  eapply type_reduction; [easy|exact typ|easy].
Qed.
Next Obligation.
  pose proof (reduce_term_sound redβιζ Σ wfΣ Γ t (watwf wat)).
  sq.
  exists (tApp orig_hd orig_arg).
  split; [rewrite eq_hnf; easy|].
  constructor.
  rewrite <- eq_decomp.
  easy.
Qed.
Next Obligation.
  now specialize (inc a (or_introl eq_refl)).
Qed.
Next Obligation.
  now specialize (inc a0 (or_intror H)).
Qed.

Inductive erase_constant_decl_error :=
| EraseTypeError (err : erase_type_error)
| EraseBodyError (err : type_error).

Definition string_of_erase_constant_decl_error (err : erase_constant_decl_error) : string :=
  match err with
  | EraseTypeError err => string_of_erase_type_error err
  | EraseBodyError err => string_of_type_error Σ err
  end.

Import ExAst.
Program Definition erase_constant_decl
          (cst : P.constant_body)
          (wt : ∥on_constant_decl (lift_typing typing) Σ cst∥)
          : result constant_body erase_constant_decl_error :=
  et <- map_error EraseTypeError (erase_type [] []%vector (P.cst_type cst) _ []);;
  eb <- match P.cst_body cst with
        | Some body =>
          match SafeErasureFunction.erase Σ wfextΣ [] body _ with
          | TypeError te => Err (EraseBodyError te)
          | Checked eb => ret (Some eb)
          end
        | None => ret None
        end;;
  ret {| cst_type := et; cst_body := eb |}.
Next Obligation.
  sq.
  unfold on_constant_decl in wt.
  destruct (P.cst_body cst).
  - cbn in wt.
    eapply validity_term; [easy|exact wt].
  - cbn in wt.
    destruct wt as (s & ?).
    right.
    now exists s.
Qed.
Next Obligation.
  destruct wt as [wt].
  unfold on_constant_decl in wt.
  rewrite <- Heq_anonymous in wt.
  cbn in *.
  now eapply iswelltyped.
Qed.

Import P.

Definition fot_to_oib_tvar (na : name) {Γ t} (f : type_flag Γ t) : oib_type_var :=
  {| tvar_name := na;
     tvar_is_logical := is_logical f;
     tvar_is_arity := if is_arity f then true else false;
     tvar_is_sort := if is_sort f then true else false; |}.

Equations erase_ind_arity
          (Γ : context)
          (t : term)
          (wat : ∥isWfArity_or_Type Σ Γ t∥)
  : typing_result (list oib_type_var)
  by wf ((Γ; t; watwf wat) : (∑ Γ t, wellformed Σ Γ t)) erase_type_rel :=
erase_ind_arity Γ t wat with inspect (hnf wfΣ Γ t (watwf wat)) := {
  | exist (tProd na A B) hnf_eq with flag_of_type Γ A _ := {
    | TypeError te := TypeError te;
    | Checked f with erase_ind_arity (Γ,, vass na A) B _ := {
      | TypeError te := TypeError te;
      | Checked tvars := ret (fot_to_oib_tvar na f :: tvars)
      }
    };
  | exist _ _ := ret []
  }.
Next Obligation. now eapply isWfArity_or_Type_prod_dom_eq. Qed.
Next Obligation. now eapply isWfArity_or_Type_prod_cod_eq. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.

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

Import ExAst.

Inductive erase_ind_body_error :=
| EraseArityError (err : type_error)
| EraseCtorError (ctor : ident) (err : erase_type_error)
| CtorUnmappedTypeVariables (ctor : ident).

Definition string_of_erase_ind_body_error (e : erase_ind_body_error) : string :=
  match e with
  | EraseArityError e => "Error while erasing arity: " ++ string_of_type_error Σ e
  | EraseCtorError ctor e => "Error while erasing ctor "
                               ++ ctor ++ ": "
                               ++ string_of_erase_type_error e
  | CtorUnmappedTypeVariables ctor => "Ctor " ++ ctor ++ " has unmapped type variables"
  end.

Definition monad_map_in
           {T : Type -> Type} {M : Monad T} {A B : Type}
           (l : list A)
           (f : forall (a : A), In a l -> T B) : T (list B) :=
  let fix go (l' : list A) : incl l' l -> T (list B) :=
      match l' return incl l' l -> T (list B) with
      | [] => fun _ => ret []
      | a :: l' =>
        fun (inc : incl (a :: l') l) =>
          b <- f a (inc _ (or_introl eq_refl));;
          tl <- go l' (fun a' a'in => inc _ (or_intror a'in));;
          ret (b :: tl)
      end in
  go l (fun a i => i).

Program Definition erase_ind_body
        (mind : kername)
        (mib : P.mutual_inductive_body)
        (oib : P.one_inductive_body)
        (wt : ∥∑i, on_ind_body (lift_typing typing) Σ mind mib i oib∥)
        : result one_inductive_body erase_ind_body_error :=
  oib_tvars <- wrap_typing_result (erase_ind_arity [] (P.ind_type oib) _) EraseArityError;;

  let '(Γ; erΓ) := arities_contexts mind (P.ind_bodies mib) in

  (* We map type vars in constructors to type vars in the inductive parameters.
     Thus, we only allow the constructor this many type vars. *)
  let num_tvars_in_params :=
      List.length
        (filter
           (fun tvar => negb (tvar_is_logical tvar) && tvar_is_sort tvar)
           (firstn (P.ind_npars mib) oib_tvars)) in

  let erase_ind_ctor (p : (ident × P.term) × nat) (is_in : In p (P.ind_ctors oib)) :=
      let '((name, t), _) := p in
      '(ctor_tvars, bt) <- map_error (EraseCtorError name)
                                     (erase_type Γ erΓ t _ []);;

      (if (#|ctor_tvars| <=? num_tvars_in_params)%nat then
         ret tt
       else
         Err (CtorUnmappedTypeVariables name));;

      let '(ctor_args, _) := decompose_arr bt in
      ret (name, ctor_args) in

  ctors <- monad_map_in (P.ind_ctors oib) erase_ind_ctor;;

  ret {| ind_name := P.ind_name oib;
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
  right.
  destruct (on_ctype r) as (s & typ).
  rewrite <- (arities_contexts_1 mind) in typ.
  rewrite <- Heq_anonymous in typ.
  now exists s.
Qed.

Inductive erase_ind_error :=
| EraseIndBodyError (ind : ident) (err : erase_ind_body_error).

Definition string_of_erase_ind_error (e : erase_ind_error) : string :=
  match e with
  | EraseIndBodyError ind e => "Error while erasing ind body "
                                 ++ ind ++ ": "
                                 ++ string_of_erase_ind_body_error e
  end.

Program Definition erase_ind
        (kn : kername)
        (mib : P.mutual_inductive_body)
        (wt : ∥on_inductive (lift_typing typing) Σ kn mib∥)
        : result mutual_inductive_body erase_ind_error :=
  inds <- monad_map_in
            (P.ind_bodies mib)
            (fun oib is_in =>
               map_error
                 (EraseIndBodyError (P.ind_name oib))
                 (erase_ind_body kn mib oib _));;
  ret {| ind_npars := P.ind_npars mib; ind_bodies := inds |}.
Next Obligation.
  apply In_nth_error in is_in.
  destruct is_in as (i & nth_some).
  destruct wt as [wt].
  constructor.
  exists i.
  specialize (onInductives _ _ _ _ wt).
  revert i nth_some.

  enough (H: forall n i,
             nth_error (P.ind_bodies mib) i = Some oib ->
             Alli (on_ind_body (lift_typing typing) Σ kn mib) n (P.ind_bodies mib) ->
             on_ind_body (lift_typing typing) Σ kn mib (n + i) oib).
  { apply (H 0). }

  induction (P.ind_bodies mib) as [|? oibs IH]; intros n i nth_some inds_wt.
  - now rewrite nth_error_nil in nth_some.
  - inversion inds_wt; subst; clear inds_wt.
    destruct i; cbn in *.
    + replace a with oib in * by congruence.
      now rewrite Nat.add_0_r.
    + specialize (IH (S n)).
      now rewrite Nat.add_succ_r.
Qed.

End FixSigmaExt.

Section EraseEnv.
Local Existing Instance extraction_checker_flags.
Context (ignored : list kername).

Import ExAst.

Inductive erase_global_decl_error :=
| ErrConstant (Σ : global_env_ext) (kn : kername) (err : erase_constant_decl_error)
| ErrInductive (Σ : global_env_ext) (kn : kername) (err : erase_ind_error).

Definition string_of_erase_global_decl_error (e : erase_global_decl_error) : string :=
  match e with
  | ErrConstant Σ kn err => "Error while erasing constant "
                              ++ string_of_kername kn ++ ": "
                              ++ string_of_erase_constant_decl_error Σ err
  | ErrInductive Σ kn err => "Error while erasing inductive "
                               ++ string_of_kername kn ++ ": "
                               ++ string_of_erase_ind_error Σ err
  end.

Program Definition erase_global_decl
        (Σext : P.global_env_ext) (wfΣext : ∥wf_ext Σext∥)
        (kn : kername)
        (decl : P.global_decl)
        (wt : ∥on_global_decl (lift_typing typing) Σext kn decl∥)
  : result global_decl erase_global_decl_error :=
  match decl with
  | P.ConstantDecl cst =>
    cst <- map_error (ErrConstant Σext kn)
                     (erase_constant_decl Σext _ cst _);;
    ret (ConstantDecl cst)
  | P.InductiveDecl mib =>
    ind <- map_error (ErrInductive Σext kn)
                     (erase_ind Σext _ kn mib _);;
    ret (InductiveDecl ind)
  end.

Definition contains (kn : kername) :=
  List.existsb (eq_kername kn).

(* Erase all unignored global declarations *)
Program Fixpoint erase_global_decls (Σ : P.global_env) (wfΣ : ∥wf Σ∥)
  : result global_env erase_global_decl_error :=
  match Σ with
  | [] => ret []
  | (kn, decl) :: Σ =>
    Σer <- erase_global_decls Σ _;;
    if contains kn ignored then
      ret Σer
    else
      let Σext := (Σ, universes_decl_of_decl decl) in
      decl <- erase_global_decl Σext _ kn decl _;;
      ret ((kn, decl) :: Σer)
  end.
Next Obligation. now sq; inversion wfΣ. Qed.
Next Obligation. now sq; inversion wfΣ. Qed.
Next Obligation. now sq; inversion wfΣ. Qed.

Definition add_seen (n : kername) (seen : list kername) : list kername :=
  if existsb (eq_kername n) seen then
    seen
  else
    n :: seen.

Fixpoint Eterm_deps (seen : list kername) (t : term) : list kername :=
  match t with
  | tBox
  | tRel _
  | tVar _ => seen
  | tEvar _ ts => fold_left Eterm_deps ts seen
  | tLambda _ t => Eterm_deps seen t
  | tLetIn _ t1 t2
  | tApp t1 t2 => Eterm_deps (Eterm_deps seen t1) t2
  | tConst n => add_seen n seen
  | tConstruct ind _ => add_seen (inductive_mind ind) seen
  | tCase (ind, _) t brs =>
    let seen := Eterm_deps (add_seen (inductive_mind ind) seen) t in
    fold_left (fun seen '(_, t) => Eterm_deps seen t) brs seen
  | tProj (ind, _, _) t => Eterm_deps (add_seen (inductive_mind ind) seen) t
  | tFix defs _
  | tCoFix defs _ =>
    fold_left (fun seen d => Eterm_deps seen (dbody d)) defs seen
  end.

Fixpoint box_type_deps (seen : list kername) (t : box_type) : list kername :=
  match t with
  | TBox
  | TAny => seen
  | TArr t1 t2
  | TApp t1 t2 => fold_left box_type_deps [t1; t2] seen
  | TVar _ => seen
  | TInd ind => add_seen (inductive_mind ind) seen
  | TConst n => add_seen n seen
  end.

Definition decl_deps (seen : list kername) (decl : global_decl) : list kername :=
  match decl with
  | ConstantDecl body =>
    let seen :=
        match cst_body body with
        | Some body => Eterm_deps seen body
        | None => seen
        end in
    box_type_deps seen (cst_type body).2
  | InductiveDecl mib =>
    let one_inductive_body_deps seen oib :=
        let seen := fold_left box_type_deps
                              (flat_map snd (ind_ctors oib))
                              seen in
        fold_left box_type_deps (map snd (ind_projs oib)) seen in
    fold_left one_inductive_body_deps (ind_bodies mib) seen
  end.

(* Erase the unignored global declarations by the specified names and
   their non-erased dependencies recursively. *)
Program Fixpoint erase_global_decls_deps_recursive
        (Σ : P.global_env) (wfΣ : ∥wf Σ∥)
        (include : list kername)
  : result global_env erase_global_decl_error :=
  match Σ with
  | [] => ret []
  | (kn, decl) :: Σ =>
    if contains kn include && negb (contains kn ignored)  then
      let Σext := (Σ, universes_decl_of_decl decl) in
      decl <- erase_global_decl Σext _ kn decl _;;
      Σer <- erase_global_decls_deps_recursive Σ _ (decl_deps include decl);;
      ret ((kn, decl) :: Σer)
    else
      erase_global_decls_deps_recursive Σ _ include
  end.
Next Obligation. now sq; inversion wfΣ. Qed.
Next Obligation. now sq; inversion wfΣ. Qed.
Next Obligation. now sq; inversion wfΣ. Qed.
Next Obligation. now sq; inversion wfΣ. Qed.

End EraseEnv.

Global Arguments is_logical {_ _ _}.
Global Arguments is_sort {_ _ _}.
Global Arguments is_arity {_ _ _}.
