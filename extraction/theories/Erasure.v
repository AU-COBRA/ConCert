From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require VectorDef.
From Coq Require Import Psatz.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EArities.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import Prelim.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICConfluence.
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

Local Open Scope string_scope.
Import ListNotations.
Import MonadNotation.
Set Equations Transparent.

Module P := PCUICAst.

Section FixSigma.
Local Existing Instance extraction_checker_flags.
Context (Σ : global_env_ext).
Context (wfextΣ : ∥wf_ext Σ∥).
Let wfΣ : ∥wf Σ∥ := ltac:(now sq).


Notation term_rel := (SafeErasureFunction.term_rel Σ).
Instance WellFounded_term_rel : WellFounded term_rel :=
  (SafeErasureFunction.wf_reduction Σ wfΣ).

Inductive term_sub_ctx : context * term -> context * term -> Prop :=
| sub_prod_dom Γ na A B : term_sub_ctx (Γ, A) (Γ, tProd na A B)
| sub_prod_cod Γ na A B : term_sub_ctx (Γ,, vass na A, B) (Γ, tProd na A B)
| sub_app_arg Γ arg hd arg1 :
    In arg (decompose_app (tApp hd arg1)).2 ->
    term_sub_ctx (Γ, arg) (Γ, tApp hd arg1).

(*
Instance WellFounded_term_sub_ctx : WellFounded term_sub_ctx.
Proof.
  Admitted.
  intros (Γl & tl).
  revert Γl.
  induction tl; intros Γl; constructor; intros (Γs & ts) sub; inversion sub; subst; auto.
  cbn in *.
  revert ts sub H0.
  induction (decompose_app_rec tl1 [tl2]).2 eqn:eq using List.rev_ind; [easy|].
  intros ts sub H0.
  SearchAbout (In _ (_ ++ _)).
  apply in_app_or in H0.
  destruct H0.
  - admit.
  - cbn in H.
    destruct H as [->|[]].
    replace ts with tl2; [easy|].
    clear -eq.
    assert (forall (l : list term) a b, [a] = (l ++ [b])%list -> a = b).
    { intros.
      replace l0 with (@nil term) in *.
      - cbn in *.
        now inversion H.
      - symmetry. apply length_zero_iff_nil.
        assert (List.length (l0 ++ [b]) = 1) by (now rewrite <- H).
        rewrite List.app_length in H0.
        cbn in H0.
        lia.
    }
    induction tl1; cbn in *; try solve [now apply H with l].
    clear H.
    destruct l; [inversion eq; auto|].
    inversion eq.
    inversion H1.
  apply app_in in H0.
  destruct H0.
  - subst.
    SearchAbout decompose_app_rec.
  - inversion sub.
*)

(*
Instance foo : WellFounded term_direct_sub_ctx.
Proof.
  intros tl.
  induction tl; try solve [constructor; intros ? sub; inversion sub; auto].
  - constructor.
    intros y sub.
    inversion sub; subst; clear sub; auto.
  - constructor.
    intros
  constructor.
  induction tl; intros ts sub; try solve [inversion sub].
  - inversion sub; subst; clear sub.
    +
  -
*)

Definition erase_type_rel : Relation_Definitions.relation (∑ Γ t, ∥isType Σ Γ t∥) :=
  fun '(Γs; ts; wfs) '(Γl; tl; wfl) =>
    ∥∑r, red Σ Γl tl r × term_sub_ctx (Γs, ts) (Γl, r)∥.

Instance WellFounded_erase_type_rel : WellFounded erase_type_rel.
Proof.
  Admitted.
(*
  intros (Γl & l & wf).
  sq.
  induction (normalisation' _ _ _ wfΣ wf) as [l _ IH].
  induction (WellFounded_term_sub_ctx (Γl, l)) as [? _ IH_sub] in Γl, wf, IH.
  constructor.
  intros (Γs & s & wfs) [(m & redm & sub)].
  inversion sub; subst; clear sub.
*)

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
         (T : Prop, or T a0 .. an : Prop) *)
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

Lemma isTwf {Γ T} (isT : ∥isType Σ Γ T∥) : wellformed Σ Γ T.
Proof. sq. now apply isType_wellformed. Qed.

Opaque SafeErasureFunction.wf_reduction.
Equations flag_of_type (Γ : context) (T : term) (isT : ∥isType Σ Γ T∥) : typing_result (type_flag Γ T)
  by wf ((Γ;T; (isTwf isT)) : (∑ Γ t, wellformed Σ Γ t)) term_rel :=
flag_of_type Γ T isT with inspect (hnf wfΣ Γ T (isTwf isT)) :=
  | exist T is_hnf with fot_viewc T := {
    | fot_view_prod na A B with flag_of_type (Γ,, vass na A) B _ := {
      | Checked flag_cod := ret {| is_logical := is_logical flag_cod;
                                   is_arity := _ ;
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
  pose proof (@hnf_sound _ _ wfΣ _ _ (isTwf isT)) as [red_hnf].
  destruct isT as [[univ typ]].
  destruct wfΣ as [wfΣu].
  assert (prod_ty: Σ;;; Γ |- tProd na A B : tSort univ).
  { apply subject_reduction with T; [easy|easy|].
    rewrite is_hnf.
    apply red_hnf. }
  apply inversion_Prod in prod_ty; [|easy].
  destruct prod_ty as (? & s & ? & ? & ?).
  constructor.
  exists s.
  easy.
Qed.
Next Obligation.
  pose proof (@hnf_sound _ _ wfΣ Γ T (isTwf isT)) as [sound].
  sq.
  exists na, A.
  rewrite is_hnf.
  easy.
Qed.
Next Obligation.
  destruct flag_cod as [logical [ar|not_ar]].
  - left.
    destruct ar as [Bconv [Bred Bar]].
    exists (tProd na A Bconv).
    split; [|easy].
    apply (sq_red_transitivity (tProd na A B)); [rewrite is_hnf; apply hnf_sound|].
    sq.
    now apply red_prod_alt.
  - right.
    intros is_conv.
    contradiction not_ar.
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
  pose proof (@hnf_sound _ _ wfΣ Γ T (isTwf isT)) as [red_prod].
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
  destruct isT as [[]].
  now econstructor.
Qed.
Next Obligation.
  sq.
  apply typing_wellformed with T; [easy| |easy].
  now case wfextΣ; intros [].
Qed.
Next Obligation.
  (* We need to show that T is not convertible to an arity under
     the assumption that hnf of T is neither tProd nor tSort.
     To do this we will need to use some completeness fact about hnf,
     which is not proved in MetaCoq yet, so we defer this proof for now. *)
  destruct wfΣ as [wfΣu].
  apply Is_conv_to_Arity_inv in H; [|easy].
  Admitted.
Next Obligation.
  (* Like above, but we need to short that T is not converible to a sort. *)
  Admitted.

(** OCaml-like types with boxes *)
Inductive box_type :=
| TBox
| TAny
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TVar (_ : nat) (* Index of type variable *)
| TInd (_ : inductive)
| TConst (_ : ident).

Definition isTypeScheme (Γ : context) (t : term) : Type :=
  ∑ (T : term), (Σ;;;Γ |- t : T) * (Is_conv_to_Arity Σ Γ T).

Inductive eraset_input :=
| et_type (Γ : context)
          (t : term)
          (args : list term)
          (isT : ∥isType Σ Γ (mkApps t args)∥)
          (var_map : Vector.t nat (List.length Γ)) (* tRel to TVar map *)
(* Erase a type scheme (which can be nullary, i.e. just a type).
   Note that this eta expands type schemes so they are always fully applied.
   For example, [option] in [Definition foo := option.] is erased to
   [([var1], TApp (TInd "option") (TVar 0))]. *)
| et_type_scheme (Γ : context)
                 (t : term)
                 (isTS : ∥isTypeScheme Γ t∥).

Definition redβιζ : RedFlags.t :=
  {| RedFlags.beta := true;
     RedFlags.iota := true;
     RedFlags.zeta := true;
     RedFlags.delta := false;
     RedFlags.fix_ := true;
     RedFlags.cofix_ := true |}.

Import VectorDef.VectorNotations.
Open Scope list.
  (*
  intros (Γl & l & wf).
  sq.
  induction (normalisation' _ _ _ wfΣ wf) as [l _ IH].
  induction (well_founded_term_subterm l) as [l _ IH_sub] in Γl, wf, IH.
  constructor.
  intros (Γs & s & wfs) [(m & redm & sub)].
  induction sub.
  - admit.
  - apply IHsub1.
  inversion redm; subst; clear redm.
  - apply IH_sub; [easy|].
    induction (normalisation' _ _ _ wfΣ wf) as [? _ ?].
  - clear IH_sub.
    induction sub.
    + inversion H; subst; clear H.
      *
    induction (normalisation' _ _ _ wfΣ wfs).

    unfold WellFounded, well_founded in H.
  induction sub.
  - inversion H; subst; clear H.
    +
  assert (wellformed Σ Γl m).
  { now apply red_wellformed with l. }
  enough (Acc erase_type_rel (Γl; m; H)).
  {
  intros (Γm & m & isTm) [(super & redsuper & sub)].
  inversion sub; subst; clear sub.
  - inversion H; subst; clear H.
    + inversion redsuper; subst; clear redsuper.
      *
      apply
  induction sub.
  - inversion H; subst; clear H.
    +
  specialize (IH super _).
*)

Fixpoint mk_apps_bt (t : box_type) (l : list box_type) :=
  match l with
  | [] => t
  | u :: l' => mk_apps_bt (TApp t u) l'
  end.

Definition app_argsM {T : Type -> Type} `{Monad T} {A} (f : P.term -> T A) :=
  fix go (t : P.term) :=
    match t with
    | P.tApp t1 t2 =>
      hd <- f t2 ;;
      tl <- go t1 ;;
      ret (hd :: tl)
    | _ => ret []
    end.

Definition check_tvars_empty (tvars : list name) (t : term) : typing_result unit :=
  match tvars with
  | [] => ret tt
  | _ => TypeError (Msg ("Unsupported type " ++ string_of_term t))
  end.

(*
(* A check_isType that uses retyping *)
Program Definition check_isType Γ t (wt : welltyped Σ Γ t) : typing_result (∥isType Σ Γ t∥) :=
  '(ty; typ) <- type_of Σ wfΣ _ Γ t wt;;
  '(univ; red) <- reduce_to_sort wfΣ Γ ty _;;
  ret _.
Next Obligation.
  now destruct wfextΣ as [[]].
Qed.
Next Obligation.
  sq.
  apply typing_wellformed with t.
  - easy.
  - now destruct wfextΣ as [[]].
  - easy.
Qed.
Next Obligation.
  sq.
  exists x.
  eapply type_reduction; try easy.
  eapply typing_wf_local; easy.
Qed.
*)

Lemma reduce_term_sr {Γ t red wft s} :
  s = reduce_term red Σ wfΣ Γ t wft ->
  ∥isType Σ Γ t∥ ->
  ∥isType Σ Γ s∥.
Proof.
  intros -> [(univ & ?)].
  pose proof (reduce_term_sound red Σ wfΣ Γ t wft) as [redt].
  destruct wfΣ as [wfΣu].
  constructor.
  exists univ.
  now apply subject_reduction with t.
Qed.

Lemma decompose_app_rec_acc_app_full t l l' :
  (decompose_app_rec t (l ++ l')).2 = (decompose_app_rec t l).2 ++ l'.
Proof.
  revert l l'.
  induction t; try easy.
  intros l l'.
  cbn.
  now rewrite app_comm_cons.
Qed.

Lemma decompose_app_rec_acc_app t l :
  (decompose_app_rec t l).2 = (decompose_app_rec t []).2 ++ l.
Proof.
  apply (decompose_app_rec_acc_app_full _ [] l).
Qed.

Definition erase_app_head (t : term) : typing_result box_type :=
  match t with
  | tConst nm _ => ret (TConst nm)
  | tInd ind _ => ret (TInd ind)
  | _ => TypeError (Msg ("Unsupported head in decomposed application "
                           ++ string_of_term t))
  end.

Fixpoint mkApps_bt (head : box_type) (l : list box_type) : box_type :=
  match l with
  | [] => head
  | x :: xs => mkApps_bt (TApp head x) xs
  end.

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

Equations erase_type
          (Γ : context)
          (t : term)
          (isT : ∥isType Σ Γ t∥)
          (var_map : Vector.t nat (List.length Γ)) (* tRel to TVar map *)
  : typing_result (list name × box_type)
  by wf ((Γ; t; isT) : (∑ Γ t, ∥isType Σ Γ t∥)) erase_type_rel :=
erase_type Γ t isT var_map with inspect (reduce_term redβιζ Σ wfΣ Γ t (isTwf isT)) :=
  (* matching on flag_of_type directly causes issues for some reason *)
  | exist thnf eq_hnf with flag_of_type Γ thnf _ := {
    | TypeError te := TypeError te;

    | Checked {| is_logical := true |} := ret ([], TBox);

    | Checked _ with erase_type_viewc thnf := {

      | et_view_rel i := ret ([], TVar (@Vector.nth_order _ _ var_map i _));

      | et_view_sort _ := ret ([], TBox);

      | et_view_prod na A B with erase_type Γ A _ var_map := {
        | TypeError te := TypeError te;

        | Checked ([], dom) with erase_type (Γ,, vass na A) B _ (0 :: var_map)%vector := {
          | TypeError te := TypeError te;
          | Checked (tvars, cod) := ret (na :: tvars, TArr dom cod)
          };

        | Checked _ := TypeError (Msg "Type is not in prenex form")
        };

      | et_view_app orig_hd orig_arg with inspect (decompose_app (tApp orig_hd orig_arg)) := {
        | exist (hd, decomp_args) _ with erase_app_head hd := {
          | TypeError te := TypeError te;

          | Checked hdbt :=

            let erase_arg (a : term) (i : In a decomp_args) : typing_result box_type :=
                '(aT; typ) <- type_of Σ wfΣ _ Γ a _;;
                ft <- flag_of_type Γ aT isTy;;
                match ft with
                | {| is_logical := true |} => ret TBox
                | {| is_sort := left _ |} =>
                  '(tvars, bt) <- erase_type Γ a _ var_map;;
                  match tvars with
                  | [] => ret bt
                  | _ => TypeError (Msg ("Type is not in prenex form"))
                  end
                | _ =>
                  TypeError (Msg ("Cannot erase argument; "
                                    ++ "it is not a type or logical type scheme "
                                    ++ string_of_term a))
                end in

            (fix erase_args
                 (args : list term) (inc : incl args decomp_args)
                 (result : box_type) : typing_result (list name * box_type) :=
               match args with
               | [] => ret ([], result)
               | a :: args =>
                 abt <- erase_arg a _;;
                 erase_args args _ (TApp result abt)
               end) decomp_args _ hdbt

          (* The code below gives a weird error *)
          (*
          where erase_args (args : list term) (inc : incl args decomp_args)
                : typing_result (list box_type) :=
          erase_args [] _ := ret [];
          (* We will fail if the arg is not a type, but let's first check to see if
             it is a logical type scheme, in which case we can get away with boxing
             it. For instance: Say we are processing [sig A P] in
               A : Type, P : A -> Prop |- sig A P : Type.
             The P argument here is not strictly a type, but is rather a type scheme.
             So we get the flag of its type, and box it. *)
          erase_args (a :: args) _ := abt <- erase_arg a _;;
                                      argsbt <- erase_args args _;;
                                      ret (abt :: argsbt)

          where erase_arg (a : term) (i : In a decomp_args) : typing_result box_type :=
          erase_arg a i with type_of Σ wfΣ _ Γ a _ := {
            | TypeError te := TypeError te;
            | Checked (aT; typ) with flag_of_type Γ aT _ := {
              | TypeError te := TypeError te;
              | Checked {| is_logical := true |} := ret TBox;
              (* If aT is a sort, then a is a type, so continue erasing it *)
              | Checked {| is_sort := left _ |} with erase_type Γ a _ var_map := {
                | TypeError te := TypeError te;
                | Checked ([], bt) := ret bt;
                | Checked _ := TypeError (Msg ("Type is not in prenex form"))
                };

              | Checked _ := TypeError (Msg ("Cannot erase argument; "
                                               ++ "it is not a type or logical type scheme "
                                               ++ string_of_term a))
              }
            }
          *)
          }
        };

      | et_view_const kn _ := ret ([], TConst kn);

      | et_view_ind ind _ := ret ([], TInd ind);

      | et_view_other t _ := TypeError (Msg ("Unsupported type "
                                               ++ string_of_term t))

      }
  }.
Next Obligation.
  now eapply reduce_term_sr.
Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf isT) as [(univ & typ)].
  destruct wfΣ as [wfΣu].
  apply inversion_Rel in typ; [|easy].
  apply nth_error_Some.
  destruct typ as (? & _ & ? & _).
  congruence.
Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf isT) as [(univ & typ)].
  destruct wfΣ as [wfΣu].
  apply inversion_Prod in typ; [|easy].
  destruct typ as (s1 & _ & ? & _ & _).
  sq.
  now exists s1.
Qed.
Next Obligation.
  pose proof (reduce_term_sound redβιζ Σ wfΣ Γ t (isTwf isT)) as [red].
  sq.
  exists (tProd na A B).
  split; [rewrite eq_hnf; easy|].
  constructor.
Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf isT) as [(univ & typ)].
  destruct wfΣ as [wfΣu].
  apply inversion_Prod in typ; [|easy].
  destruct typ as (s1 & s2 & ? & ? & _).
  sq.
  now exists s2.
Qed.
Next Obligation.
  pose proof (reduce_term_sound redβιζ Σ wfΣ Γ t (isTwf isT)) as [red].
  sq.
  exists (tProd na A B).
  split; [rewrite eq_hnf; easy|].
  constructor.
Qed.
Next Obligation.
  now case wfextΣ; intros [[]].
Qed.
Next Obligation.
  Admitted.
Next Obligation.
  destruct typ as [typ].
  apply validity_term in typ.
  SearchAbout welltyped.
  SearchAbout (tSort _).
  SearchAbout validity.
  SearchAbout Is_conv_to_Arity.
Next Obligation.
  pose proof (reduce_term_sound redβιζ Σ wfΣ Γ t (isTwf isT)).
  sq.
  exists (tApp hd0 arg).
  split.
  - now rewrite wildcard.
  - constructor.
    cbn.
    rewrite decompose_app_rec_acc_app.
    now apply in_or_app; right; constructor.
Qed.

    exist (tRel i) _ _ := Checked ([], TVar (@Vector.nth_order _ _ var_map i _));
    erase

  | exist (tRel i) _ := Checked ([], TVar (@Vector.nth_order _ _ var_map i _));
  | exist (tSort _) _ := Checked ([], TBox);
  | exist (tProd na A B) _ with flag_of_type Γ A _ := {
    | Checked {| is_logical := false; is_arity := right _ |}
      (* Domain is a simple type (like [nat]), erase codomain first. *)
      with erase_type (Γ,, vass na A) B _ (0 :: var_map)%vector) := {
      | Checked (tvars, TBox) := Checked (tvars, TBox)
  }.




Equations eraset (input : eraset_input)
  : typing_result (list name × box_type)
  by wf input eraset_input_rel :=
eraset (et_type Γ t args isT var_map)
  with inspect (reduce_term redβιζ Σ wfΣ Γ t _) := {
  | exist (tRel i) _ := Checked ([], TVar (@Vector.nth_order _ _ var_map i _));
  | exist (tApp hd arg) _ := eraset (et_type Γ hd (arg :: args) _ var_map);
  | exist (tSort _) _ := Checked ([], TBox);
  | exist (tProd na A B) _ with flag_of_type Γ A _ := {
    | Checked {| is_logical := false; is_arity := right _ |}
      (* domain is a simple type like nat, erase codomain first *)
      with eraset (et_type (Γ,, vass na A) B [] _ (0 :: var_map)%vector) := {
      | Checked (tvars, TBox) := Checked (tvars, TBox);
      | Checked (tvars, cod) with eraset (et_type Γ A [] _ var_map) := {
        | Checked ([], dom) := Checked (tvars, TArr dom cod);
        | Checked _ := TypeError (Msg "Type is not in prenex normal form");
        | TypeError m := TypeError m
        };
      | TypeError m := TypeError m
      };
    | _ := todo "rest"
    };
  | exist _ _ := todo "rest"
  };
eraset (et_type_scheme Γ t isTS) := todo "rest".


(* Erase the type (mkApps t args). *)
Equations erase_type
          (Γ : context)
          (t : term)
          (args : list term)
          (isT : ∥isType Σ Γ (mkApps t args)∥)
          (var_map : Vector.t nat (length Γ)) (* TRel to TVar map *)
          (names : list name)
  : typing_result (list name * box_type) :=
erase_type Γ t args isT with inspect (reduce_term red_beta_iota_zeta wfΣ Γ t _) := {
  | exist (tRel i) _ := TVar (@Vector.nth_order _ _ var_map i _);
  | exist (tApp head arg) _ := erase_type Γ head (arg :: args) _ var_map names;
  | exist (tSort _) _ := TBox;
  | exist (tProd na A B) _ with flag_of_type Γ A _ := {
    | Checked f

(* Erase the type (mkApps t args) *)
where aux (Γ : context) (t : term) (args : list term) (isT : ∥isType Σ Γ (mkApps t args)∥)
         : typing_result (list name * box_type) :=
aux Γ t args isT with inspect (hnf

Lemma isTSwf {Γ t} (isTS : ∥isTypeScheme Γ t∥) : wellformed Σ Γ t.
Proof.
  destruct isTS as [[]].
  left.
  now econstructor.
Qed.

(* Erase a type scheme (which can be nullary, i.e. just a type).
   Note that this eta expands type schemes so they are always fully applied.
   For example, [option] in [Definition foo := option.] is erased to
   [([var1], TApp (TInd "option") (TVar 0))]. *)
Equations erase_type_scheme
          (Γ : context)
          (t : term)
          (isTS : ∥isTypeScheme Γ t∥) : typing_result (list name * box_type) :=
erase_type_scheme Γ t isTS with inspect (hnf Σ wfΣ Γ t (isTSwf isTS)) := {
  | exist (tApp head arg) _ with erase_type_scheme Γ head _ := {
    | Checked ((nahd :: natl), head) :=

Inductive eraset_input :=
| eraset_type (Γ : context)
              (t : term)
              (args : list term)
              (isT : ∥isType Σ Γ (mkApps t args)∥)
(* Erase a type scheme (which can be nullary, i.e. just a type).
   Note that this eta expands type schemes so they are always fully applied.
   For example, [option] in [Definition foo := option.] is erased to
   [([var1], TApp (TInd "option") (TVar 0))]. *)
| eraset_type_scheme (Γ : context)
                     (t : term)
                     (isTS : ∥isTypeScheme Γ t∥).


Equations erase_type_scheme


Equations eraset (input : eraset_input) : typing_result (list name * box_type)

Equations erase_type_scheme
          (Γ : context)
          (t : term)
          (isTS : ∥isTypeScheme Γ t∥) : typing_result (list name * box_type) :=
erase_type_scheme

Axiom actually_isType : forall {Γ ty} (wt : welltyped Σ Γ ty), ∥isType Σ Γ ty∥.

(** The type erasure procedure. It produces a list of names used to bind type variables and a prenex type with some parts (corresponding to quantification over types and propositions) replaced with boxes. Fails for types that are not prenex or non-extractable dependent types (e.g. containing constructors of inductive types) *)
Program Fixpoint erase_type
           (Γ : context)
           (db : list (option nat)) (* for reindexing tRels in types *)
           (names : list name) (* names of the binders in [tProd] for further printing *)
           (j : nat) (* how many binders we are under *)
           (l_arr : bool) (* [true] is we are erasing a domain of the function type*)
           (ty : P.term)
           (* TODO: we need to pass [isType] instead, but this requires to
             implement the function in a different way *)
           (Hty : welltyped Σ Γ ty)
  : typing_result (list name * box_type) :=
  match flag_of_type Γ ty (actually_isType Hty) with
  | Checked (Some r) => ret (names, TBox r)
  | TypeError (NotASort _) (* TODO: figure out how to get rid of this case*)
  | Checked None =>
    match ty with
    | P.tRel i =>
      (* we use well-typedness to provide a witness that there is something in the context *)
      let v := safe_nth Γ (exist i _) in
      match (nth_error db i) with
      | Some (Some n) => ret (names, TVar n)
      | Some None => TypeError (Msg ("Variable " ++ string_of_name v.(decl_name) ++ " is not translated. Probably not a prenex type"))
      | _ => TypeError (Msg ("Variable " ++ string_of_name v.(decl_name) ++ " is not found in the translation context"))
      end
    | P.tSort _ => ret (names,TBox E.ER_type)
    | P.tProd na t b =>
      let wt_t := _ in
      let wt_b := _ in
      ft <- flag_of_type Γ t wt_t ;;
      match flag_of_type (P.vass na t :: Γ) b wt_b with
          | Checked (Some _) => ret (names, TBox E.ER_type)
          | Checked None =>
            (* we pass [true] flag to indicate that we translate the domain *)
            '(nms1, t1) <- erase_type Γ db names j true t wt_t ;;
            (* if it is a binder for a type variable, e.g [forall A, ...] and we are in the codomain, we add current variable to the translation context [db], otherwise, we add [None], because it's either not a binder for a type variable or the type is not prenex. This guarantees that non-prenex types will fail *)
            let db' := if is_arity ft && (negb l_arr) then Some j :: db
                       else None :: db in
            (* we only count binders for type variables *)
            let j' := if is_arity ft then (1+j)%nat else j in
            '(nms2, t2) <- erase_type (P.vass na t :: Γ) db' names j' l_arr b wt_b ;;
            (* we keep track of the binders for types *)
            let names' := if is_arity ft then (nms1++ [na] ++ nms2)%list
                          else (nms1 ++ nms2)%list in
            ret (names', TArr t1 t2)
          | TypeError te => TypeError te
      end
    | P.tApp t1 t2 =>
      '(nms1, t1') <- erase_type Γ db names j l_arr t1 _ ;;
      '(nms2,t2') <- erase_type Γ db names j l_arr t2 _ ;;
      ret (nms1 ++ nms2, TApp t1' t2')%list
    | P.tInd ind _ =>
      decl <- lookup_ind_decl ind ;;
      let oib := projT1 (projT2 decl) in
      ret (names,TInd ind)
    | P.tLambda na t b => (* NOTE: assume that this is a type scheme, meaning that applied to enough args it ends up a type *)
      erase_type (P.vass na t :: Γ) db names j l_arr b _
    | P.tConst nm _ =>
      (* NOTE: since the original term is well-typed (need also to be a type!), we know that the constant, applied to enough arguments is a valid type (meaning that the constant is a type scheme), so, we just leave the constant name in the erased version *)
      ret (names, TConst nm)
    | P.tEvar _ _  | P.tCase _ _ _ _ | P.tProj _ _
    | P.tFix _ _ | P.tCoFix _ _ | P.tVar _ | P.tLetIn _ _ _ _
    | P.tConstruct _ _ _ => TypeError (Msg ("Not supported type: " ++ string_of_term ty))
    end
  | TypeError te => TypeError te
  end.
Solve Obligations with
    ((intros;subst;
    try clear dependent filtered_var;
    try clear dependent filtered_var0;
    try clear dependent Heq_anonymous;
     try clear dependent Heq_anonymous0);try solve_erase;try easy).
Next Obligation.
  sq'. inversion Hty as [? X]. eapply inversion_Rel in X as (? & ? & ? & ?);eauto.
  apply nth_error_Some;easy.
Qed.
Next Obligation. easy. Qed.
Next Obligation.
  clear dependent Heq_anonymous;solve_erase.
Qed.
Next Obligation.
  sq'. inversion Hty as [? X]. eapply inversion_Rel in X as (? & ? & ? & ?);eauto.
  apply nth_error_Some;easy.
Qed.
Next Obligation. easy. Qed.
Next Obligation.
  clear dependent Heq_anonymous;solve_erase.
Qed.

Record one_inductive_body :=
  {
    ind_name : ident;
    ind_type_parameters : list name;
    ind_ctors : list (ident * list D.box_type);

End FixSigma.
