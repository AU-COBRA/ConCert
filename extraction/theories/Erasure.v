From ConCert.Extraction Require Import StringExtra.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Psatz.
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
Equations(noeqns) flag_of_type (Γ : context) (T : term) (isT : ∥isType Σ Γ T∥) : typing_result (type_flag Γ T)
  by wf ((Γ;T; (isTwf isT)) : (∑ Γ t, wellformed Σ Γ t)) term_rel :=
flag_of_type Γ T isT with inspect (hnf wfΣ Γ T (isTwf isT)) :=
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
Transparent SafeErasureFunction.wf_reduction.

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

Inductive term_sub_ctx : context * term -> context * term -> Prop :=
| sub_prod_dom Γ na A B : term_sub_ctx (Γ, A) (Γ, tProd na A B)
| sub_prod_cod Γ na A B : term_sub_ctx (Γ,, vass na A, B) (Γ, tProd na A B)
| sub_app_arg Γ arg hd arg1 :
    In arg (decompose_app (tApp hd arg1)).2 ->
    term_sub_ctx (Γ, arg) (Γ, tApp hd arg1).

Definition erase_type_rel : Relation_Definitions.relation (∑ Γ t, ∥isType Σ Γ t∥) :=
  fun '(Γs; ts; wfs) '(Γl; tl; wfl) =>
    ∥∑r, red Σ Γl tl r × term_sub_ctx (Γs, ts) (Γl, r)∥.

Lemma well_founded_erase_type_rel : well_founded erase_type_rel.
Proof.
  Admitted.

Instance WellFounded_erase_type_rel : WellFounded erase_type_rel :=
  Wf.Acc_intro_generator 1000 well_founded_erase_type_rel.

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

Lemma isType_prod_dom Γ t na A B red wft :
  ∥ isType Σ Γ t ∥ ->
  tProd na A B = reduce_term red Σ wfΣ Γ t wft ->
  ∥ isType Σ Γ A ∥.
Proof.
  intros isT eq.
  pose proof (reduce_term_sr eq isT) as [(univ & typ)].
  destruct wfΣ as [wfΣu].
  apply inversion_Prod in typ; [|easy].
  destruct typ as (s1 & ? & ? & ? & ?).
  sq.
  now exists s1.
Qed.

Lemma isType_prod_cod Γ t na A B red wft :
  ∥ isType Σ Γ t ∥ ->
  tProd na A B = reduce_term red Σ wfΣ Γ t wft ->
  ∥ isType Σ (Γ,, vass na A) B ∥.
Proof.
  intros isT eq.
  pose proof (reduce_term_sr eq isT) as [(univ & typ)].
  destruct wfΣ as [wfΣu].
  apply inversion_Prod in typ; [|easy].
  destruct typ as (s1 & s2 & ? & ? & _).
  sq.
  now exists s2.
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

Inductive tRel_kind :=
(* tRel refers to type variable n in the list of type vars *)
| rel_type_var (n : nat)
(* tRel refers to an inductive type (used in constructors of inductives) *)
| rel_inductive (ind : inductive)
(* tRel refers to something logical *)
| rel_logical
(* tRel refers to something that is not a type (for example, a
non-nullary type scheme or a value *)
| rel_nontype.

Inductive erase_type_error :=
| NotPrenex
| TypingError (te : type_error)
| GeneralError (msg : string).

Definition wrap_typing_result {A} (tr : typing_result A) : result A erase_type_error :=
  match tr with
  | Checked a => ret a
  | TypeError te => Err (TypingError te)
  end.

Opaque WellFounded_erase_type_rel SafeErasureFunction.wf_reduction.
(* Marked noeqns until we need to prove things about it to make its
definition faster *)
Equations(noeqns) erase_type
          (Γ : context)
          (erΓ : Vector.t tRel_kind (List.length Γ))
          (t : term)
          (isT : ∥isType Σ Γ t∥)
          (tvars : list name)
  : result (list name × box_type) erase_type_error
  by wf ((Γ; t; isT) : (∑ Γ t, ∥isType Σ Γ t∥)) erase_type_rel :=
erase_type Γ erΓ t isT tvars with inspect (reduce_term redβιζ Σ wfΣ Γ t (isTwf isT)) :=
  | exist t eq_hnf with (f <- flag_of_type Γ t _;; ret (is_logical f)) := {
    | TypeError te := Err (TypingError te);

    | Checked true := ret (tvars, TBox);

    | Checked false with erase_type_viewc t := {

      | et_view_rel i with @Vector.nth_order _ _ erΓ i _ := {
        | rel_type_var n := ret (tvars, TVar n);
        | rel_inductive ind := ret (tvars, TInd ind);
        | rel_logical := ret (tvars, TBox);
        | rel_nontype := ret (tvars, TAny) (* unreachable *)
        };

      | et_view_sort _ := ret (tvars, TBox);

      | et_view_prod na A B with flag_of_type Γ A _ := {
          (* For logical things just box and proceed *)
        | Checked {| is_logical := true |} :=
          '(tvars, bt) <- erase_type (Γ,, vass na A) (rel_logical :: erΓ)%vector B _ tvars;;
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

          '(tvars, cod) <- erase_type (Γ,, vass na A) (rel_nontype :: erΓ)%vector B _ tvars;;
          ret (tvars, TArr dom cod);

        (* Ok, so it is an arity. If it is a sort then add a type variable. *)
        | Checked {| is_sort := left _ |} :=
          '(tvars, cod) <- erase_type
                             (Γ,, vass na A) (rel_type_var (List.length tvars) :: erΓ)%vector
                             B _
                             (tvars ++ [na]);;
          ret (tvars, TArr TBox cod);

        (* Finally this must be a non-nullary non-logical arity.
           This is not in prenex form. *)
        | Checked _ := Err NotPrenex;

        | TypeError te := Err (TypingError te)

        };

      | et_view_app orig_hd orig_arg with inspect (decompose_app (tApp orig_hd orig_arg)) := {
        | exist (hd, decomp_args) eq_decomp with erase_app_head hd := {
          | TypeError te := Err (TypingError te);

          | Checked hdbt :=
            let erase_arg (a : term) (i : In a decomp_args) : result box_type erase_type_error :=
                '(aT; typ) <- wrap_typing_result (type_of Σ wfΣ _ Γ a _);;
                ft <- wrap_typing_result (flag_of_type Γ aT _);;
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

          (*
          (* The code below gives a weird error *)
          where erase_args (args : list term) (inc : incl args decomp_args)
                           (result : box_type)
                : typing_result (list name * box_type) :=
          erase_args [] _ r := ret ([], r);
          (* We will fail if the arg is not a type, but let's first check to see if
             it is a logical type scheme, in which case we can get away with boxing
             it. For instance: Say we are processing [sig A P] in
               A : Type, P : A -> Prop |- sig A P : Type.
             The P argument here is not strictly a type, but is rather a type scheme.
             So we get the flag of its type, and box it. *)
          erase_args (a :: args) _ r := abt <- erase_arg a _;;
                                        erase_args args _ (TApp r abt)

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

      | et_view_const kn _ := ret (tvars, TConst kn);

      | et_view_ind ind _ := ret (tvars, TInd ind);

      | et_view_other t _ := Err (GeneralError ("Unsupported type " ++ string_of_term t))

      }
    }.
Next Obligation. now eapply reduce_term_sr. Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf isT) as [(univ & typ)].
  destruct wfΣ as [wfΣu].
  apply inversion_Rel in typ; [|easy].
  apply nth_error_Some.
  destruct typ as (? & _ & ? & _).
  congruence.
Qed.
Next Obligation. now eapply isType_prod_dom. Qed.
Next Obligation. now eapply isType_prod_cod. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation. now eapply isType_prod_cod. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation. now eapply isType_prod_dom. Qed.
Next Obligation. now eapply rec_prod_dom. Qed.
Next Obligation. now eapply isType_prod_cod. Qed.
Next Obligation. now eapply rec_prod_cod. Qed.
Next Obligation. now case wfextΣ; intros [[]]. Qed.
Next Obligation.
  pose proof (reduce_term_sr eq_hnf isT) as [(univ & typ)].
  unfold PCUICTypingDef.typing in typ.
  replace (tApp orig_hd orig_arg) with (mkApps hd decomp_args) in typ; cycle 1.
  { symmetry. apply decompose_app_inv.
    now rewrite <- eq_decomp. }
  destruct wfΣ as [wfΣu].
  apply type_mkApps_inv in typ; [|easy].
  destruct typ as (? & ? & (? & spine) & ?).
  clear -spine i.
  induction spine; [easy|].
  destruct i.
  - subst a.
    econstructor; easy.
  - easy.
Qed.
Next Obligation.
  (* Strategy: Since the app is welltyped, the head must be a product with domain aT,
     it follows that aT is a type. *)
  pose proof (reduce_term_sr eq_hnf isT) as [(univ & typapp)].
  unfold PCUICTypingDef.typing in typapp.
  replace (tApp orig_hd orig_arg) with (mkApps hd decomp_args) in typapp; cycle 1.
  { symmetry. apply decompose_app_inv.
    now rewrite <- eq_decomp. }
  destruct wfΣ as [wfΣu].
  apply type_mkApps_inv in typapp; [|easy].
  destruct typapp as (? & ? & (? & spine) & ?).
  clear -spine i typ wfΣu.
  induction spine; [easy|].
  destruct i.
  - subst a.
    apply isWAT_tProd in i0; [|easy|now eapply typing_wf_local].
    destruct i0 as ((univ & typA) & _).
    destruct typ as [typ].
    unfold PCUICTypingDef.typing in *.
    assert (Σ;;; Γ |- aT <= A) by todo "type_of principality".
    (* TODO: We should have aT <= A : PCUICTerm.tSort univ by using
       type_of_principal. Does this give us aT : PCUICTerm.tSort u for some universe u? *)
    todo "type_of".
  - easy.
Qed.
Next Obligation.
  destruct conv_sort as (univ & reduniv).
  destruct wfΣ as [wfΣu].
  sq.
  exists univ.
  eapply type_reduction.
  - easy.
  - now eapply typing_wf_local.
  - exact typ.
  - easy.
Qed.
Next Obligation.
  pose proof (reduce_term_sound redβιζ Σ wfΣ Γ t (isTwf isT)).
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
Transparent WellFounded_erase_type_rel SafeErasureFunction.wf_reduction.
End FixSigma.

Global Arguments is_logical {_ _ _}.
Global Arguments is_sort {_ _ _}.
Global Arguments is_arity {_ _ _}.
