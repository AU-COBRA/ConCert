From ConCert.Extraction Require Import Annotations.
From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizePropDiscr.
From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import List.
From Coq Require Import VectorDef.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EArities.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require Import PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICGeneration.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICValidity.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.
From MetaCoq.Template Require Import Kernames.

Import VectorNotations.
Import ListNotations.

Open Scope list.
Set Equations Transparent.

Section fix_env.
Opaque flag_of_type erase_type.

Context (Σ : global_env_ext).
Context (wfextΣ : ∥wf_ext Σ∥).
Lemma wfΣ : ∥wf Σ∥.
Proof. now sq. Qed.

Section annotate.
  Context {A : Type}.
  Context (annotate_types :
             forall Γ t (Ht : welltyped Σ Γ t) et (er : erases Σ Γ t et), annots A et).

  Equations? (noeqns) annotate_branches
           Γ
           (brs : list (nat × term))
           (ebrs : list (nat × E.term))
           (wf : Forall2 (fun '(_, t) '(_, et) => welltyped Σ Γ t /\ erases Σ Γ t et) brs ebrs)
    : bigprod (annots A ∘ snd) ebrs by struct ebrs :=
    annotate_branches Γ _ [] _ := tt;
    annotate_branches Γ ((_, t) :: brs) ((_, et) :: ebrs) wf :=
      (annotate_types Γ t _ et _, annotate_branches Γ brs ebrs _);
    annotate_branches _ _ _ _ := !.
  Proof. all: now depelim wf. Qed.

  Equations? (noeqns) annotate_defs
           Γ
           (defs : list (def term))
           (edefs : list (E.def E.term))
           (wf : Forall2 (fun d ed => welltyped Σ Γ (dbody d) /\ erases Σ Γ (dbody d) (E.dbody ed))
                         defs edefs)
    : bigprod (annots A ∘ E.dbody) edefs by struct edefs :=
    annotate_defs Γ _ [] _ := tt;
    annotate_defs Γ (d :: defs) (ed :: edefs) wf :=
      (annotate_types Γ (dbody d) _ (E.dbody ed) _, annotate_defs Γ defs edefs _);
    annotate_defs _ _ _ _ := !.
  Proof. all: now depelim wf. Qed.
End annotate.

Fixpoint vec_repeat {A} (a : A) (n : nat) : Vector.t A n :=
  match n with
  | 0 => []%vector
  | S n => (a :: vec_repeat a n)%vector
  end.

Program Definition erase_type_of Γ t (wt : welltyped Σ Γ t) : box_type :=
  let ty := type_of Σ wfΣ _ Γ t wt in
  let flag := flag_of_type Σ wfextΣ Γ ty _ in
  if conv_ar flag then
    TBox
  else
    (erase_type_aux Σ wfextΣ Γ (vec_repeat RelOther #|Γ|) ty _ None).2.
Next Obligation.
  destruct wfextΣ as [[]].
  now constructor.
Qed.
Next Obligation.
  unfold type_of.
  destruct infer as (ty & [(typ & ?)]).
  cbn.
  destruct wfΣ.
  constructor.
  eapply validity_term; eauto.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct infer as (ty & [(typ & ?)]).
  cbn in *.
  destruct wfΣ.
  eapply validity_term in typ; eauto using sq.
Qed.

Equations? (noeqns) annotate_types
         (Γ : context)
         (t : term) (wt : welltyped Σ Γ t)
         (et : E.term)
         (er : erases Σ Γ t et) : annots box_type et by struct et :=
(* For some reason 'with' hangs forever so we need 'where' here *)
annotate_types Γ t wt et er := annot (erase_type_of Γ t wt) et t wt er
where annot
        (bt : box_type)
        (et : E.term)
        (t : term) (wt : welltyped Σ Γ t)
        (er : erases Σ Γ t et) : annots box_type et := {
annot bt E.tBox _ _ _ => bt;
annot bt (E.tRel _) _ _ _ => bt;
annot bt (E.tVar _) _ _ _ => bt;
annot bt (E.tEvar _ ets) t wt er => !;
annot bt (E.tLambda na eB) (tLambda na' A B) wt er => (bt, annotate_types (Γ,, vass na' A) B _ eB _);
annot bt (E.tLetIn na eb eb') (tLetIn na' b ty b') wt er =>
  (bt, (annotate_types Γ b _ eb _, annotate_types (Γ,, vdef na' b ty) b' _ eb' _));
annot bt (E.tApp ehd earg) (tApp hd arg) wt er =>
  (bt, (annotate_types Γ hd _ ehd _, annotate_types Γ arg _ earg _));
annot bt (E.tConst _) _ wt er => bt;
annot bt (E.tConstruct _ _) _ wt er => bt;
annot bt (E.tCase _ ediscr ebrs) (tCase _ _ discr brs) wt er =>
  (bt, (annotate_types Γ discr _ ediscr _, annotate_branches annotate_types Γ brs ebrs _));
annot bt (E.tProj _ et) (tProj _ t) wt er => (bt, annotate_types Γ t _ et _);
annot bt (E.tFix edefs _) (tFix defs _) wt er =>
  (bt, annotate_defs annotate_types (Γ,,, fix_context defs) defs edefs _);
annot bt (E.tCoFix edefs _) (tCoFix defs _) wt er =>
  (bt, annotate_defs annotate_types (Γ,,, fix_context defs) defs edefs _);
annot bt _ _ wt er => !
}.
Proof.
  all: try solve [inversion er; auto].
  all: destruct wt.
  all: destruct wfextΣ as [[]].
  - depelim er.
    now apply inversion_Evar in X.
  - apply inversion_Lambda in X as (? & ? & ? & ? & ?); auto.
    econstructor; eauto.
  - apply inversion_LetIn in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_LetIn in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_App in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_App in X as (?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_Case in X as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_Case in X as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); auto.
    depelim er.
    clear -a X.
    induction X in x5, a, X |- *; [constructor|].
    depelim a.
    constructor; eauto.
    destruct x, y0.
    destruct r.
    destruct p as ((?&?)&?).
    cbn in *.
    split; [|now auto].
    econstructor; eauto.
  - apply inversion_Proj in X as (?&?&?&?&?&?&?&?&?); auto.
    econstructor; eauto.
  - apply inversion_Fix in X as (?&?&?&?&?&?&?); auto.
    depelim er.
    clear -a0 X.
    eapply All2_All_mix_left in X; eauto.
    clear -X.
    revert X.
    generalize (Γ,,, fix_context defs).
    clear Γ.
    intros Γ a.
    induction a; [now constructor|].
    constructor; [|now eauto].
    destruct r as ((? & ?) & ? & ? & ?).
    split; [|now auto].
    econstructor; eauto.
  - apply inversion_CoFix in X as (?&?&?&?&?&?&?); auto.
    depelim er.
    clear -a0 X.
    eapply All2_All_mix_left in X; eauto.
    clear -X.
    revert X.
    generalize (Γ,,, fix_context defs).
    clear Γ.
    intros Γ a.
    induction a; [now constructor|].
    constructor; [|now eauto].
    destruct r as (? & ? & ? & ?).
    split; [|now auto].
    econstructor; eauto.
Qed.

Definition annotate_types_erase_constant_decl cst wt :
  match erase_constant_decl Σ wfextΣ cst wt with
  | inl cst => constant_body_annots box_type cst
  | _ => unit
  end.
Proof.
  unfold erase_constant_decl.
  destruct flag_of_type.
  cbn in *.
  destruct conv_ar.
  - destruct cst; cbn.
    destruct cst_body; exact tt.
  - destruct cst; cbn.
    destruct cst_body; [|exact tt].
    cbn.
    apply (annotate_types [] t); [|apply ErasureFunction.erases_erase].
    cbn in *.
    destruct wt.
    econstructor; eauto.
Defined.

Definition annotate_types_erase_global_decl kn decl wt :
  global_decl_annots box_type (erase_global_decl Σ wfextΣ kn decl wt).
Proof.
  unfold erase_global_decl.
  destruct decl; [|exact tt].
  cbn.
  pose proof (annotate_types_erase_constant_decl c wt).
  destruct erase_constant_decl; [|exact tt].
  cbn.
  exact X.
Defined.

End fix_env.

Definition annotate_types_erase_global_decls_deps_recursive Σ wfΣ include ignore_deps :
  env_annots box_type (erase_global_decls_deps_recursive Σ wfΣ include ignore_deps).
Proof.
  revert include.
  induction Σ; intros include; [exact tt|].
  cbn in *.
  destruct a.
  destruct KernameSet.mem.
  - cbn.
    match goal with
    | |- context[erase_global_decl ?a ?b ?c ?d ?e] =>
      pose proof (annotate_types_erase_global_decl a b c d e)
    end.
    match goal with
    | |- context[erase_global_decls_deps_recursive _ ?prf ?incl _] =>
      specialize (IHΣ prf incl)
    end.
    exact (X, IHΣ).
  - match goal with
    | |- context[erase_global_decls_deps_recursive _ ?prf ?incl _] =>
      specialize (IHΣ prf incl)
    end.
    exact IHΣ.
Defined.

Import EAst.
Definition annot_dearg_lambdas {A} mask {t} (ta : annots A t)
  : annots A (dearg_lambdas mask t).
Proof.
  revert t ta mask.
  fix f 1.
  intros [] ta mask; cbn in *; try exact ta.
  - destruct mask; [exact ta|].
    destruct b.
    + apply annot_subst1; [exact ta.1|].
      apply (f _ ta.2).
    + exact (ta.1, f _ ta.2 _).
  - exact (ta.1, (ta.2.1, f _ ta.2.2 _)).
Defined.

Definition annot_dearg_single
           mask
           {hd}
           (hda : annots box_type hd)
           {args}
           (argsa : All (fun t => box_type * annots box_type t) args)
  : annots box_type (dearg_single mask hd args).
Proof.
  revert hd hda args argsa.
  induction mask; intros hd hda args argsa; cbn.
  - apply annot_mkApps; assumption.
  - destruct a.
    + (* arg is being removed but overall type does not change. *)
      destruct argsa.
      * (* there is no arg. Lambda has original type so body has type of codomain *)
        refine (annot hda, _).
        apply IHmask; [|exact All_nil].
        apply annot_lift.
        (* type of body is now the codomain *)
        exact (map_annot
                 (fun bt =>
                    match bt with
                    | TArr _ cod => cod
                    | _ => bt
                    end) hda).
      * (* arg was removed. We take the new type to be the old type of the application
         instead of the codomain as the old type of the application is more specialized. *)
        apply IHmask; [|exact argsa].
        exact (map_annot (fun _ => p.1) hda).
    + destruct argsa.
      * refine (annot hda, _).
        apply IHmask; [|exact All_nil].
        cbn.
        exact (match annot hda with
                | TArr dom cod => (cod, (annot_lift _ _ hda, dom))
                | t => (t, (annot_lift _ _ hda, t))
                end).
      * apply IHmask; [|exact argsa].
        exact (p.1, (hda, p.2)).
Defined.

Definition annot_dearg_case_branches
           {A}
           mm i
           {brs} (brsa : bigprod (annots A ∘ snd) brs)
  : bigprod (annots A ∘ snd) (dearg_case_branches mm i brs).
Proof.
  destruct mm; [|exact brsa].
  cbn.
  apply bigprod_mapi_rec; [|exact brsa].
  intros.
  apply annot_dearg_lambdas.
  exact X.
Defined.

Definition annot_dearg_aux
           im cm
           {args : list term}
           (argsa : All (fun t => box_type * annots box_type t) args)
           {t : term}
           (ta : annots box_type t) : annots box_type (dearg_aux im cm args t).
Proof.
  revert args argsa t ta.
  fix f 3.
  intros args argsa [] ta; cbn.
  - exact (annot_mkApps ta argsa).
  - exact (annot_mkApps ta argsa).
  - exact (annot_mkApps ta argsa).
  - apply annot_mkApps; [|exact argsa].
    cbn in *.
    refine (ta.1, bigprod_map _ ta.2).
    apply f.
    exact All_nil.
  - apply annot_mkApps; [|exact argsa].
    exact (ta.1, f _ All_nil _ ta.2).
  - apply annot_mkApps; [|exact argsa].
    exact (ta.1, (f _ All_nil _ ta.2.1, f _ All_nil _ ta.2.2)).
  - apply f; [|exact ta.2.1].
    apply All_cons; [|exact argsa].
    exact (ta.1, f _ All_nil _ ta.2.2).
  - exact (annot_dearg_single _ ta argsa).
  - exact (annot_dearg_single _ ta argsa).
  - destruct p.
    refine (annot_mkApps _ argsa).
    cbn in *.
    refine (ta.1, _).
    refine (f _ All_nil _ ta.2.1, _).
    apply annot_dearg_case_branches.
    apply bigprod_map; [|exact ta.2.2].
    intros.
    exact (f _ All_nil _ X).
  - destruct p as ((? & ?) & ?).
    refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    exact (f _ All_nil _ ta.2).
  - refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    fold (annots box_type).
    apply bigprod_map; [|exact ta.2].
    intros.
    exact (f _ All_nil _ X).
  - refine (annot_mkApps _ argsa).
    refine (ta.1, _).
    fold (annots box_type).
    apply bigprod_map; [|exact ta.2].
    intros.
    exact (f _ All_nil _ X).
Defined.

Definition annot_dearg im cm {t : term} (ta : annots box_type t) : annots box_type (dearg im cm t) :=
  annot_dearg_aux im cm All_nil ta.

Definition annot_debox_type_decl Σ {decl} (a : global_decl_annots box_type decl)
  : global_decl_annots box_type (debox_type_decl Σ decl).
Proof.
  unfold debox_type_decl.
  destruct decl;[|exact a|  (destruct o as [p|]; auto; destruct p;exact a)].
  cbn in *.
  (* we have removed type variables from inductives, so adjust type annotations similarly *)
  unfold constant_body_annots in *.
  cbn.
  destruct Ex.cst_body; [|exact tt].
  exact (map_annots (debox_box_type Σ) a).
Defined.

Definition annot_debox_env_types {Σ} (a : env_annots box_type Σ)
  : env_annots box_type (debox_env_types Σ).
Proof.
  unfold debox_env_types.
  apply bigprod_map; [|exact a].
  intros.
  apply annot_debox_type_decl.
  exact X.
Defined.

Definition annot_dearg_cst im cm kn {cst} (a : constant_body_annots box_type cst)
  : constant_body_annots box_type (dearg_cst im cm kn cst).
Proof.
  red in a |- *.
  unfold dearg_cst.
  cbn in *.
  destruct Annotations.Ex.cst_body; [|exact tt].
  cbn.
  apply annot_dearg.
  apply annot_dearg_lambdas.
  exact a.
Defined.

Definition annot_dearg_decl im cm kn {decl} (a : global_decl_annots box_type decl) :
  global_decl_annots box_type (dearg_decl im cm kn decl).
Proof.
  unfold dearg_decl.
  destruct decl; try exact a.
  cbn.
  apply annot_dearg_cst.
  exact a.
Defined.

Definition annot_dearg_env im cm {Σ} (a : env_annots box_type Σ)
  : env_annots box_type (dearg_env im cm Σ).
Proof.
  apply bigprod_map; [|exact a].
  intros ((? & ?) & ?) ?.
  cbn in *.
  apply annot_dearg_decl.
  exact X.
Defined.

Definition annot_dearg_transform
           (do_trim_const_masks : bool)
           (do_trim_ctor_masks : bool)
           (check_closed : bool)
           (check_expanded : bool)
           (check_valid_masks : bool) :
  annot_transform_type
    box_type
    (dearg_transform
       do_trim_const_masks do_trim_ctor_masks
       check_closed check_expanded check_valid_masks).
Proof.
  red.
  intros Σ a.
  red.
  unfold timed.
  destruct (_ && _); [exact tt|].
  destruct analyze_env.
  destruct (_ && _); [exact tt|].
  destruct (_ && _); [exact tt|].
  apply annot_debox_env_types.
  apply annot_dearg_env.
  exact a.
Defined.

Module AnnotOptimizePropDiscr.
  Import EOptimizePropDiscr OptimizePropDiscr.
  Definition annot_optimize Σ {t} (a : annots box_type t) : annots box_type (optimize Σ t).
  Proof.
    revert t a.
    fix f 1.
    intros [] a; cbn in *; try exact a.
    - exact (a.1, bigprod_map f a.2).
    - exact (a.1, f _ a.2).
    - exact (a.1, (f _ a.2.1, f _ a.2.2)).
    - exact (a.1, (f _ a.2.1, f _ a.2.2)).
    - assert (br_annots : bigprod (fun br => annots box_type br.2) (map (on_snd (optimize Σ)) l)).
      { refine (bigprod_map _ a.2.2).
        intros ? a'; apply (f _ a'). }
      destruct ETyping.is_propositional_ind as [[]|]; cbn.
      2-3: exact (a.1, (f _ a.2.1, br_annots)).
      destruct map as [|(?&?) []]; cbn in *.
      1,3: exact (a.1, (f _ a.2.1, br_annots)).
      (* Term changed from
         match e with
         | c a1 .. an => f
         end
         to
         f tBox .. tBox *)
      (* We annotate the boxes based on the domains of f. *)
      destruct br_annots as (fa&_).
      revert n t0 fa.
      clear.
      fix f 1.
      intros [] hd hda.
      + exact hda.
      + cbn.
        apply f.
        exact (
            match annot hda with
            | TArr dom cod => (cod, (hda, cod))
            | t => (t, (hda, t))
            end).
    - destruct ETyping.is_propositional_ind as [[]|].
      2-3: exact (a.1, f _ a.2).
      exact a.1.
    - refine (a.1, bigprod_map _ a.2).
      intros ? a'; exact (f _ a').
    - refine (a.1, bigprod_map _ a.2).
      intros ? a'; exact (f _ a').
  Defined.

  Definition annot_optimize_constant_body Σ {cst} (a : constant_body_annots box_type cst) :
    constant_body_annots box_type (optimize_constant_body Σ cst).
  Proof.
    unfold constant_body_annots, optimize_constant_body in *.
    cbn.
    destruct ExAst.cst_body; cbn; [|exact tt].
    apply annot_optimize.
    exact a.
  Defined.

  Definition annot_optimize_decl Σ {decl} (a : global_decl_annots box_type decl) :
    global_decl_annots box_type (optimize_decl Σ decl).
  Proof.
    unfold global_decl_annots, optimize_decl in *.
    destruct decl; [|exact tt|exact tt].
    apply annot_optimize_constant_body.
    exact a.
  Defined.

  Definition annot_optimize_env Σ (a : env_annots box_type Σ) :
    env_annots box_type (optimize_env Σ).
  Proof.
    unfold env_annots, optimize_env.
    apply bigprod_map.
    - intros.
      apply annot_optimize_decl.
      exact X.
    - exact a.
  Defined.
End AnnotOptimizePropDiscr.

Definition annot_compose_transforms {Σ} (a : env_annots box_type Σ) transforms :
  All (annot_transform_type box_type) transforms ->
  match compose_transforms transforms Σ with
  | Ok Σ => env_annots box_type Σ
  | Err _ => unit
  end.
Proof.
  revert transforms Σ a.
  fix f 4.
  intros ? Σ a [].
  - exact a.
  - cbn.
    red in a0.
    specialize (a0 _ a).
    destruct x; [|exact tt].
    apply f; [exact a0|exact a1].
Defined.

Definition annot_extract_pcuic_env params Σ wfΣ include ignore :
  All (annot_transform_type box_type) (transforms params) ->
  match extract_pcuic_env params Σ wfΣ include ignore with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  intros all.
  unfold extract_pcuic_env.
  destruct optimize_prop_discr.
  + apply annot_compose_transforms; [|exact all].
    apply AnnotOptimizePropDiscr.annot_optimize_env.
    apply annotate_types_erase_global_decls_deps_recursive.
  + apply annotate_types_erase_global_decls_deps_recursive.
Defined.

Definition annot_extract_template_env params Σ include ignore :
  All (annot_transform_type box_type) (transforms (pcuic_args params)) ->
  match extract_template_env params Σ include ignore with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  intros all.
  unfold extract_template_env.
  destruct check_wf_env_func; [|exact tt].
  apply annot_extract_pcuic_env.
  exact all.
Defined.

Definition annot_extract_template_env_within_coq Σ include ignore :
  match extract_template_env_within_coq Σ include ignore with
  | Ok Σ => env_annots box_type Σ
  | _ => unit
  end.
Proof.
  apply annot_extract_template_env.
  cbn.
  constructor; [|constructor].
  apply annot_dearg_transform.
Defined.

Definition annot_extract_template_env_within_coq_sig
           (Σ : Ast.global_env)
           (include : KernameSet.t)
           (ignore : kername -> bool) : option (∑ Σ, env_annots box_type Σ).
Proof.
  pose proof (annot_extract_template_env_within_coq Σ include ignore).
  destruct extract_template_env_within_coq; [|exact None].
  exact (Some (t; X)).
Defined.
