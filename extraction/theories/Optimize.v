From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ESubterm.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import StringExtra.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import PArith.
From Coq Require Import String.
From Coq Require VectorDef.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EArities.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Prelim.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.

Local Open Scope string_scope.
Import ListNotations.
Import MonadNotation.
Set Equations Transparent.

Import EAstUtils.
Import Erasure.
Import ExAst.

Definition inspect {A} (x : A) : { a | a = x } :=
  exist x eq_refl.

(* Eta expand all constructors so they are applied to all their parameters *)
Section eta.
Context (Σ : global_env).

Definition mcΣ : EAst.global_declarations :=
  map (fun '(kn, cst) =>
         (kn,
          match cst with
          | ConstantDecl cst =>
            EAst.ConstantDecl {| EAst.cst_body := cst_body cst |}
          | InductiveDecl mib =>
            EAst.InductiveDecl
              {| EAst.ind_npars := ind_npars mib;
                 EAst.ind_bodies :=
                   map (fun oib =>
                          {| EAst.ind_name := ind_name oib;
                             EAst.ind_kelim := InType;
                             EAst.ind_ctors :=
                               map (fun '(name, data) => (name, tBox, List.length data))
                                   (ind_ctors oib);
                             EAst.ind_projs :=
                               map (fun '(name, bt) => (name, tBox))
                                   (ind_projs oib) |})
                       (ind_bodies mib) |}
          end))
      Σ.

Section eta.
(* Ctors to eta expand *)
Context (ctors : list (inductive * nat * nat)).
(* Constants to eta expand *)
Context (constants : list (kername * nat)).

Definition eta_single (t : term) (args : list term) (count : nat) : term :=
  let needed := count - List.length args in
  let prev_args := map (lift0 needed) args in
  let eta_args := rev_map tRel (seq 0 needed) in
  nat_rect
    _
    (mkApps t (prev_args ++ eta_args))
    (fun _ => tLambda nAnon)
    needed.

Definition eta_ctor (ind : inductive) (c : nat) (args : list term) : term :=
  match find (fun '(ind', c', n) => eq_inductive ind' ind && (c' =? c)) ctors with
  | Some (_, _, n) => eta_single (tConstruct ind c) args n
  | None => mkApps (tConstruct ind c) args
  end.

Definition eta_const (kn : kername) (args : list term) : term :=
  match find (fun '(kn', n) => eq_kername kn' kn) constants with
  | Some (_, n) => eta_single (tConst kn) args n
  | None => mkApps (tConst kn) args
  end.

Definition map_subterms (f : term -> term) (t : term) : term :=
  match t with
  | tEvar n ts => tEvar n (map f ts)
  | tLambda na body => tLambda na (f body)
  | tLetIn na val body => tLetIn na (f val) (f body)
  | tApp hd arg => tApp (f hd) (f arg)
  | tCase p disc brs =>
    tCase p (f disc) (map (on_snd f) brs)
  | tProj p t => tProj p (f t)
  | tFix def i => tFix (map (map_def f) def) i
  | tCoFix def i => tCoFix (map (map_def f) def) i
  | t => t
  end.

Fixpoint eta_expand (args : list term) (t : term) : term :=
  match t with
  | tApp hd arg => eta_expand (eta_expand [] arg :: args) hd
  | tConstruct ind c => eta_ctor ind c args
  | tConst kn => eta_const kn args
  | t => mkApps (map_subterms (eta_expand []) t) args
  end.

Lemma wfe_term_eta_single t args n :
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

Lemma wfe_term_eta_ctor ind i args :
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

Lemma wfe_term_eta_const kn args :
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

Lemma wfe_term_eta_expand args t :
  Forall (wfe_term Σ) args ->
  wfe_term Σ t ->
  wfe_term Σ (eta_expand args t).
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

Lemma eta_expand_unfold t args :
  eta_expand args t =
  match decompose_app t with
  | (tConstruct ind c, args') => eta_ctor ind c (map (eta_expand []) args' ++ args)
  | (tConst kn, args') => eta_const kn (map (eta_expand []) args' ++ args)
  | (hd, args') => mkApps (map_subterms (eta_expand []) hd) (map (eta_expand []) args' ++ args)
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

Lemma eta_expand_nil_unfold t :
  eta_expand [] t =
  match decompose_app t with
  | (tConstruct ind c, args) => eta_ctor ind c (map (eta_expand []) args)
  | (tConst kn, args) => eta_const kn (map (eta_expand []) args)
  | (hd, args) => mkApps (map_subterms (eta_expand []) hd) (map (eta_expand []) args)
  end.
Proof.
  rewrite eta_expand_unfold.
  destruct (decompose_app _).
  now rewrite app_nil_r.
Qed.

Notation "s ▷ t" := (eval mcΣ s t) (at level 50, t at next level) : type_scope.

End eta.

Definition set_bit (n : nat) (p : positive) : positive :=
  Pos.lor p (Pos.shiftl_nat 1 n).

Definition has_bit (n : nat) (p : positive) : bool :=
  Pos.testbit_nat p n.

Local Open Scope positive.
Definition chop (p : positive) : positive :=
  match p with
  | p~0 => p
  | p~1 => p
  | XH => 1
  end.

(* Return bitmask indicating which context variables have uses *)
Fixpoint used_context_vars (Γ : positive) (t : term) : positive :=
  match t with
  | tBox => Γ
  | tRel i => set_bit i Γ
  | tVar n => Γ
  | tEvar _ ts => fold_right Pos.lor Γ (map (used_context_vars Γ) ts)
  | tLambda _ cod => chop (used_context_vars Γ~0 cod)
  | tLetIn _ val body => chop (used_context_vars (used_context_vars Γ val)~0 body)
  | tApp hd arg => used_context_vars (used_context_vars Γ hd) arg
  | tConst _ => Γ
  | tConstruct _ _ => Γ
  | tCase _ disc brs =>
    let Γ := used_context_vars Γ disc in
    fold_right Pos.lor Γ (map (used_context_vars Γ ∘ snd) brs)
  | tProj _ t => used_context_vars Γ t
  | tFix def _
  | tCoFix def _ => fold_right Pos.lor Γ (map (used_context_vars Γ ∘ dbody) def)
  end.

Local Open Scope nat.
Fixpoint uses_var (db : nat) (t : term) : bool :=
  match t with
  | tBox => false
  | tRel i => i =? db
  | tVar _ => false
  | tEvar _ ts => fold_right orb false (map (uses_var db) ts)
  | tLambda _ cod => uses_var (S db) cod
  | tLetIn _ val body => uses_var db val || uses_var (S db) body
  | tApp hd arg => uses_var db hd || uses_var db arg
  | tConst _ => false
  | tConstruct _ _ => false
  | tCase _ disc brs =>
    fold_right orb (uses_var db disc) (map (uses_var db ∘ snd) brs)
  | tProj _ t => uses_var db t
  | tFix def _
  | tCoFix def _ => fold_right orb false (map (uses_var db ∘ dbody) def)
  end.

Definition uses_var_decision (n : nat) (t : term) : Type :=
  {uses_var n t} + {~uses_var n t}.

Fixpoint use_annots (t : term) : Type :=
  match t with
  | tBox => unit
  | tRel _ => unit
  | tVar _ => unit
  | tEvar _ ts => fold_right prod unit (map use_annots ts)
  | tLambda _ cod => uses_var_decision 0 cod × use_annots cod
  | tLetIn _ val body => use_annots val * uses_var_decision 0 body * use_annots body
  | tApp hd arg => use_annots hd × use_annots arg
  | tConst _ => unit
  | tConstruct _ _ => unit
  | tCase _ disc brs =>
    use_annots disc × fold_right prod unit (map (use_annots ∘ snd) brs)
  | tProj _ t => use_annots t
  | tFix def _
  | tCoFix def _ => fold_right prod unit (map (use_annots ∘ dbody) def)
  end.

(* TODO: This can be optimized. A lot. *)
Equations annotate (t : term) : use_annots t :=
annotate tBox := tt;
annotate (tRel _) := tt;
annotate (tVar _) := tt;
annotate (tEvar _ ts) := annot_ts ts
where annot_ts (ts : list term) : fold_right prod unit (map use_annots ts) := {
annot_ts [] := tt;
annot_ts (t :: ts) := (annotate t, annot_ts ts)
};
annotate (tLambda _ cod) with inspect (uses_var 0 cod) := {
  | exist true _ := (left _, annotate cod);
  | exist false _ := (right _, annotate cod)
  };
annotate (tLetIn _ val body) with inspect (uses_var 0 body) := {
  | exist true _ := (annotate val, left _, annotate body);
  | exist false _ := (annotate val, right _, annotate body)
  };
annotate (tApp hd arg) := (annotate hd, annotate arg);
annotate (tConst _) := tt;
annotate (tConstruct _ _) := tt;
annotate (tCase _ disc brs) := (annotate disc, annot_brs brs)
where annot_brs (brs : list (nat × term)) : fold_right prod unit (map (use_annots ∘ snd) brs) := {
annot_brs [] := tt;
annot_brs ((_, t) :: brs) := (annotate t, annot_brs brs)
};
annotate (tProj _ t) := annotate t;
annotate (tFix defs _) := annot_defs defs
where annot_defs (defs : list (def term)) : fold_right prod unit (map (use_annots ∘ dbody) defs) := {
annot_defs [] := tt;
annot_defs (d :: defs) := (annotate (dbody d), annot_defs defs)
};
annotate (tCoFix defs _) := annot_defs defs
where annot_defs (defs : list (def term)) : fold_right prod unit (map (use_annots ∘ dbody) defs) := {
annot_defs [] := tt;
annot_defs (d :: defs) := (annotate (dbody d), annot_defs defs)
}.
Next Obligation. congruence. Qed.
Next Obligation. congruence. Qed.

Definition decl_marks (decl : global_decl) : Type :=
  match decl with
  | ConstantDecl cst => list bool
  | InductiveDecl mib =>
    (* constructors are simple enough that we just look them up directly *)
    unit
  end.

Definition global_env_marks (Σ : global_env) : Type :=
  fold_right prod unit (map (decl_marks ∘ snd) Σ).

Equations lookup_const_marks
          (Σ : global_env)
          (marks : global_env_marks Σ)
          (kn : kername) : list bool :=
lookup_const_marks [] _ _ := [];
lookup_const_marks ((dkn, ConstantDecl cst) :: Σ) (marks, rest) kn with eq_kername dkn kn := {
  | true := marks;
  | false := lookup_const_marks Σ rest kn
  };
lookup_const_marks (_ :: Σ) (_, rest) kn := lookup_const_marks Σ rest kn.

Fixpoint mark_parameters (bt : box_type) (tm : term) : list bool :=
  match bt, tm with
  | TArr dom cod, tLambda _ res =>
    match dom with
    | TBox => true
    | _ => false
    end :: mark_parameters cod res
  | _, _ => []
  end.

Equations mark_constants (Σ : global_env) : global_env_marks Σ :=
mark_constants [] := tt;
mark_constants ((kn, decl) :: Σ) := (mark_decl decl, mark_constants Σ)
  where mark_decl (decl : global_decl) : decl_marks decl :=
  mark_decl (ConstantDecl cst) with cst_body cst := {
    | Some body := mark_parameters (cst_type cst).2 body;
    | None := []
    };
  mark_decl (InductiveDecl _) := tt.

(* Step 2:
