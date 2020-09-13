From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ExAst.
From Coq Require Import Arith.
From Coq Require Import List.
From Equations Require Import Equations.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import Extract.

Import MonadNotation.

Section wf.
Context (Σ : global_env).

Definition lookup_constant (kn : kername) : option constant_body :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cst) => Some cst
  | _ => None
  end.

Definition lookup_minductive (kn : kername) : option mutual_inductive_body :=
  match lookup_env Σ kn with
  | Some (InductiveDecl _ mib) => Some mib
  | _ => None
  end.

Definition lookup_inductive (ind : inductive) : option one_inductive_body :=
  mib <- lookup_minductive (inductive_mind ind);;
  nth_error (ind_bodies mib) (inductive_ind ind).

Definition lookup_constructor (ind : inductive) (c : nat) : option (ident * list box_type) :=
  oib <- lookup_inductive ind;;
  nth_error (ind_ctors oib) c.

Fixpoint wfe_term (t : term) : bool :=
  match t with
  | tBox => true
  | tRel _ => true
  | tVar _ => true
  | tEvar _ ts => forallb wfe_term ts
  | tLambda _ cod => wfe_term cod
  | tLetIn _ val body => wfe_term val && wfe_term body
  | tApp hd arg => wfe_term hd && wfe_term arg
  | tConst _ => true
  | tConstruct ind c => if lookup_constructor ind c then true else false
  | tCase (ind, npars) disc brs =>
    match lookup_minductive (inductive_mind ind) with
    | Some mib => ind_npars mib =? npars
    | None => false
    end && wfe_term disc && forallb (wfe_term ∘ snd) brs
  | tProj (ind, npars, arg) t =>
    match lookup_minductive (inductive_mind ind) with
    | Some mib =>
      (ind_npars mib =? npars) &&
      match nth_error (ind_bodies mib) (inductive_ind ind) with
      | Some oib => #|ind_ctors oib| =? 1
      | None => false
      end
    | None => false
    end
  | tFix def _
  | tCoFix def _ => forallb (wfe_term ∘ dbody) def
  end.

Lemma wfe_term_mkApps hd args :
  wfe_term hd ->
  Forall wfe_term args ->
  wfe_term (mkApps hd args).
Proof.
  intros wfhd wfall.
  revert hd wfhd.
  induction wfall; intros hd wfhd; [easy|].
  cbn in *.
  apply IHwfall.
  cbn.
  now propify.
Qed.

Lemma wfe_term_mkApps_inv hd args :
  wfe_term (mkApps hd args) ->
  wfe_term hd /\ Forall wfe_term args.
Proof.
  intros wf.
  induction args in hd, wf |- *; [easy|].
  cbn in *.
  apply IHargs in wf as (wf_app & wf_args).
  cbn in *.
  now propify.
Qed.

Lemma wfe_term_lift t n k :
  wfe_term t ->
  wfe_term (lift n k t).
Proof.
  intros wft.
  revert n k.
  induction t using term_forall_list_ind; intros ? ?; cbn in *; try easy.
  - now destruct (_ <=? _).
  - induction H; cbn in *; [easy|].
    now propify.
  - now propify.
  - now propify.
  - destruct p.
    propify.
    split; [easy|].
    induction X; cbn in *; [easy|].
    now propify.
  - revert k.
    induction H; intros k; [easy|].
    cbn in *; propify.
    split; [easy|].
    now rewrite <- Nat.add_succ_r.
  - revert k.
    induction H; intros k; [easy|].
    cbn in *; propify.
    split; [easy|].
    now rewrite <- Nat.add_succ_r.
Qed.

End wf.

Fixpoint wfe_env (Σ : global_env) : bool :=
  match Σ with
  | [] => true
  | (kn, decl) :: Σ =>
    match decl with
    | ConstantDecl cst =>
      match cst_body cst with
      | Some body => wfe_term Σ body
      | None => true
      end
    | InductiveDecl _ _ => true
    | TypeAliasDecl _ => true
    end && wfe_env Σ
  end.
