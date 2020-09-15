From ConCert.Extraction Require Import ExAst.
From Coq Require Import Arith.
From Coq Require Import List.
From Equations Require Import Equations.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.

Import MonadNotation.

Section wf.
Context (Σ : global_env).

Definition declared_constant (kn : kername) (cst : constant_body) : Prop :=
  lookup_env Σ kn = Some (ConstantDecl cst).

Definition declared_minductive (kn : kername) (mib : mutual_inductive_body) : Prop :=
  exists flag, lookup_env Σ kn = Some (InductiveDecl flag mib).

Definition declared_inductive
           (mib : mutual_inductive_body)
           (ind : inductive)
           (oib : one_inductive_body) : Prop :=
  declared_minductive (inductive_mind ind) mib /\
  nth_error (ind_bodies mib) (inductive_ind ind) = Some oib.

Definition declared_constructor
           (mib : mutual_inductive_body)
           (oib : one_inductive_body)
           (ind : inductive)
           (i : nat)
           (cdecl : ident * list box_type) : Prop :=
  declared_inductive mib ind oib /\
  nth_error (ind_ctors oib) i = Some cdecl.

Fixpoint wfe_term (t : term) : Prop :=
  match t with
  | tBox => True
  | tRel _ => True
  | tVar _ => True
  | tEvar _ ts => fold_right and True (map wfe_term ts)
  | tLambda _ cod => wfe_term cod
  | tLetIn _ val body => wfe_term val /\ wfe_term body
  | tApp hd arg => wfe_term hd /\ wfe_term arg
  | tConst _ => True
  | tConstruct ind c => exists mib oib cdecl, declared_constructor mib oib ind c cdecl
  | tCase (ind, npars) disc brs =>
    (exists mib oib, declared_inductive mib ind oib /\ ind_npars mib = npars) /\
    wfe_term disc /\
    fold_right and True (map (wfe_term ∘ snd) brs)
  | tProj _ t => wfe_term t
  | tFix def _
  | tCoFix def _ => fold_right and True (map (wfe_term ∘ dbody) def)
  end.

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

Lemma lookup_constant_declared kn cst :
  declared_constant kn cst ->
  lookup_constant kn = Some cst.
Proof.
  unfold declared_constant, lookup_constant.
  now intros ->.
Qed.

Lemma lookup_minductive_declared kn mib :
  declared_minductive kn mib ->
  lookup_minductive kn = Some mib.
Proof.
  unfold declared_minductive, lookup_minductive.
  intros H. destruct H. now rewrite H.
Qed.

Lemma lookup_inductive_declared mib ind oib :
  declared_inductive mib ind oib ->
  lookup_inductive ind = Some oib.
Proof.
  unfold declared_inductive, lookup_inductive.
  now intros (->%lookup_minductive_declared & ?).
Qed.

Lemma lookup_ctor_declared mib oib ind c ctor :
  declared_constructor mib oib ind c ctor ->
  lookup_constructor ind c = Some ctor.
Proof.
  unfold declared_constructor, lookup_constructor.
  now intros (->%lookup_inductive_declared & ?).
Qed.

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
  now cbn.
Qed.

Lemma wfe_term_lift t n k :
  wfe_term t ->
  wfe_term (lift n k t).
Proof.
  intros wft.
  revert n k.
  induction t using term_forall_list_ind; intros ? ?; cbn in *; try easy.
  - now destruct (_ <=? _).
  - induction H; cbn in *; easy.
  - destruct p.
    split; [easy|].
    split; [easy|].
    destruct wft as (_ & _ & allwf).
    unfold tCaseBrsProp in X.
    induction X; cbn in *; easy.
  - revert k.
    induction H; intros k; [easy|].
    cbn in *.
    split; [easy|].
    rewrite <- Nat.add_succ_r.
    easy.
  - revert k.
    induction H; intros k; [easy|].
    cbn in *.
    split; [easy|].
    rewrite <- Nat.add_succ_r.
    easy.
Qed.

End wf.

Fixpoint wfe (Σ : global_env) : Prop :=
  match Σ with
  | [] => True
  | (kn, decl) :: Σ =>
    match decl with
    | ConstantDecl cst =>
      match cst_body cst with
      | Some body => wfe_term Σ body
      | None => True
      end
    | InductiveDecl _ _ => True
    | TypeAliasDecl _ => True (* FIXME: Do we need to say something about type aliases? *)
    end /\ wfe Σ
  end.
