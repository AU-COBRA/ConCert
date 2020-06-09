From ConCert.Extraction Require Import ESubterm.
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

Definition declared_minductive (kn : kername) (mib : mutual_inductive_body) : Prop :=
  lookup_env Σ kn = Some (InductiveDecl mib).

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

Definition lookup_minductive (kn : kername) : option mutual_inductive_body :=
  match lookup_env Σ kn with
  | Some (InductiveDecl mib) => Some mib
  | _ => None
  end.

Definition lookup_inductive (ind : inductive) : option one_inductive_body :=
  mib <- lookup_minductive (inductive_mind ind);;
  nth_error (ind_bodies mib) (inductive_ind ind).

Definition lookup_constructor (ind : inductive) (c : nat) : option (ident * list box_type) :=
  oib <- lookup_inductive ind;;
  nth_error (ind_ctors oib) c.

Lemma lookup_minductive_declared kn mib :
  declared_minductive kn mib ->
  lookup_minductive kn = Some mib.
Proof.
  unfold declared_minductive, lookup_minductive.
  now intros ->.
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
    destruct wft as (_ & (_ & allwf)).
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

Lemma wfe_term_direct_subterm t t' :
  term_direct_subterm t' t ->
  wfe_term t ->
  wfe_term t'.
Proof.
  intros sub wft.
  destruct t; inversion sub; subst; clear sub; cbn in *; try easy.
  - induction l; cbn in *; [easy|].
    now destruct H1.
  - now destruct p.
  - destruct p.
    destruct wft as (_ & _ & wft).
    induction l; cbn in *; [easy|].
    now destruct H1.
  - induction m; cbn in *; [easy|].
    now destruct H1.
  - induction m; cbn in *; [easy|].
    now destruct H1.
Qed.

Lemma wfe_term_subterm t t' :
  term_subterm t' t ->
  wfe_term t ->
  wfe_term t'.
Proof.
  induction 1.
  - now apply wfe_term_direct_subterm.
  - tauto.
Qed.

Lemma map_subterms_sublist
      {A B}
      (p : B -> term)
      (l : list A)
      (f : forall a, In a l -> B) :
  (forall a isin, wfe_term (p (f a isin))) ->
  fold_right and True (map (fun a => wfe_term (p a)) (map_in l f)).
Proof.
  intros wff.
  induction l; [easy|].
  cbn.
  split; [easy|].
  now apply IHl.
Qed.

Lemma wfe_term_map_subterms t f :
  wfe_term t ->
  (forall t' sub, wfe_term t' -> wfe_term (f t' sub)) ->
  wfe_term (map_subterms t f).
Proof.
  intros wft wff.
  destruct t; try easy.
  - cbn.
    apply map_subterms_sublist.
    intros.
    apply wff.
    eapply wfe_term_subterm; [|exact wft].
    now do 2 constructor.
  - now cbn in *.
  - now cbn in *.
  - now cbn in *.
  - cbn in *.
    destruct p as [ind c].
    split; [easy|].
    split; [easy|].
    apply map_subterms_sublist.
    intros [n' t'] isin.
    apply wff.
    apply (wfe_term_subterm (tCase (ind, c) t l)); [|easy].
    constructor.
    constructor.
    clear -isin.
    induction l; [easy|].
    destruct isin as [->|?]; cbn; easy.
  - now cbn in *.
  - cbn.
    apply map_subterms_sublist.
    intros.
    apply wff.
    eapply wfe_term_subterm; [|eassumption].
    do 2 constructor.
    now apply in_map.
  - cbn.
    apply map_subterms_sublist.
    intros.
    apply wff.
    eapply wfe_term_subterm; [|eassumption].
    do 2 constructor.
    now apply in_map.
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
    | InductiveDecl _ => True
    end /\ wfe Σ
  end.
