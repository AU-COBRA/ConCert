From Coq Require Import List.
From Coq Require Import RelationClasses.
From Coq Require Import Relation_Operators.
From Coq Require Import Transitive_Closure.
From Equations Require Import Equations.
From MetaCoq Require Import All_Forall.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import Prelim.

Import ListNotations.

Inductive term_direct_subterm : term -> term -> Prop :=
| term_sub_Var t n ts : In t ts -> term_direct_subterm t (tEvar n ts)
| term_sub_Lambda n body : term_direct_subterm body (tLambda n body)
| term_sub_LetIn_1 na val body : term_direct_subterm val (tLetIn na val body)
| term_sub_LetIn_2 na val body : term_direct_subterm body (tLetIn na val body)
| term_sub_App_1 hd arg : term_direct_subterm hd (tApp hd arg)
| term_sub_App_2 hd arg : term_direct_subterm arg (tApp hd arg)
| term_sub_Case_1 p discr brs : term_direct_subterm discr (tCase p discr brs)
| term_sub_Case_2 t p discr brs : In t (map snd brs) -> term_direct_subterm t (tCase p discr brs)
| term_sub_Proj p t : term_direct_subterm t (tProj p t)
| term_sub_Fix t defs n : In t (map dbody defs) -> term_direct_subterm t (tFix defs n)
| term_sub_CoFix t defs n : In t (map dbody defs) -> term_direct_subterm t (tCoFix defs n).

Derive Inversion_clear inv_sub_of_tBox with (forall t, term_direct_subterm t tBox).
Derive Inversion_clear inv_sub_of_tRel with (forall t i, term_direct_subterm t (tRel i)).
Derive Inversion_clear inv_sub_of_tVar with (forall t na, term_direct_subterm t (tVar na)).
Derive Inversion_clear inv_sub_of_tEvar with (forall t n ts, term_direct_subterm t (tEvar n ts)).
Derive Inversion_clear inv_sub_of_tLambda
  with (forall t na body, term_direct_subterm t (tLambda na body)).
Derive Inversion_clear inv_sub_of_tLetIn
  with (forall t na val body, term_direct_subterm t (tLetIn na val body)).
Derive Inversion_clear inv_sub_of_tApp
  with (forall t hd arg, term_direct_subterm t (tApp hd arg)).
Derive Inversion_clear inv_sub_of_tConst with (forall t kn, term_direct_subterm t (tConst kn)).
Derive Inversion_clear inv_sub_of_tConstruct
  with (forall t ind c, term_direct_subterm t (tConstruct ind c)).
Derive Inversion_clear inv_sub_of_tCase
  with (forall t p discr brs, term_direct_subterm t (tCase p discr brs)).
Derive Inversion_clear inv_sub_of_tProj
  with (forall t p val, term_direct_subterm t (tProj p val)).
Derive Inversion_clear inv_sub_of_tFix
  with (forall t defs i, term_direct_subterm t (tFix defs i)).
Derive Inversion_clear inv_sub_of_tCoFix
  with (forall t defs i, term_direct_subterm t (tCoFix defs i)).

(* This proof could be much shorter, but it is intentionally abstracted out here
   so the proof term is smaller and we can compute with it more nicely. *)
Lemma well_founded_term_direct_subterm : well_founded term_direct_subterm.
Proof.
  intros t.
  induction t using term_forall_list_ind; constructor; intros t' rel.
  - now apply inv_sub_of_tBox.
  - now apply (inv_sub_of_tRel t' n (fun t _ => Acc term_direct_subterm t)).
  - now apply (inv_sub_of_tVar t' i (fun t _ => Acc term_direct_subterm t')).
  - apply (inv_sub_of_tEvar t' n l (fun t _ _ => Acc term_direct_subterm t)).
    + intros.
      eapply Forall_forall; eassumption.
    + assumption.
  - now apply (inv_sub_of_tLambda t' n t (fun t _ _ => Acc term_direct_subterm t)).
  - now apply (inv_sub_of_tLetIn t' n t1 t2 (fun t _ _ _ => Acc term_direct_subterm t)).
  - now apply (inv_sub_of_tApp t' t1 t2 (fun t _ _ => Acc term_direct_subterm t)).
  - now apply (inv_sub_of_tConst t' s (fun t _ => Acc term_direct_subterm t)).
  - now apply (inv_sub_of_tConstruct t' i n (fun t _ _ => Acc term_direct_subterm t)).
  - apply (inv_sub_of_tCase t' p t l (fun t _ _ _ => Acc term_direct_subterm t)).
    + assumption.
    + intros isin.
      eapply Forall_forall; [|exact isin].
      apply All_Forall.
      now apply All_map.
    + assumption.
  - now apply (inv_sub_of_tProj t' s t (fun t _ _ => Acc term_direct_subterm t)).
  - apply (inv_sub_of_tFix t' m n (fun t _ _ => Acc term_direct_subterm t)).
    + intros isin.
      eapply Forall_forall; [|exact isin].
      now apply Forall_map.
    + assumption.
  - apply (inv_sub_of_tCoFix t' m n (fun t _ _ => Acc term_direct_subterm t)).
    + intros isin.
      eapply Forall_forall; [|exact isin].
      now apply Forall_map.
    + assumption.
Defined.

Definition term_subterm : term -> term -> Prop :=
  clos_trans _ term_direct_subterm.

Instance Transitive_term_subterm : Transitive term_subterm.
Proof.
  intros x y z xy yz.
  now apply t_trans with y.
Qed.

Lemma well_founded_term_subterm : well_founded term_subterm.
Proof.
  apply wf_clos_trans.
  apply well_founded_term_direct_subterm.
Defined.

Instance WellFounded_term_subterm : WellFounded term_subterm :=
  well_founded_term_subterm.

Fixpoint map_in {A B} (l : list A) (f : forall a, In a l -> B) {struct l} : list B.
Proof.
  destruct l as [|a l].
  - exact [].
  - refine (cons (f a (or_introl eq_refl)) _).
    refine (map_in _ _ l (fun a' ina' => _)).
    refine (f a' _).
    refine (or_intror _).
    exact ina'.
Defined.

(*
Equations map_subterms (t : term) (f : forall t', term_direct_subterm t' t -> term) : term :=
map_subterms (tEvar n ts) f := tEvar n (map_in ts (fun a isin => f a _));
map_subterms (tLambda na body) f := tLambda na (f body _);
map_subterms (tLetIn na val body) f := tLetIn na (f val _) (f body _);
map_subterms (tApp hd arg) f := tApp (f hd _) (f arg _);
map_subterms (tCase p disc brs) f :=
  tCase p (f disc _) (map_in brs (fun '(n, t) isin => (n, f t _)));
map_subterms (tProj p t) f := tProj p (f t _);
map_subterms (tFix defs i) f := tFix (map_in defs (fun d isin => {| dname := dname d;
                                                                  dbody := f (dbody d) _;
                                                                  rarg := rarg d |})) i;
map_subterms (tCoFix defs i) f := tCoFix (map_in defs (fun d isin => {| dname := dname d;
                                                                        dbody := f (dbody d) _;
                                                                        rarg := rarg d |})) i;
map_subterms t f := t.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation.
  constructor.
  apply in_map_iff.
  now exists (n, t).
Qed.
Next Obligation. now constructor. Qed.
Next Obligation.
  constructor.
  apply in_map_iff.
  now exists d.
Qed.
Next Obligation.
  constructor.
  apply in_map_iff.
  now exists d.
Qed.
*)

Program Definition map_subterms (t : term) (f : forall t', term_direct_subterm t' t -> term) : term :=
  match t with
  | tEvar n ts => tEvar n (map_in ts (fun a isin => f a _))
  | tLambda na body => tLambda na (f body _)
  | tLetIn na val body => tLetIn na (f val _) (f body _)
  | tApp hd arg => tApp (f hd _) (f arg _)
  | tCase p disc brs =>
    tCase p (f disc _) (map_in brs (fun '(n, t) isin => (n, f t _)))
  | tProj p t => tProj p (f t _)
  | tFix defs i => tFix (map_in defs (fun d isin => {| dname := dname d;
                                                       dbody := f (dbody d) _;
                                                       rarg := rarg d |})) i
  | tCoFix defs i => tCoFix (map_in defs (fun d isin => {| dname := dname d;
                                                           dbody := f (dbody d) _;
                                                           rarg := rarg d |})) i
  | t => t
  end.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation. now constructor. Qed.
Next Obligation.
  constructor.
  apply in_map_iff.
  now exists (n0, t1).
Qed.
Next Obligation. now constructor. Qed.
Next Obligation.
  constructor.
  apply in_map_iff.
  now exists d.
Qed.
Next Obligation.
  constructor.
  apply in_map_iff.
  now exists d.
Qed.
Next Obligation. easy. Qed.
Next Obligation. easy. Qed.
Next Obligation. easy. Qed.
Next Obligation. easy. Qed.
Next Obligation. easy. Qed.

Lemma decompose_app_head_or_subterm hd args t :
  (hd, args) = decompose_app t ->
  hd = t \/ term_subterm hd t.
Proof.
  intros is_decomp.
  symmetry in is_decomp.
  apply decompose_app_inv in is_decomp.
  subst.
  revert hd.
  induction args using List.rev_ind; [easy|]; intros hd.
  right.
  rewrite emkApps_snoc.
  destruct (IHargs hd) as [?|].
  - SearchAbout mkApps.
    change hd with (mkApps hd []) in H.
    apply mkApps_eq_right in H.
    subst.
    cbn.
    do 2 constructor.
  - transitivity (mkApps hd args); [easy|].
    do 2 constructor.
Qed.

Lemma decompose_app_args_subterm hd args t t' :
  (hd, args) = decompose_app t ->
  In t' args ->
  term_subterm t' t.
Proof.
  intros is_decomp is_in.
  symmetry in is_decomp.
  apply decompose_app_inv in is_decomp.
  subst.
  revert hd.
  induction args using List.rev_ind; [easy|]; intros hd.
  rewrite emkApps_snoc.
  apply in_app_iff in is_in.
  destruct is_in.
  - transitivity (mkApps hd args); [easy|].
    do 2 constructor.
  - destruct H as [->|[]].
    do 2 constructor.
Qed.
