(** * Conversion from values back to expressions through the environment substitution *)
From Coq Require Import List.
From Coq Require Import Relations.
From Coq Require Import Morphisms.
From Coq Require Import ssrbool.
From Coq Require Import PeanoNat.
From ConCert.Utils Require Import Env.
From ConCert.Utils Require Import Extras.
From ConCert.Embedding Require Import EvalE.
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Misc.

(** ** Substitution for the nameless representation *)
Module NamelessSubst.

  Definition expr_to_ty (e : expr) : option type :=
    match e with
    | eTy ty => Some ty
    | _ => None
    end.

  Definition lookup_ty (ρ : env expr) (i : nat) : option type :=
     match lookup_i ρ i with
     | Some e => expr_to_ty e
     | None => None
     end.

  Fixpoint subst_env_i_ty (k : nat) (ρ : env expr) (ty : type) : type :=
      match ty with
      | tyInd x => ty
      | tyForall x ty => tyForall x (subst_env_i_ty (1+k) ρ ty)
      | tyApp ty1 ty2 =>
        let ty2' := subst_env_i_ty k ρ ty2 in
        let ty1' := subst_env_i_ty k ρ ty1 in
        tyApp ty1' ty2'
      | tyVar nm => ty
      | tyRel i => if Nat.leb k i then
                    with_default (tyRel i) (lookup_ty ρ (i-k)) else tyRel i
      | tyArr ty1 ty2 =>
        let ty2' := subst_env_i_ty k ρ ty2 in
        let ty1' := subst_env_i_ty k ρ ty1 in
        tyArr ty1' ty2'
      end.


  (** NOTE: assumes, that expression in [ρ] are closed! *)
  Fixpoint subst_env_i_aux (k : nat) (ρ : env expr) (e : expr) : expr :=
    match e with
    | eRel i => if Nat.leb k i then
                 with_default (eRel i) (lookup_i ρ (i-k)) else eRel i
    | eVar nm => eVar nm
    | eLambda nm ty b => eLambda nm (subst_env_i_ty k ρ ty) (subst_env_i_aux (1+k) ρ b)
    | eTyLam nm b => eTyLam nm (subst_env_i_aux (1+k) ρ b)
    | eLetIn nm e1 ty e2 => eLetIn nm (subst_env_i_aux k ρ e1) (subst_env_i_ty k ρ ty)
                                  (subst_env_i_aux (1+k) ρ e2)
    | eApp e1 e2 => eApp (subst_env_i_aux k ρ e1) (subst_env_i_aux k ρ e2)
    | eConstr t i as e' => e'
    | eConst nm => eConst nm
    | eCase nm_i ty e bs =>
      let (nm, tys) := nm_i in
      eCase (nm,map (subst_env_i_ty k ρ) tys) (subst_env_i_ty k ρ ty) (subst_env_i_aux k ρ e)
            (map (fun x => (fst x, subst_env_i_aux (length (fst x).(pVars) + k) ρ (snd x))) bs)
    | eFix nm v ty1 ty2 b => eFix nm v (subst_env_i_ty k ρ ty1) (subst_env_i_ty k ρ ty2)
                                 (subst_env_i_aux (2+k) ρ b)
    | eTy ty => eTy (subst_env_i_ty k ρ ty)
    end.

  Definition subst_env_i := subst_env_i_aux 0.

    (** Converting from values back to expressions.
       This will be used to compare results of the evaluation with different semantics,
       or for stating soundness theorem for the translation to a different language, e.g.
       to Template Coq terms.

       The most non-trivial part is to convert closures, for which we have to perform
       some form of substitution of values from the value environment (see [subst_env])
       Inspired by the implementation of
       "A Certified Implementation of ML with Structural Polymorphism" by Jacques Garrigue.
     *)

  Notation apps := vars_to_apps.

  Fixpoint of_val_i (v : val) : expr :=
    match v with
    | vConstr c i vs => apps (eConstr c i) (map of_val_i vs)
    | vClos ρ nm cm ty1 ty2 e =>
      let res := match cm with
                 | cmLam => eLambda nm ty1 e
                 | cmFix fixname => eFix fixname nm ty1 ty2 e
                end
      in subst_env_i (map (fun x => (fst x, of_val_i (snd x))) ρ) res
    | vTyClos ρ nm e => subst_env_i (map (fun x => (fst x, of_val_i (snd x))) ρ)
                                 (eTyLam nm e)
    | vTy ty => eTy ty

    end.

  Notation exprs := (map (fun x => (fst x, of_val_i (snd x)))).


  (** *** Notations for the environment substitution *)
  Notation "e .[ ρ ] n " := (subst_env_i_aux n ρ e) (at level 6).

  Definition inst_env_i (ρ : env val) (e : expr) : expr :=
    subst_env_i (map (fun x => (fst x, of_val_i (snd x))) ρ) e.
  Notation "e .[ ρ ]" := (subst_env_i ρ e) (at level 6).

  Import Lia.

  Lemma lookup_i_of_val_env ρ n v :
    lookup_i ρ n = Some v -> lookup_i (exprs ρ) n = Some (of_val_i v).
  Proof.
    revert dependent n.
    induction ρ; intros n0 Hρ.
    + easy.
    + destruct a; simpl in *.
      destruct n0.
      * simpl in *. inversion Hρ. subst. reflexivity.
      * simpl in *. replace (n0 - 0) with n0 in * by lia. easy.
  Qed.


  Lemma inst_env_i_in (ρ : env val) n :
    n <? length ρ ->
    {v | lookup_i ρ n = Some v /\ (eRel n).[exprs ρ] = of_val_i v}.
  Proof.
    intros Hlt.
    revert dependent n.
    induction ρ; intros n1 Hlt.
    + easy.
    + destruct (Nat.eqb n1 0) eqn:Hn1.
      * destruct a. eexists. split.
        ** simpl. rewrite Hn1.
           reflexivity.
        ** simpl in *. unfold inst_env_i,subst_env_i. simpl.
           assert (n1=0) by (apply Nat.eqb_eq; easy).
           subst. simpl. reflexivity.
      * destruct a.
        assert (Hn2 : {n2 | n1 = S n2}) by (destruct n1 as [ | n2];
          try discriminate; exists n2; reflexivity).
        destruct Hn2 as [n2 Heq_n2]. replace (n1-1) with n2 by lia.
        subst. simpl in Hlt. unfold is_true in *. rewrite Nat.ltb_lt in Hlt.
        apply Nat.succ_lt_mono in Hlt. rewrite <- Nat.ltb_lt in Hlt.
        specialize (IHρ _ Hlt). destruct IHρ as [v1 HH]. destruct HH as [H1 H2].
        exists v1. split.
        ** simpl in *. replace (n2 - 0) with n2 by lia. assumption.
        ** specialize (lookup_i_length _ _ Hlt) as Hlookup.
           destruct Hlookup.
           simpl in *. unfold inst_env_i,subst_env_i in *. simpl in *.
           rewrite <- H2. replace (n2 - 0) with n2 by lia.
           apply lookup_i_of_val_env in H1.
           now eapply with_default_indep.
  Qed.

End NamelessSubst.

(** ** Substitution for the named representation *)
Module NamedSubst.

  (** Currently we do not use named substitution in our soundness proof. *)

  (** NOTE: assumes, that expression in [ρ] are closed! *)
 Fixpoint subst_env (ρ : list (ename * expr)) (e : expr) : expr :=
  match e with
  | eRel i as e' => e'
  | eVar nm => match lookup ρ nm with
                    | Some v => v
                    | None => e
                    end
  | eLambda nm ty b => eLambda nm ty (subst_env (remove_by_key nm ρ) b)
  | eTyLam nm b => eTyLam nm (subst_env (remove_by_key nm ρ) b)
  | eLetIn nm e1 ty e2 => eLetIn nm (subst_env ρ e1) ty (subst_env (remove_by_key nm ρ) e2)
  | eApp e1 e2 => eApp (subst_env ρ e1) (subst_env ρ e2)
  | eConstr t i as e' => e'
  | eConst nm => eConst nm
  | eCase nm_i ty e bs =>
    (* TODO: this case is not complete! We ignore variables bound by patterns *)
    eCase nm_i ty (subst_env ρ e) (map (fun x => (fst x, subst_env ρ (snd x))) bs)
  | eFix nm v ty1 ty2 b => eFix nm v ty1 ty2 (subst_env (remove_by_key v ρ) b)
  | eTy _ => e
  end.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | vConstr x i vs => vars_to_apps (eConstr x i) (map of_val vs)
    | vClos ρ nm cm ty1 ty2 e =>
      let res := match cm with
                 | cmLam => eLambda nm ty1 e
                 | cmFix fixname => eFix fixname nm ty1 ty2 e
                 end
      in subst_env (map (fun x => (fst x, of_val (snd x))) ρ) res
    | vTyClos ρ nm e => subst_env (map (fun x => (fst x, of_val (snd x))) ρ)
                                 (eTyLam nm e)
    | vTy ty => eTy ty
    end.

 Definition inst_env (ρ : env val) (e : expr) : expr :=
    subst_env (map (fun x => (fst x, of_val (snd x))) ρ) e.

End NamedSubst.

Module Equivalence.
  Import NamelessSubst.
  Reserved Notation "v1 ≈ v2" (at level 50).

  Inductive val_equiv : relation val :=
  | veqConstr i n (vs1 vs2 : list val) :
      Forall2 (fun v1 v2 => v1 ≈ v2) vs1 vs2 -> vConstr i n vs1 ≈ vConstr i n vs2
  | veqClosLam ρ1 ρ2 nm ty1 e1 e2 :
      inst_env_i ρ1 (eLambda nm ty1 e1) = inst_env_i ρ2 (eLambda nm ty1 e2) ->
      (* ty2 used only by a fixpoint, so it doesn't matter here *)
      forall ty2 ty2', vClos ρ1 nm cmLam ty1 ty2 e1 ≈ vClos ρ2 nm cmLam ty1 ty2' e2
  | veqClosFix ρ1 ρ2 n ty1 ty2 e1 e2 :
      (forall fixname ty2 , inst_env_i ρ1 (eFix fixname n ty1 ty2 e1) =
       inst_env_i ρ2 (eFix fixname n ty1 ty2 e2)) ->
       (forall fixname, vClos ρ1 n (cmFix fixname) ty1 ty2 e1 ≈ vClos ρ2 n (cmFix fixname) ty1 ty2 e2)
   | veqClosTyLam ρ1 ρ2 nm e1 e2 :
       inst_env_i ρ1 (eTyLam nm e1) = inst_env_i ρ2 (eTyLam nm e2) ->
       (* ty2 used only by a fixpoint, so it doesn't matter here *)
       vTyClos ρ1 nm e1 ≈ vTyClos ρ2 nm e2
   | veqTy ty :
       vTy ty ≈ vTy ty
   where
   "v1 ≈ v2" := (val_equiv v1 v2).

   Definition list_val_equiv vs1 vs2 := Forall2 (fun v1 v2 => v1 ≈ v2) vs1 vs2.
   Notation " vs1 ≈ₗ vs2 " := (list_val_equiv vs1 vs2) (at level 50).

   #[export]
   Instance val_equiv_reflexive : Reflexive val_equiv.
   Proof.
     intros v. induction v using val_ind_full.
     + constructor.
       induction l; constructor; inversion H; easy.
     + destruct cm; constructor; reflexivity.
     + constructor. reflexivity.
     + constructor.
   Defined.

   (* TODO: Add the rest to prove that [val_equiv] is indeed an equivalence *)
   Axiom val_equiv_symmetric : Symmetric val_equiv.
   Axiom val_equiv_transitive : Transitive val_equiv.

   #[export]
   Existing Instance val_equiv_symmetric.
   #[export]
   Existing Instance val_equiv_transitive.

   (* TODO: Define these *)
   Axiom list_val_equiv_reflexive : Reflexive list_val_equiv.
   Axiom list_val_equiv_symmetric : Symmetric list_val_equiv.
   Axiom list_val_equiv_transitive : Transitive list_val_equiv.

   #[export]
   Existing Instance list_val_equiv_reflexive.
   #[export]
   Existing Instance list_val_equiv_symmetric.
   #[export]
   Existing Instance list_val_equiv_transitive.

   Lemma list_val_compat v1 v2 vs1 vs2 :
     v1 ≈ v2 -> vs1 ≈ₗ vs2 -> (v1 :: vs1) ≈ₗ (v2 :: vs2).
   Proof.
     intros Heq Heql.
     constructor; easy.
   Qed.

   #[export]
   Instance cons_compat : Proper (val_equiv ==> list_val_equiv ==> list_val_equiv) cons.
   Proof.
      cbv; intros; apply list_val_compat; assumption.
    Defined.

    Lemma constr_cons_compat (vs1 vs2 : list val) (i : inductive) (nm : ename) :
      vs1 ≈ₗ vs2 -> (vConstr i nm vs1) ≈ (vConstr i nm vs2).
    Proof.
      intros Heql.
      constructor.
      induction Heql.
      + constructor.
      + constructor; assumption.
    Defined.

    #[export]
    Instance constr_morph i nm : Proper (list_val_equiv ==> val_equiv) (vConstr i nm).
    Proof.
      cbv; intros; apply constr_cons_compat; assumption.
    Defined.
End Equivalence.
