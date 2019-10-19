(** * Convertion from values back to expressions through the environment substitution *)
Require Import List Bool Relations Morphisms ssrbool PeanoNat.
Require Import MetaCoq.Template.utils.

Require Import Ast CustomTactics Misc.
Require Import EvalE.
Require Import MyEnv.

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
                    from_option (lookup_ty ρ (i-k)) (tyRel i) else tyRel i
      | tyArr ty1 ty2 =>
        let ty2' := subst_env_i_ty k ρ ty2 in
        let ty1' := subst_env_i_ty k ρ ty1 in
        tyArr ty1' ty2'
      end.


   (** NOTE: assumes, that expression in [ρ] are closed! *)
  Fixpoint subst_env_i_aux (k : nat) (ρ : env expr) (e : expr) : expr :=
    match e with
    | eRel i => if Nat.leb k i then
                 from_option (lookup_i ρ (i-k)) (eRel i) else eRel i
    | eVar nm  => eVar nm
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
       This will be used to compare results of the evaluation with different semantics, or
       for stating soundness theorem for the translation to a different language, e.g.
       to Template Coq terms.

       The most non-trivial part is to convert closures, for which we have to perform some form
       of substitution of values from the value environment (see [subst_env])
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
    induction ρ;intros n0 Hρ.
    + easy.
    + destruct a;simpl in *.
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
    induction ρ;intros n1 Hlt.
    + easy.
    + destruct (Nat.eqb n1 0) eqn:Hn1.
      * destruct a. eexists. split.
        ** simpl. rewrite Hn1.
           reflexivity.
        ** simpl in *. unfold inst_env_i,subst_env_i. simpl.
           assert (n1=0) by (apply EqNat.beq_nat_eq; easy).
           subst. simpl. reflexivity.
      * destruct a.
        assert (Hn2 : {n2 | n1 = S n2}) by (destruct n1 as [ | n2]; tryfalse; exists n2; reflexivity).
        destruct Hn2 as [n2 Heq_n2]. replace (n1-1) with n2 by lia.
        subst. simpl in Hlt. unfold is_true in *. rewrite Nat.ltb_lt in Hlt.
        apply Lt.lt_S_n in Hlt. rewrite <- Nat.ltb_lt in Hlt.
        specialize (IHρ _ Hlt). destruct IHρ as [v1 HH]. destruct HH as [H1 H2].
        exists v1. split.
        ** simpl in *. replace (n2 - 0) with n2 by lia. assumption.
        ** specialize (lookup_i_length _ _ Hlt) as Hlookup.
           destruct Hlookup.
           simpl in *. unfold inst_env_i,subst_env_i in *. simpl in *.
           rewrite <- H2. replace (n2 - 0) with n2 by lia.
           apply lookup_i_of_val_env in H1.
           now eapply from_option_indep.
  Qed.

End NamelessSubst.

(** ** Substitution for the named representation *)
Module NamedSubst.

  (** Currenlty we do not use named substitution in our soundness proof. *)

  (** NOTE: assumes, that expression in [ρ] are closed! *)
 Fixpoint subst_env (ρ : list (ename * expr)) (e : expr) : expr :=
  match e with
  | eRel i as e' => e'
  | eVar nm  => match lookup ρ nm with
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
