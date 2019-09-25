(** * Convertion from values back to expressions through the environment substitution *)
Require Import List Bool Relations Morphisms ssrbool.
Require Import MetaCoq.Template.utils.

Require Import Ast.
Require Import EvalE.
Require Import MyEnv.

Import InterpreterEnvList.

(** Substitution for the named representation *)
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


 (** Substitution for the nameless representation *)

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

  (* Converting from values back to expression.
     This will be used to compare results of the evaluation with different semantics, or
     for stating soundness theorem for the translation to a different language, e.g.
     to Template Coq terms.

     The most non-trivial part is to convert closures, for which we have to perform some form
     of substitution of values from the value environment (see [subst_env])
     Inspired by the implementation of
     "A Certified Implementation of ML with Structural Polymorphism" by Jacques Garrigue.
   *)
  Fixpoint from_val (v : val) : expr :=
    match v with
    | vConstr x i vs => vars_to_apps (eConstr x i) (map from_val vs)
    | vClos ρ nm cm ty1 ty2 e =>
      let res := match cm with
                 | cmLam => eLambda nm ty1 e
                 | cmFix fixname => eFix fixname nm ty1 ty2 e
                 end
      in subst_env (map (fun x => (fst x, from_val (snd x))) ρ) res
    | vTyClos ρ nm e => subst_env (map (fun x => (fst x, from_val (snd x))) ρ)
                                 (eTyLam nm e)
    | vTy ty => eTy ty
    end.

  Definition inst_env (ρ : env val) (e : expr) : expr :=
    subst_env (map (fun x => (fst x, from_val (snd x))) ρ) e.

  Fixpoint from_val_i (v : val) : expr :=
    match v with
    | vConstr x i vs => vars_to_apps (eConstr x i) (map from_val_i vs)
    | vClos ρ nm cm ty1 ty2 e =>
      let res := match cm with
                 | cmLam => eLambda nm ty1 e
                 | cmFix fixname => eFix fixname nm ty1 ty2 e
                end
      in subst_env_i (map (fun x => (fst x, from_val_i (snd x))) ρ) res
    | vTyClos ρ nm e => subst_env_i (map (fun x => (fst x, from_val_i (snd x))) ρ)
                                 (eTyLam nm e)
    | vTy ty => eTy ty

    end.

  Notation exprs := (map (fun x => (fst x, from_val_i (snd x)))).

  (* The similar notation will be used when we change to a parallel substitution *)
  Notation "e .[ ρ ] n " := (subst_env_i_aux n ρ e) (at level 6).

 Definition inst_env_i (ρ : env val) (e : expr) : expr :=
   subst_env_i (map (fun x => (fst x, from_val_i (snd x))) ρ) e.
 Notation "e .[ ρ ]" := (subst_env_i ρ e) (at level 6).

 Definition is_type e : bool :=
   match expr_to_ty e with
   | Some _ => true
   | _ => false
  end.

  Fixpoint ty_env_ok (n : nat) (ρ : env expr) (ty : type): bool :=
    match ty with
    | tyInd x => true
    | tyForall v ty0 => ty_env_ok (S n) ρ ty0
    | tyApp ty1 ty2 => ty_env_ok n ρ ty1 && ty_env_ok n ρ ty2
    | tyVar _ => false
    | tyRel i => if Nat.leb n i then
                  match lookup_i ρ (i-n) with
                  | Some e => is_type e (* if there is somethig in [ρ], it must be a type *)
                  | None => true (* if nothing there, that's ok *)
                  end
                else true
    | tyArr ty1 ty2 => ty_env_ok n ρ ty1 && ty_env_ok n ρ ty2
    end.

  Definition ty_expr_env_ok (ρ : env expr) : nat -> expr -> bool:=
    fix rec n e :=
      match e with
      | eRel i => true
      | eVar nm  => false
      | eLambda nm ty b => ty_env_ok n ρ ty && rec (1+n) b
      | eTyLam nm b => rec (1+n) b
      | eLetIn nm e1 ty e2 => rec n e1 && ty_env_ok n ρ ty && rec (1+n) e2
      | eApp e1 e2 => rec n e1 && rec n e2
      | eConstr t i as e' => true
      | eConst nm => true
      | eCase nm_i ty e bs =>
        let bs'' := List.forallb
                      (fun x => rec (length (pVars (fst x)) + n) (snd x)) bs in
        forallb (ty_env_ok n ρ) (snd nm_i) && ty_env_ok n ρ ty && rec n e && bs''
      | eFix nm v ty1 ty2 b => ty_env_ok n ρ ty1 && ty_env_ok n ρ ty2 && rec (2+n) b
      | eTy ty => ty_env_ok n ρ ty
      end.


  Inductive ty_val : type -> Type :=
  | vtyInd : forall ind, ty_val (tyInd ind)
  | vtyRel : forall i, ty_val (tyRel i)
  | vtyForall : forall nm ty , ty_val ty -> ty_val (tyForall nm ty)
  | vtyApp : forall ty1 ty2 ind tys,
      decompose_inductive ty1 = Some (ind, tys) ->
      ty_val ty1 ->
      ty_val ty2 ->
      ty_val (tyApp ty1 ty2)
  | vtyArr : forall ty1 ty2,
      ty_val ty1 ->
      ty_val ty2 ->
      ty_val (tyArr ty1 ty2).


 Inductive val_ok Σ : val -> Type :=
  | vokClosLam : forall e nm ρ ty1 ty2,
      AllEnv (val_ok Σ) ρ ->
      ty_expr_env_ok (exprs ρ) 1 e ->
      iclosed_n (1 + length ρ) e ->
      iclosed_ty 0 ty1 ->
      iclosed_ty 0 ty2 ->
      ty_val ty1 ->
      ty_val ty2 ->
      val_ok Σ (vClos ρ nm cmLam ty1 ty2 e)
  | vokClosFix : forall e nm fixename ρ ty1 ty2,
      AllEnv (val_ok Σ) ρ ->
      ty_expr_env_ok (exprs ρ) 2 e ->
      iclosed_n (2 + length ρ) e ->
      iclosed_ty 0 ty1 ->
      iclosed_ty 0 ty2 ->
      ty_val ty1 ->
      ty_val ty2 ->
      val_ok Σ (vClos ρ nm (cmFix fixename) ty1 ty2 e)
  | vokTyClos : forall e nm ρ,
      AllEnv (val_ok Σ) ρ ->
      ty_expr_env_ok (exprs ρ) 1 e ->
      iclosed_n (1 + length ρ) e ->
      val_ok Σ (vTyClos ρ nm e)
  | vokContr : forall i nm vs ci,
      All (val_ok Σ) vs ->
      resolve_constr Σ i nm = Some ci ->
      val_ok Σ (vConstr i nm vs)
  | vokTy : forall ty,
      iclosed_ty 0 ty ->
      ty_val ty ->
      val_ok Σ (vTy ty).

 Definition env_ok Σ (ρ : env val) := AllEnv (val_ok Σ) ρ.

 Definition constr_ok (nparam : nat) (c : constr) : bool :=
   forallb (iclosed_ty nparam) (map snd c.2).

 Definition global_dec_ok (gd : global_dec) : bool :=
   match gd with
   | gdInd _ nparam cs _ => forallb (constr_ok nparam) cs
   end.

 Definition genv_ok Σ := forallb global_dec_ok Σ.

 Module Equivalence.
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

   Instance val_equiv_reflexive : Reflexive val_equiv.
   Proof.
     intros v. induction v using val_ind_full.
     + constructor.
       induction l;constructor; inversion H; easy.
     + destruct cm;constructor;reflexivity.
     + constructor. reflexivity.
     + constructor.
   Defined.

   (* TODO:  Add the rest to prove that [val_equiv] is indeed an equivalence *)
   Axiom val_equiv_symmetric : Symmetric val_equiv.
   Axiom val_equiv_transitive : Transitive val_equiv.

   Existing Instance val_equiv_symmetric.
   Existing Instance val_equiv_transitive.

   (* TODO:  Define these  *)
   Axiom list_val_equiv_reflexive : Reflexive list_val_equiv.
   Axiom list_val_equiv_symmetric : Symmetric list_val_equiv.
   Axiom list_val_equiv_transitive : Transitive list_val_equiv.

   Existing Instance list_val_equiv_reflexive.
   Existing Instance list_val_equiv_symmetric.
   Existing Instance list_val_equiv_transitive.

   Lemma list_val_compat v1 v2 vs1 vs2 :
     v1 ≈ v2 -> vs1 ≈ₗ vs2 -> (v1 :: vs1) ≈ₗ (v2 :: vs2).
   Proof.
     intros Heq Heql.
     constructor;easy.
   Qed.

   Instance cons_compat : Proper (val_equiv ==> list_val_equiv ==> list_val_equiv) cons.
   Proof.
      cbv;intros;apply list_val_compat;assumption.
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

    Instance constr_morph i nm : Proper (list_val_equiv ==> val_equiv) (vConstr i nm).
    Proof.
      cbv;intros;apply constr_cons_compat;assumption.
    Defined.

  End Equivalence.
