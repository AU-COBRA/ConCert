(** * Interpreter for the monomorphic fragment of the Oak langage *)
Require Import Relations Morphisms.
Require Import String.
Require Import List.
Require Import Ast MyEnv.

(* TODO: we use definition of monads from Template Coq,
   but (as actually comment in the [monad_utils] says, we
   should use a real monad library) *)
Require Import Template.monad_utils.


Import ListNotations.
Import MonadNotation.

(* Common definitions *)

Inductive res A :=
| Ok : A -> res A
| NotEnoughFuel : res A
| EvalError : string -> res A.


Arguments Ok {_}.
Arguments NotEnoughFuel {_}.
Arguments EvalError {_}.

Instance res_monad : Monad res :=
  { ret := @Ok;
    bind := fun _ _ r f => match r with
                    | Ok v => f v
                    | EvalError msg => EvalError msg
                    | NotEnoughFuel => NotEnoughFuel
                        end }.

Definition res_map {A B} (f : A -> B) (r : res A) : res B :=
  v <- r ;;
  ret (f v).

Definition option_to_res {A : Type} (o : option A) (msg : string) :=
  match o with
  | Some v => Ok v
  | None => EvalError msg
  end.

Definition todo {A} := EvalError (A:=A) "Not implemented".

Module InterpreterEnvList.

  Import Basics.

  Open Scope program_scope.

  (** A type of labels to distinguish closures corresponding to lambdas and fixpoints *)
  Inductive clos_mode : Type :=
    cmLam | cmFix : name -> clos_mode.

  (** Values *)
  Inductive val : Type :=
  | vConstr : inductive -> name -> list val -> val
  | vClos   : env val -> name ->
              clos_mode ->
              type ->(* type of the domain *)
              type ->(* type of the codomain *)
              expr -> val.

  Definition ForallEnv {A} (P: A -> Prop) : env A -> Prop := Forall (P ∘ snd).

  (** Value is well-formed if expressions in closures are appropriately closed *)
  Inductive val_ok Σ : val -> Prop :=
  | vokClosLam : forall e nm ρ ty1 ty2,
      ForallEnv (val_ok Σ) ρ ->
      iclosed_n (1 + length ρ) e = true ->
      val_ok Σ (vClos ρ nm cmLam ty1 ty2 e)
  | vokClosFix : forall e nm fixname ρ ty1 ty2,
      ForallEnv (val_ok Σ) ρ ->
      iclosed_n (2 + length ρ) e = true ->
      val_ok Σ (vClos ρ nm (cmFix fixname) ty1 ty2 e)
  | vokContr : forall i nm vs ci,
      Forall (val_ok Σ) vs ->
      resolve_constr Σ i nm = Some ci ->
      val_ok Σ (vConstr i nm vs).

  Definition env_ok Σ (ρ : env val) := ForallEnv (val_ok Σ) ρ.

  (** An induction principle that takes into account nested occurrences of elements of [val] in the list of arguments of [vConstr] and in the environment of [vClos] *)
  Definition val_ind_full
     (P : val -> Prop)
     (Hconstr : forall (i : inductive) (n : name) (l : list val), Forall P l -> P (vConstr i n l))
     (Hclos : forall (ρ : env val) (n : name) (cm : clos_mode) (ty1 ty2 : type) (e0 : expr),
          ForallEnv P ρ -> P (vClos ρ n cm ty1 ty2 e0)) :
    forall v : val, P v.
    refine (fix val_ind_fix (v : val) := _).
    destruct v.
    + apply Hconstr.
      induction l. constructor. constructor. apply val_ind_fix. apply IHl.
    + apply Hclos.
      induction e.
      * constructor.
      * constructor. apply val_ind_fix. apply IHe.
  Defined.

  (** For some reason, this is not a part of the standard lib *)
  Lemma Forall_app {A} (l1 l2 : list A) P :
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
  Proof.
    split.
    - intros H. induction l1.
      + simpl in *. easy.
      + simpl in *. inversion H. subst.
        split.
        * constructor. assumption.
          destruct (IHl1 H3). assumption.
        * destruct (IHl1 H3). assumption.
    - intros H. induction l1.
      + simpl in *. easy.
      + simpl in *. destruct H as [H1 H2].
        constructor;inversion H1;auto.
  Qed.

  Lemma Forall_rev {A} {l : list A} P : Forall P l -> Forall P (rev l).
  Proof.
    intros H.
    induction l.
    + constructor.
    + simpl. apply Forall_app.
      inversion H;auto.
  Qed.

  Definition ind_name (v : val) :=
    match v with
    | vConstr ind_name _ _ => Some ind_name
    | _ => None
    end.

  (** Very simple implementation of pattern-matching *)
  Definition match_pat {A} (cn : name) (arity :list type)
             (constr_args : list A) (bs : list (pat * expr)) :=
    pe <- find (fun x => (fst x).(pName) =? cn) bs;;
    let '(p,e) := pe in
    if (andb (Nat.eqb (length constr_args) (length p.(pVars)))
             (Nat.eqb (length constr_args) (length arity))) then
      let assignments := combine p.(pVars) constr_args in
      Some (assignments,e)
    else None.

  (** ** The interpreter *)

  (** The interpreter works for both named and nameless representation of Oak expressions, depending on a parameter [named]. Due to the potential non-termination of Oak programs, we define our interpreter using a fuel idiom: by structural recursion on an additional argument (a natural number). *)
  Fixpoint expr_eval_general (fuel : nat) (named : bool) (Σ : global_env)
           (ρ : env val) (e : expr) : res val :=
    match fuel with
    | O => NotEnoughFuel
    | S n =>
      match e with
      | eRel i => if named then EvalError "Indices as variables are not supported"
                  else option_to_res (lookup_i ρ i) ("var not found")
      | eVar nm => if named then
                    option_to_res (ρ # (nm)) (nm ++ " - var not found")
                  else EvalError (nm ++ " variable found, but named variables are not supported")
      | eLambda nm ty b =>
      (* NOTE: we pass the same type as the codomain type here
        (because it's not needed for lambda).
        Maybe separate constructors for lambda/fixpoint closures would be better? *)
        Ok (vClos ρ nm cmLam ty ty b)
      | eLetIn nm e1 ty e2 =>
        v <- expr_eval_general n named Σ ρ e1 ;;
        expr_eval_general n named Σ (ρ # [nm ~> v]) e2
      | eApp e1 e2 =>
        match (expr_eval_general n named Σ ρ e1), (expr_eval_general n named Σ ρ e2) with
        | Ok (vClos ρ' nm cmLam _ _ b), Ok v =>
          res <- (expr_eval_general n named Σ (ρ' # [nm ~> v]) b);;
          ret res
        | Ok (vClos ρ' nm (cmFix fixname) ty1 ty2 b), Ok v =>
          let v_fix := (vClos ρ' nm (cmFix fixname) ty1 ty2 b) in
          res <- expr_eval_general n named Σ (ρ' # [fixname ~> v_fix] # [nm ~> v]) b;;
          ret res
        | Ok (vConstr ind n vs), Ok v => Ok (vConstr ind n (List.app vs [v]))
        | EvalError msg, _ => EvalError msg
        | _, EvalError msg => EvalError msg
        | NotEnoughFuel,_ | _, NotEnoughFuel => NotEnoughFuel
        end
      | eConstr ind ctor =>
        match (resolve_constr Σ ind ctor) with
        | Some _ => Ok (vConstr ind ctor [])
        | _ => EvalError "No constructor or inductive found"
        end
      | eConst nm => todo
      | eCase (ind,i) ty e bs =>
        match (expr_eval_general n named Σ ρ e) with
        | Ok (vConstr ind' c vs) =>
          match resolve_constr Σ ind' c with
          | Some (_,ci) =>
            (* TODO : move cheking inductive names before
               resolving the constructor *)
            if (string_dec ind ind') then
              match (match_pat c ci vs bs) with
              | Some (var_assign, v) =>
                expr_eval_general n named Σ (List.app (rev var_assign) ρ) v
              | None => EvalError "No such constructor"
              end
            else EvalError ("Expecting inductive " ++ ind ++
                            " but found " ++ ind')
            | None => EvalError "No constructor or inductive found in the global envirionment"
          end
        | Ok _ => EvalError "Discriminee should evaluate to a constructor"
        | v => v
        end
      | eFix fixname vn ty1 ty2 b as e =>
        Ok (vClos ρ vn (cmFix fixname) ty1 ty2 b)
      end
    end.

  Definition expr_eval_n n := expr_eval_general n true.
  Definition expr_eval_i n := expr_eval_general n false.

  (** * Converting values to expressions *)
  (** Proving soundness of the embedding requires comparing of values to the MetaCoq terms. In order to accomplish this we need some way of first instantiating all closures with the values contained in the environments for a given closure *)


  (** Substitution of an environment to an expression. NOTE: assumes, that expression in [ρ] are closed! *)

 Fixpoint subst_env (ρ : list (name * expr)) (e : expr) : expr :=
  match e with
  | eRel i as e' => e'
  | eVar nm  => match lookup ρ nm with
                    | Some v => v
                    | None => e
                    end
  | eLambda nm ty b => eLambda nm ty (subst_env (remove_by_key nm ρ) b)
  | eLetIn nm e1 ty e2 => eLetIn nm (subst_env ρ e1) ty (subst_env (remove_by_key nm ρ) e2)
  | eApp e1 e2 => eApp (subst_env ρ e1) (subst_env ρ e2)
  | eConstr t i as e' => e'
  | eConst nm => eConst nm
  | eCase nm_i ty e bs =>
    (* TODO: this case is not complete! We ignore variables bound by patterns *)
    eCase nm_i ty (subst_env ρ e) (map (fun x => (fst x, subst_env ρ (snd x))) bs)
  | eFix nm v ty1 ty2 b => eFix nm v ty1 ty2 (subst_env (remove_by_key v ρ) b)
  end.

  (* NOTE: assumes, that expression in [ρ] are closed! *)
 Fixpoint subst_env_i_aux (k : nat) (ρ : env expr) (e : expr) : expr :=
  match e with
  | eRel i => if Nat.leb k i then
               from_option (lookup_i ρ (i-k)) (eRel i) else eRel i
  | eVar nm  => eVar nm
  | eLambda nm ty b => eLambda nm ty (subst_env_i_aux (1+k) ρ b)
  | eLetIn nm e1 ty e2 => eLetIn nm (subst_env_i_aux k ρ e1) ty (subst_env_i_aux (1+k) ρ e2)
  | eApp e1 e2 => eApp (subst_env_i_aux k ρ e1) (subst_env_i_aux k ρ e2)
  | eConstr t i as e' => e'
  | eConst nm => eConst nm
  | eCase nm_i ty e bs =>
    eCase nm_i ty (subst_env_i_aux k ρ e)
          (map (fun x => (fst x, subst_env_i_aux (length (fst x).(pVars) + k) ρ (snd x))) bs)
  | eFix nm v ty1 ty2 b => eFix nm v ty1 ty2 (subst_env_i_aux (2+k) ρ b)
  end.

 Definition subst_env_i := subst_env_i_aux 0.

  (** Converting from values back to expression. The most non-trivial part is to convert closures, for which we have to perform some form
     of substitution of values from the value environment (see [subst_env], [subst_env_i]). Inspired by the implementation of "A Certified Implementation of ML with Structural Polymorphism" by Jacques Garrigue. *)
  Fixpoint from_val (v : val) : expr :=
    match v with
    | vConstr x i vs => vars_to_apps (eConstr x i) (map from_val vs)
    | vClos ρ nm cm ty1 ty2 e =>
      let res := match cm with
                 | cmLam => eLambda nm ty1 e
                 | cmFix fixname => eFix fixname nm ty1 ty2 e
                 end
      in subst_env (map (fun x => (fst x, from_val (snd x))) ρ) res
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
    end.

  Notation "e .[ ρ ] n " := (subst_env_i_aux n ρ e) (at level 50).

 Definition inst_env_i (ρ : env val) (e : expr) : expr :=
   subst_env_i (map (fun x => (fst x, from_val_i (snd x))) ρ) e.
 Notation "e .[ ρ ]" := (subst_env_i ρ e) (at level 50).


 (** Values are equivalent up to subsitution of corresponding environments in closures *)
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

    Lemma constr_cons_compat (vs1 vs2 : list val) (i : inductive) (nm : name) :
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

End InterpreterEnvList.

Module Examples.
  Import BaseTypes.
  Import StdLib.

  Definition prog1 :=
    [|
     (\x : Bool ->
           case x : Bool return Bool of
           | true -> false
           | false -> true) true
     |].

  Example eval_prog1_named :
    InterpreterEnvList.expr_eval_n 3 Σ [] prog1 = Ok (InterpreterEnvList.vConstr "Coq.Init.Datatypes.bool" "false" []).
  Proof. simpl. reflexivity. Qed.

  Example eval_prog1_indexed :
    InterpreterEnvList.expr_eval_i 3 Σ [] (indexify [] prog1) = Ok (InterpreterEnvList.vConstr "Coq.Init.Datatypes.bool" "false" []).
  Proof. simpl. reflexivity. Qed.

  End Examples.
