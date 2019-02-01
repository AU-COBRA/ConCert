(** * Interpreters for the core langage *)
(** Contains two implementations of interpreters with
    different value envirionment representations *)
Require Import Relations Morphisms.
Require Import String.
Require Import List.
Require Import Ast.

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

  (* An interpreter that uses list-like structure to represent environments.
     Currently does not handle recursion [fix] *)

  (* Inspired by this: https://www.cs.bgu.ac.il/~elhadad/advpro/course6.html *)
  Inductive env (A : Type) :=
  | enEmpty  : env A
  | enCons   : name -> A -> env A -> env A
  | enRec    : name -> name -> expr -> type -> type -> env A -> env A.

  Arguments enEmpty {_}.
  Arguments enCons {_}.
  Arguments enRec {_}.

  Fixpoint concat_env {A : Type} (ρ ρ' : env A) :=
    match ρ with
    | enEmpty => ρ'
    | enCons nm v ρ'' => enCons nm v (concat_env ρ'' ρ')
    | enRec fixname nm e ty1 ty2 ρ'' => enRec fixname nm e ty1 ty2 (concat_env ρ'' ρ')
    end.

  Fixpoint list_to_env {A : Type} (xs : list (name * A)) : env A :=
    match xs with
    | [] => enEmpty
    | (k,v) :: xs' => enCons k v (list_to_env xs')
    end.

  Inductive val : Type :=
  | vConstr : inductive -> name -> list val -> val
  | vClos   : env val -> name ->
              type ->(* types are used to convert closures back to lambdas *)
              expr -> val.

  Inductive ForallEnv {A} (P : A -> Prop) : env A -> Prop :=
  | feNil : ForallEnv P enEmpty
  | feCons : forall (nm : name) (a : A) (ρ : env A), P a -> ForallEnv P ρ -> ForallEnv P (enCons nm a ρ)
  | feRec  : forall fixname nm e ty1 ty2 ρ,
      ForallEnv P ρ -> ForallEnv P (enRec fixname nm e ty1 ty2 ρ).


  (* An induction principle that takes into account nested occurences of elements of [val]
     in the list of arguments of [vConstr] and in the environment of [vClos] *)
  Definition val_ind_full
     (P : val -> Prop)
     (Hconstr : forall (i : inductive) (n : name) (l : list val), Forall P l -> P (vConstr i n l))
     (Hclos : forall (ρ : env val) (n : name) (ty : type) (e0 : expr),
          ForallEnv P ρ -> P (vClos ρ n ty e0)) :
    forall v : val, P v.
    refine (fix val_ind_fix (v : val) := _).
    destruct v.
    + apply Hconstr.
      induction l. constructor. constructor. apply val_ind_fix. apply IHl.
    + apply Hclos.
      induction e.
      * constructor.
      * constructor. apply val_ind_fix. apply IHe.
      * constructor. apply IHe.
  Defined.

  (* For some reason, this is not a part of the standard lib *)
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

  Fixpoint lookup (ρ : env val) (key : string) : option val :=
    match ρ with
    | enEmpty => None
    | enCons nm a ρ' =>
      if (nm =? key) then Some a else lookup ρ' key
    | enRec fixname nm e ty1 ty2 ρ' =>
      if (fixname =? key) then Some (vClos ρ nm ty1 e) else lookup ρ' key
    end.

  Notation "ρ # '(' k ')'" := (lookup ρ k) (at level 10).
  (** A value environment extension: *)
  Notation "ρ # [ k ~> v ]" := (enCons k v ρ) (at level 50).

  Fixpoint remove_by_key  (key : name) (ρ : env val) : env val :=
    match ρ with
      | enEmpty => enEmpty
      | enCons nm a ρ' => if (nm =? key) then remove_by_key key ρ'
                           else enCons nm a (remove_by_key key ρ')
      | enRec fixname nm e ty1 ty2 ρ'=> if (fixname =? key) then remove_by_key key ρ'
                          else enRec fixname nm e ty1 ty2 (remove_by_key key ρ')
    end.

  (* This doesn't work for the same reason as for STLC: in the case
     for application we don't know if [b] is decreasing.
     Although, for the relational specification we can prove this using logical relations *)
  Fail Fixpoint expr_eval (ρ : env val) (e : expr) {struct e} : option val :=
      match e with
      | eRel i => None
      | eVar nm => ρ # (nm)
      | eLambda nm ty b =>
        Some (vClos ρ nm ty b)
      | eLetIn nm e1 ty e2 => None
      | eApp e1 e2 =>
        match (expr_eval ρ e1), (expr_eval ρ e2) with
        | Some (vClos ρ' nm _ b), Some v =>
          match (expr_eval (ρ' # [nm ~> v]) b) with
          | Some v' => Some v'
          | None => None
          end
        | Some (vConstr ind n vs), Some v => Some (vConstr ind n (v :: vs))
        | _,_ => None
        end
      | eConstruct t i =>
        Some (vConstr t i [])
      | eConst nm => None
      | eCase (ind,i) ty e bs =>
        match (expr_eval ρ e) with
        | Some (vConstr ind' i _) => if (string_dec ind ind') then
                                        match (List.nth_error bs i) with
                                        | Some v =>  expr_eval ρ (snd v)
                                        | _ => None
                                        end
                                     else None
        | _ => None
        end
      | eFix nm ty b => None
      end.


  Definition ind_name (v : val) :=
    match v with
    | vConstr ind_name _ _ => Some ind_name
    | _ => None
    end.

  Fixpoint match_pat {A} (constr_name : name) (constr_args : list A) (bs : list (pat * expr)) :=
    match bs with
    | [] => None
    | (p, e) :: bs' => if (andb (p.(pName) =? constr_name))
                          (Nat.eqb (length constr_args) (length p.(pVars)))
                     then
                       let assignments := combine p.(pVars) constr_args in
                       Some (assignments,e)
                     else match_pat constr_name constr_args bs'
    end.

  Fixpoint expr_eval (fuel : nat) (Σ : global_env) (ρ : env val) (e : expr) : res val :=
    match fuel with
    | O => NotEnoughFuel
    | S n =>
      match e with
      | eRel i => EvalError "Indices as variables are not supported"
      | eVar nm => option_to_res (ρ # (nm)) (nm ++ " - var not found")
      | eLambda nm ty b =>
        Ok (vClos ρ nm ty b)
      | eLetIn nm e1 ty e2 => todo
      | eApp e1 e2 =>
        match (expr_eval n Σ ρ e1), (expr_eval n Σ ρ e2) with
        | Ok (vClos ρ' nm _ b), Ok v =>
          match (expr_eval n Σ (ρ' # [nm ~> v]) b) with
          | Ok v' => Ok v'
          | err => err
          end
        | Ok (vConstr ind n vs), Ok v => Ok (vConstr ind n (List.app vs [v]))
        | EvalError msg, _ => EvalError msg
        | _, EvalError msg => EvalError msg
        | NotEnoughFuel,_ | _, NotEnoughFuel => NotEnoughFuel
        end
      | eConstr t i =>
        Ok (vConstr t i [])
      | eConst nm => todo
      | eCase (ind,i) ty e bs =>
        match (expr_eval n Σ ρ e) with
        | Ok (vConstr ind' c vs) => if (string_dec ind ind') then
                                      match (match_pat c vs bs) with
                                      | Some (var_assign, v) =>
                                        expr_eval n Σ (concat_env (list_to_env var_assign) ρ) v
                                      | None => EvalError "No such constructor"
                                      end
                                    else EvalError ("Expecting inductive " ++ ind ++
                                                     " but found " ++ ind')
        | v => v
        end
      | eFix fixname vn ty1 ty2 b as e =>
        expr_eval n Σ (enRec fixname vn b ty1 ty2 ρ) (eLambda vn ty1 b)
      end
    end.

  Definition map_env {A B : Type} (f : A -> B) : env A -> env B :=
    fix menv (ρ : env A) :=
      match ρ with
      | enEmpty => enEmpty
      | enCons nm v ρ' => enCons nm (f v) (menv ρ')
      | enRec fixname nm e ty1 ty2 ρ' => enRec fixname nm e ty1 ty2 (menv ρ')
      end.

  Fixpoint env_to_list {A : Type} (ρ : env A) : list (name * A) :=
    match ρ with
    | enEmpty => []
    | enCons nm v ρ' => (nm, v) :: env_to_list ρ'
    | enRec fixname nm e ty1 ty2 ρ' => env_to_list ρ'
    end.

  (* This is equivalent to the composition env_to_list ∘ (map_env f), but
     we if we use the comosition in the definition of from_val, then Coq cannot
     recognise it as a fixpoint. So, we have to merge the two definitions *)
  Definition map_env_list {A B : Type} (f : A -> B) : env A -> list (name * B) :=
    fix menv (ρ : env A) :=
      match ρ with
      | enEmpty => []
      | enCons nm v ρ' => (nm, f v) :: (menv ρ')
      | enRec fixname nm e ty1 ty2 ρ' => menv ρ'
      end.


  Definition lookup_list {A : Type} (ρ : list (name * A)) (key : string) : option A :=
    option_map snd (List.find (fun '(key',v) => if (string_dec key key')
                          then Coq.Init.Datatypes.true else Coq.Init.Datatypes.false) ρ).

  Fixpoint remove_by_key_list (key : name) (ρ : list (name * expr)) : list (name * expr) :=
    match ρ with
      | [] => []
      | (nm,a) :: ρ' => if (nm =? key) then remove_by_key_list key ρ'
                           else (nm, a) :: (remove_by_key_list key ρ')
    end.


    (* NOTE: assumes, that [e] is a closed expression! *)
 Fixpoint subst_env (ρ : list (name * expr)) (e : expr) : expr :=
  match e with
  | eRel i as e' => e'
  | eVar nm  => match lookup_list ρ nm with
                    | Some v => v
                    | None => e
                    end
  | eLambda nm ty b => eLambda nm ty (subst_env (remove_by_key_list nm ρ) b)
  | eLetIn nm e1 ty e2 => eLetIn nm (subst_env ρ e1) ty (subst_env (remove_by_key_list nm ρ) e2)
  | eApp e1 e2 => eApp (subst_env ρ e1) (subst_env ρ e2)
  | eConstr t i as e' => e'
  | eConst nm => eConst nm
  | eCase nm_i ty e bs =>
    (* TODO: this case is not complete! We ignore variables bound by patterns *)
    eCase nm_i ty (subst_env ρ e) (map (fun x => (fst x, subst_env ρ (snd x))) bs)
  | eFix nm v ty1 ty2 b => eFix nm v ty1 ty2 (subst_env (remove_by_key_list v ρ) b)
  end.

  (* Converting from values back to expression.
     This will be used to compare results of the evaluation with different semantics, or
     for stating soundness theorem for the translation to a different language, e.g.
     to Template Coq terms.

     The most non-trival part is to convert closures, for which we have to perform some form
     of subsitution of values from the value environment (see [subst_env])
     Inspired by the implementation of
     "A Certified Implementation of ML with Structural Polymorphism" by Jacques Garrigue.
   *)
  Fixpoint from_val (v : val) : expr :=
    match v with
    | vConstr x i vs => vars_to_apps (eConstr x i) (map from_val vs)
    | vClos ρ nm ty e =>
      match ρ with
      | enRec fixname _ _ ty1 ty2 _ =>
        subst_env (map_env_list from_val ρ) (eFix fixname nm ty ty2 e)
      | _ => subst_env (map_env_list from_val ρ) (eLambda nm ty e)
      end
    end.

  Definition inst_env (ρ : env val) (e : expr) : expr := subst_env (map_env_list from_val ρ) e.

  Reserved Notation "v1 ≈ v2" (at level 50).

  Inductive val_equiv : relation val :=
  | veqConstr i n (vs1 vs2 : list val) :
      Forall2 (fun v1 v2 => v1 ≈ v2) vs1 vs2 -> vConstr i n vs1 ≈ vConstr i n vs2
  | veqClos ρ1 ρ2 nm ty e1 e2 :
      inst_env ρ1 (eLambda nm ty e1) = inst_env ρ2 (eLambda nm ty e2) ->
      vClos ρ1 nm ty e1 ≈ vClos ρ2 nm ty e2
  where
  "v1 ≈ v2" := (val_equiv v1 v2).

  Definition list_val_equiv vs1 vs2 := Forall2 (fun v1 v2 => v1 ≈ v2) vs1 vs2.
  Notation " vs1 ≈ₗ vs2 " := (list_val_equiv vs1 vs2) (at level 50).

  Instance val_equiv_reflexive : Reflexive val_equiv.
  Proof.
    intros v. induction v using val_ind_full.
    + constructor.
      induction l;constructor; inversion H; easy.
    + constructor;reflexivity.
  Defined.

  (* TODO:  Add the rest to prove that [val_equiv] is indeed an equivalence *)
  Axiom val_equiv_symmetric : Symmetric val_equiv.
  Axiom val_equiv_transitive : Transitive val_equiv.

  Existing Instance val_equiv_symmetric.
  Existing Instance val_equiv_transitive.

  Add Relation val val_equiv
      reflexivity proved by val_equiv_reflexive
      symmetry proved by val_equiv_symmetric
      transitivity proved by val_equiv_transitive as val_equiv_rel.

  (* TODO:  Define these  *)
  Axiom list_val_equiv_reflexive : Reflexive list_val_equiv.
  Axiom list_val_equiv_symmetric : Symmetric list_val_equiv.
  Axiom list_val_equiv_transitive : Transitive list_val_equiv.

  Existing Instance list_val_equiv_symmetric.
  Existing Instance list_val_equiv_symmetric.
  Existing Instance list_val_equiv_transitive.

  Add Relation (list val) list_val_equiv
      reflexivity proved by list_val_equiv_reflexive
      symmetry proved by list_val_equiv_symmetric
      transitivity proved by list_val_equiv_transitive as list_val_equiv_rel.

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

End InterpreterEnvList.

Module InterpreterEnvFun.

  (* An interpreter that uses functions to represent environments.
     Moreover, we need partial environments, because recursive environment extension
     might not terminate *)
  Definition env A := name -> res A.
  Definition default_fun_env {A : Type}: env A :=
    fun k => EvalError ("Undefined var :" ++ k).
  Definition in_env {A} k (ρ : env A) := exists v, ρ k = Ok v.

  Definition remove_by_key {A : Type} (key : string) (ρ : InterpreterEnvFun.env A)
  : InterpreterEnvFun.env A :=
  fun key' => if (eqb key key') then (default_fun_env key)
           else ρ key.

  Lemma remove_spec {A} k (ρ : env A) : ~ in_env k (remove_by_key k ρ).
  Proof.
    intros H. unfold in_env,remove_by_key in H.
    destruct H.
    rewrite eqb_refl in H.
    inversion H.
  Qed.


  Inductive val : Type :=
  | vConstr : inductive -> name -> list val -> val
  | vClos   : env val -> name ->
               type (* types are used to convert closures back to lambdas *) ->
               expr -> val.

  Definition ext_env (ρ : env val) (k : name) v :=
    fun k' => if (string_dec k k') then v else ρ k'.

  (* Notation "ρ # '(' k ')'" := (ρ k) (at level 10). *)
  (** A value environment extension: *)
  Notation "ρ # [ k ~> v ]" := (ext_env ρ k v) (at level 50).

  Fixpoint ext_env_list (ρ : env val) (kvs : list (name * val)) :=
    match kvs with
    | [] => ρ
    | (k,v) :: kvs' => ext_env (ext_env_list ρ kvs' ) k (Ok v)
    end.

  Definition ext_env_rec (fixname : name) (var : name) (ty : type) (e : expr)
             (ρ : env val) :=
    fix rec_enc fuel : res (env val) :=
        match fuel with
        | O => NotEnoughFuel
        | S n => Ok (fun k =>
                      if (eqb fixname k) then
                        match rec_enc n with
                        | Ok ρ' => Ok (vClos ρ' var ty e)
                        | EvalError msg => EvalError msg
                        | NotEnoughFuel => NotEnoughFuel
                        end
                      else ρ k)
        end.

  (* This is a simple fact, but it shows that we have two sources of partiality:
     possible non-termination of the recursive context extension and a corresponding
     lookup operation (here it is just a function application, but it returns a
     value of type [res fvar] instead of a plain [fvar] ) *)
  Lemma ext_env_rec_extend_lookup : forall n nm vn ty e ρ ρ',
      ext_env_rec nm vn ty e ρ n = Ok ρ ->
      ρ nm = Ok ρ' ->
    exists ρ'', ρ' = vClos ρ'' vn ty e.
  Proof.
    intros n nm nv ty e ρ ρ' H1 H2. destruct n.
    + inversion H1.
    + destruct n.
      * inversion H1 as [H3]. rewrite <- H3 in H2. rewrite eqb_refl in H2.
        inversion H2.
      * inversion H1 as [H3]. simpl in *.
        rewrite <- H3 in H2.
        rewrite eqb_refl in H2.
        inversion H2. subst.
        eexists.
        inversion_clear H2. f_equal. reflexivity.
  Qed.

  Import Basics.

  Open Scope program_scope.

  Fixpoint expr_eval (fuel : nat) (Σ : global_env) (ρ : env val) (e : expr) : res val :=
    match fuel with
    | O => NotEnoughFuel
    | S n =>
      match e with
      | eRel i => EvalError "Indices as variables are not supported"
      | eVar nm => ρ nm
      | eLambda nm ty b => ret (vClos ρ nm ty b)
      | eLetIn nm e1 ty e2 =>
        expr_eval n Σ (ρ # [nm ~> (expr_eval n Σ ρ e1)]) e2
      | eApp e1 e2 =>
        v1 <- expr_eval n Σ ρ e1 ;;
        v2 <- expr_eval n Σ ρ e2 ;;
        match v1 with
        | vClos ρ' nm _ b =>
          expr_eval n Σ (ρ' # [nm ~> ret v2]) b
        | vConstr ind n vs => ret (vConstr ind n (List.app vs [v2]))
        end
      | eConstr t i =>
        Ok (vConstr t i [])
      | eConst nm => todo
        (* option_to_res (lookup_global Σ nm) ("Constant " ++ nm ++ " not found") *)
      | eCase (ind,i) ty e bs =>
        v <- (expr_eval n Σ ρ e);;
        match v with
        | vConstr ind' c vs =>
          if (string_dec ind ind') then
            (* The pattern-mathcing is the same for the both interpreters,
               so we just reuse it *)
            match (InterpreterEnvList.match_pat c vs bs) with
            | Some (var_assign, v) =>
              expr_eval n Σ (ext_env_list ρ var_assign) v
            | None =>
              EvalError ("No such constructor for inductive " ++ ind)
            end
          else EvalError ("Expecting inductive " ++ ind ++ " but found " ++ ind')
        | _ => EvalError "Not a constructor"
        end
      | eFix fixname vn ty1 ty2 e =>
        ρ' <- ext_env_rec fixname vn ty1 e ρ n ;;
        expr_eval n Σ ρ' (eLambda vn ty1 e)
      end
    end.

  Fixpoint subst_env (ρ : InterpreterEnvFun.env expr) (e : expr) : expr :=
  match e with
  | eRel i as e' => e'
  | eVar nm  => match ρ nm with
                    | Ok v => v
                    | _ => e
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


  (* Cannot make Coq to recognize this as a valid fixpoint *)
  Fail Fixpoint from_val (v : val) {struct v} : expr :=
    match v with
    | vConstr x i vs => vars_to_apps (eConstr x i) (map from_val vs)
    | vClos ρ nm ty e =>
      subst_env (fun k => v <- ρ k ;; ret (from_val v)) (eLambda nm ty e)
    end.
End InterpreterEnvFun.

Module Examples.
  Import BaseTypes.
  Import StdLib.

  Definition prog1 :=
    [|
     (\x : Bool ->
           case x : Bool_name return Bool of
           | true -> false
           | false -> true) true
     |].

  Example eval_prog1 :
    InterpreterEnvList.expr_eval 3 Σ InterpreterEnvList.enEmpty prog1 = Ok (InterpreterEnvList.vConstr "Coq.Init.Datatypes.bool" "false" []).
  Proof. simpl. reflexivity. Qed.

  Example eval_prog1' :
    InterpreterEnvFun.expr_eval 3 Σ InterpreterEnvFun.default_fun_env  prog1 = Ok (InterpreterEnvFun.vConstr "Coq.Init.Datatypes.bool" "false" []).
  Proof. simpl. reflexivity. Qed.
End Examples.