(** * Interpreter for the λsmart langage *)

(** This version of the interpreter supports polymorhic types *)
Require Import String List Bool.

Require Import Ast MyEnv Notations PCUICTranslate.

(* TODO: we use definition of monads from Template Coq,
   but (as actually comment in the [monad_utils] says, we
   should use a real monad library) *)
Require Import MetaCoq.Template.monad_utils.

(* We need some definitions like [All] from utils *)
Require Import MetaCoq.Template.utils.


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

Import Basics.

Open Scope program_scope.

(** A type of labels to distinguish closures corresponding to lambdas and fixpoints *)
Inductive clos_mode : Type :=
  cmLam | cmFix : ename -> clos_mode.

(** Values *)
Inductive val : Type :=
| vConstr : inductive -> ename -> list val -> val
| vClos   : env val -> ename ->
            clos_mode ->
            type ->(* type of the domain *)
            type ->(* type of the codomain *)
            expr -> val
| vTyClos : env val -> ename -> expr -> val
| vTy : type -> val.

Definition AllEnv {A} (P: A -> Type) : env A -> Type := All (P ∘ snd).

(** An induction principle that takes into account nested occurences of elements of [val] in the list of arguments of [vConstr] and in the environment of [vClos] *)
Definition val_ind_full
   (P : val -> Prop)
   (Hconstr : forall (i : inductive) (n : ename) (l : list val), Forall P l -> P (vConstr i n l))
   (Hclos : forall (ρ : env val) (n : ename) (cm : clos_mode) (ty1 ty2 : type) (e0 : expr),
       AllEnv P ρ -> P (vClos ρ n cm ty1 ty2 e0))
   (Htyclos : forall (ρ : env val) (n : ename) (e0 : expr),
       AllEnv P ρ -> P (vTyClos ρ n e0))
   (Hty : forall (t : type),  P (vTy t)) :
  forall v : val, P v.
  refine (fix val_ind_fix (v : val) := _).
  destruct v.
  + apply Hconstr.
    induction l. constructor. constructor. apply val_ind_fix. apply IHl.
  + apply Hclos.
    induction e.
    * constructor.
    * constructor. apply val_ind_fix. apply IHe.
  + apply Htyclos.
    induction e.
    * constructor.
    * constructor. apply val_ind_fix. apply IHe.
  + apply Hty.
Defined.

(** An elimination principle (on a predicate to [Type]) that takes into account nested occurences of elements of [val]
   in the list of arguments of [vConstr] and in the environment of [vClos] *)
Definition val_elim_full
   (P : val -> Type)
   (Hconstr : forall (i : inductive) (n : ename) (l : list val), All P l -> P (vConstr i n l))
   (Hclos : forall (ρ : env val) (n : ename) (cm : clos_mode) (ty1 ty2 : type) (e0 : expr),
       AllEnv P ρ -> P (vClos ρ n cm ty1 ty2 e0))
  (Htyclos : forall (ρ : env val) (n : ename) (e0 : expr),
       AllEnv P ρ -> P (vTyClos ρ n e0))
   (Hty : forall (t : type),  P (vTy t)) :
  forall v : val, P v.
   refine (fix val_ind_fix (v : val) := _).
  destruct v.
  + apply Hconstr.
    induction l. constructor. constructor. apply val_ind_fix. apply IHl.
  + apply Hclos.
    induction e.
    * constructor.
    * constructor. apply val_ind_fix. apply IHe.
  + apply Htyclos.
    induction e.
    * constructor.
    * constructor. apply val_ind_fix. apply IHe.
  + apply Hty.
Defined.

Definition ind_name (v : val) :=
  match v with
  | vConstr ind_ename _ _ => Some ind_ename
  | _ => None
  end.

Open Scope string.

(** Very simple implementation of pattern-matching. Note that we do not match on parameters of constructors coming from parameterised inductives *)
Definition match_pat {A} (cn : ename) (nparam : nat) (arity :list type)
           (constr_args : list A) (bs : list (pat * expr)) :=
  pe <- option_to_res (find (fun x => (fst x).(pName) =? cn) bs) (cn ++ ": not found");;
  let '(p,e) := pe in
  let ctr_len := length constr_args in
  let pt_len := nparam + length p.(pVars) in
  let arity_len := nparam + length arity in
  if (Nat.eqb ctr_len pt_len) then
    if (Nat.eqb ctr_len arity_len) then
      (* NOTE: first [nparam] elements in the [constr_args] are types, so we don't match them *)
      let args := skipn nparam constr_args in
      let assignments := combine p.(pVars) args in
      Ok (assignments,e)
    else EvalError (cn ++ ": constructor arity does not match")
  else EvalError (cn ++ ": pattern arity does not match (constructor: "
                     ++ utils.string_of_nat ctr_len ++ ",
                  pattern: "  ++ utils.string_of_nat pt_len ++ ")").

Fixpoint inductive_name (ty : type) : option ename :=
  match ty with
  | tyInd nm => Some nm
  | tyApp ty1 ty2 => inductive_name ty1
  | _ => None
  end.


(** Some machinery to substitute types during the evaluation. Although we don't care about the types the during evaluation, we need the types later. *)
Fixpoint eval_type_i (k : nat) (ρ : env val) (ty : type) : option type :=
  match ty with
  | tyInd x => Some ty
  | tyForall x ty => ty' <- (eval_type_i (1+k) ρ ty);;
                     ret (tyForall x ty')
  | tyApp ty1 ty2 =>
    ty2' <- eval_type_i k ρ ty2;;
    ty1' <- eval_type_i k ρ ty1;;
    match decompose_inductive ty1' with
    | Some _  => ret (tyApp ty1' ty2')
    | _ => None
    end
  | tyVar nm => None
  | tyRel i => if Nat.leb k i then
                match (lookup_i ρ (i-k)) with
                | Some (vTy ty) => Some ty
                | _ => None
                end
              else None
  | tyArr ty1 ty2 =>
    ty2' <- eval_type_i k ρ ty2;;
    ty1' <- eval_type_i k ρ ty1;;
    Some (tyArr ty1' ty2')
  end.

(** The same as [eval_type_i] but for named variables. NOTE: not up-to-date wrt. eval_type_i *)
Fixpoint eval_type_n (ρ : env val) (ty : type) : option type :=
  match ty with
  | tyInd x => Some ty
  | tyForall x ty => ty' <- eval_type_n (remove_by_key x ρ) ty;;
                     ret (tyForall x ty')
  | tyApp ty1 ty2 =>
    ty2' <- eval_type_n ρ ty2;;
    ty1' <- eval_type_n ρ ty1;;
    match decompose_inductive ty1' with
    | Some _  => ret (tyApp ty1' ty2')
    | _ => None
    end
  | tyVar nm => match lookup ρ nm with
                  | Some (vTy ty) => Some ty
                  | _ => None
                  end
  | tyRel i => None
  | tyArr ty1 ty2 =>
    ty2' <- eval_type_n ρ ty2;;
    ty1' <- eval_type_n ρ ty1;;
    Some (tyArr ty1' ty2')
  end.

Definition eval_ty (enamed : bool) ρ ty err :=
  if enamed then
    option_to_res (eval_type_n ρ ty) err
  else option_to_res (eval_type_i 0 ρ ty) err.

Fixpoint print_type (ty : type) : string :=
  match ty with
  | tyInd x => x
  | tyForall x x0 => "forall " ++ x ++ "," ++ print_type x0
  | tyApp x x0 => "(" ++ print_type x ++ " " ++ print_type x0 ++ ")"
  | tyVar x => x
  | tyRel x => "^" ++ utils.string_of_nat x
  | tyArr x x0 => print_type x ++ "->" ++ print_type x0
  end.

Definition is_type_val (v : val) : bool :=
 match v with
 | vTy ty  => true
 | _ => false
end.

Fixpoint valid_ty_env (n : nat) (ρ : env val) (ty : type): bool :=
  match ty with
  | tyInd x => true
  | tyForall v ty0 => valid_ty_env (S n) ρ ty0
  | tyApp ty1 ty2 => valid_ty_env n ρ ty1 && valid_ty_env n ρ ty2
  | tyVar _ => false
  | tyRel i => if Nat.leb n i then
                match lookup_i ρ (i-n) with
                | Some e => is_type_val e (* if there is somethig in [ρ], it must be a type *)
                | None => true (* if nothing there, that's ok *)
                end
              else true
  | tyArr ty1 ty2 => valid_ty_env n ρ ty1 && valid_ty_env n ρ ty2
  end.

Definition valid_env (ρ : env val) : nat -> expr -> bool:=
  fix rec n e :=
    match e with
    | eRel i => true
    | eVar nm  => false
    | eLambda nm ty b => valid_ty_env n ρ ty && rec (1+n) b
    | eTyLam nm b => rec (1+n) b
    | eLetIn nm e1 ty e2 => rec n e1 && valid_ty_env n ρ ty && rec (1+n) e2
    | eApp e1 e2 => rec n e1 && rec n e2
    | eConstr t i as e' => true
    | eConst nm => true
    | eCase nm_i ty e bs =>
      let bs'' := List.forallb
                    (fun x => rec (length (pVars (fst x)) + n) (snd x)) bs in
      forallb (valid_ty_env n ρ) (snd nm_i) && valid_ty_env n ρ ty && rec n e && bs''
    | eFix nm v ty1 ty2 b => valid_ty_env n ρ ty1 && valid_ty_env n ρ ty2 && rec (2+n) b
    | eTy ty => valid_ty_env n ρ ty
    end.

Definition validate (enamed : bool) (ρ : env val) (n : nat) (e : expr) : res unit :=
  if enamed then Ok tt (* we validate only for the "indexed" mode *)
  else
    if valid_env ρ n e then Ok tt else EvalError "Invalid environment".

Definition validate_branches (enamed : bool) (ρ : env val) (es : list (pat * expr)) : res unit :=
  if enamed then
    Ok tt (* we validate only for the "indexed" mode *)
  else
    if forallb (fun x => valid_env ρ #|(fst x).(pVars)| (snd x)) es then Ok tt else EvalError "Invalid environment".


(** The interpreter works for both enamed and enameless representation of Oak expressions, depending on a parameter [enamed]. Due to the potential non-termination of Oak programs, we define our interpreter using a fuel idiom: by structural recursion on an additional argument (a natural number). We keep types in during evaluation, because for the soundness theorem we would have to translate values back to expression and then further to MetaCoq terms. This requires us to keep all types in place. In addition to this interpreter, we plan to implement another one which computes on terms after erasure of typing information. *)

Definition expr_eval_general : bool -> global_env -> nat -> env val -> expr -> res val :=
  fun (enamed : bool) (Σ : global_env) =>
    fix eval fuel ρ e :=
    match fuel with
    | O => NotEnoughFuel
    | S n =>
      match e with
      | eRel i => if enamed then EvalError "Indices as variables are not supported"
                 else option_to_res (lookup_i ρ i) ("var not found")
      | eVar nm => if enamed then
                    option_to_res (ρ # (nm)) (nm ++ " - var not found")
                  else EvalError (nm ++ " variable found, but enamed variables are not supported")
      | eLambda nm ty b =>
        (* NOTE: we pass the same type as the codomain type here
          (because it's not needed for lambda).
          Maybe separate constructors for lambda/fixpoint closures would be better? *)
        ty_v <- eval_ty enamed ρ ty "Type error";;
        validate enamed ρ 1 b;;
        Ok (vClos ρ nm cmLam ty_v ty_v b)
      | eLetIn nm e1 ty e2 =>
        v <- eval n ρ e1 ;;
        ty <- eval_ty enamed ρ ty "Type error";;
        eval n (ρ # [nm ~> v]) e2
      | eApp e1 e2 =>
           v2 <- eval n ρ e2;;
           v1 <- eval n ρ e1;;
          match v1,v2 with
          | vClos ρ' nm cmLam _ _ b, v =>
            eval n (ρ' # [nm ~> v]) b
          | vClos ρ' nm (cmFix fixename) ty1 ty2 b, v =>
            match v with
            | vConstr ind ctor vs =>
              let v_fix := (vClos ρ' nm (cmFix fixename) ty1 ty2 b) in
              eval n (ρ' # [fixename ~> v_fix] # [nm ~> v]) b
            | _ => EvalError "Fix should be applied to an inductive"
            end
          | vTyClos ρ' nm b, v =>
              eval n (ρ' # [nm ~> v]) b
          | vConstr ind n vs, v => Ok (vConstr ind n (List.app vs [v]))
          | _, _ => EvalError "eApp : not a constructor or closure"
          end
      | eConstr ind ctor =>
          match (resolve_constr Σ ind ctor) with
          | Some _ => Ok (vConstr ind ctor [])
          | _ => EvalError "No constructor or inductive found"
          end
      | eConst nm => todo (* we assume that all external references were resolved *)
      | eCase (ind,params) ty e bs =>
        validate_branches enamed ρ bs;;
        ty_v <- eval_ty enamed ρ ty "Type Error";;
        _ <- monad_map (fun x => eval_ty enamed ρ x "Type Error") params;;
        match eval n ρ e with
        | Ok (vConstr ind' c vs) =>
          if (string_dec ind ind') then
            match resolve_constr Σ ind' c with
            | Some ((nparams,_),ci) =>
              if Nat.eqb nparams #|params| then
                pm_res <- match_pat c nparams ci vs bs;;
                let '(var_assign, v) := pm_res in
                eval n (List.app (List.rev var_assign) ρ) v
              else EvalError "Case: number of params doesn't match with the definition"
          | None => EvalError "No constructor or inductive found in the global environment"
            end
          else EvalError ("Expecting inductive " ++ ind ++ " but found " ++ ind')
        | Ok (vTy ty) => EvalError ("Discriminee cannot be a type : " ++ print_type ty)
        | Ok _ => EvalError "Discriminee should evaluate to a constructor"
        | v => v
          end
      | eFix fixename vn ty1 ty2 b as e =>
        validate enamed ρ 2 b;;
        ty_v1 <- eval_ty enamed ρ ty1 "Type error";;
        ty_v2 <- eval_ty enamed ρ ty2 "Type error";;
        Ok (vClos ρ vn (cmFix fixename) ty_v1 ty_v2 b)
      | eTyLam nm e =>
        validate enamed ρ 1 e;;
        Ok (vTyClos ρ nm e)
      | eTy ty =>
        let error := "Error while evaluating type: " ++ print_type ty in
        ty' <- eval_ty enamed ρ ty error;; ret (vTy ty')
      end
    end.

Definition expr_eval_n := expr_eval_general true.
Definition expr_eval_i := expr_eval_general false.

Module Examples.
  Import BaseTypes.
  Import StdLib.

  Open Scope string.
  Definition x :="x".

  Definition prog1 :=
    [|
     (\x : Bool =>
           case x : Bool return Bool of
           | True -> False
           | False -> True) True
     |].

  Example eval_prog1_named :
    expr_eval_n Σ 3 [] prog1 = Ok (vConstr "Coq.Init.Datatypes.bool" "false" []).
  Proof. reflexivity. Qed.

  Example eval_prog1_indexed :
    expr_eval_i Σ 3 [] (indexify [] prog1) = Ok (vConstr "Coq.Init.Datatypes.bool" "false" []).
  Proof. simpl. reflexivity. Qed.

  End Examples.