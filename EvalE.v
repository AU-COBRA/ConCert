Require Import String.
Require Import List.
Require Import Ast.

(* TODO: we use definition of monads from Template Coq,
   but (as actually comment in the [monad_utils] says, we
   should use a real monad library. )*)
Require Import Template.monad_utils.


Import ListNotations.
Import MonadNotation.

Module Interpreter.

  Definition env A := list (string * A).

  Definition lookup {A : Type} (ρ : env A) (key : string) : option A :=
    option_map snd (List.find (fun '(key',v) => if (string_dec key key')
                          then Coq.Init.Datatypes.true else Coq.Init.Datatypes.false) ρ).

  Notation "ρ # '(' k ')'" := (lookup ρ k) (at level 10).
  (** A value environment extension: *)
  Notation "E # [ k ~> v ]" := ((k,v) :: E) (at level 50).


  Inductive val : Type :=
  | vConstr : inductive -> name -> list val -> val
  | vClos   : env val -> name ->
              type (*types are used to convert closures back to lambdas *) ->
              expr -> val.

  (* This doesn't work for the same reason as for STLC: in the case
     for application we don't know if [b] is decreasing.
     Alhough, for the relational specification we can prove this using logical relations *)
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

  Definition option_to_res {A : Type} (o : option A) (msg : string) :=
    match o with
    | Some v => Ok v
    | None => EvalError msg
    end.

  Definition todo {A} := EvalError (A:=A) "Not implemented".

  Definition ind_name (v : val) :=
    match v with
    | vConstr ind_name _ _ => Some ind_name
    | _ => None
    end.

  (* FIXME: should be extended to match the arguments of the constructor *)
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
      | eVar nm => option_to_res (ρ # (nm)) ("Var not found: " ++ nm)
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
                                      | Some (var_assign, v) => expr_eval n Σ (List.app ρ var_assign) v
                                      | None => EvalError "No such constructor"
                                      end
                                    else EvalError ("Expecting inductive " ++ ind ++
                                                     " but found " ++ ind')
        | v => v
        end
      | eFix fixname vn ty1 ty2 b as e =>
        let lam := eLambda vn ty1 b in
        (* ρ below should be be extended recursively as well :( *)
        match (expr_eval n Σ ρ lam) with
        | Ok v' => Ok (vClos (ρ # [fixname ~> v']) vn ty1 b )
        | e => e
        end
         (* expr_eval n Σ (ρ # [fixname ~> vClos ρ fixname (tyArr ty1 ty2) e ]) b *)
      end
    end.

  Definition fun_env A := name -> A.
  Inductive fval : Type :=
  | fvConstr : inductive -> name -> list fval -> fval
  | fvClos   : fun_env fval -> name ->
              type (*types are used to convert closures back to lambdas *) ->
              expr -> fval.

  Definition ext_env (ρ : fun_env fval) (k : name) v := fun k' => if (string_dec k k') then v else ρ k'.
  Fixpoint ext_env_list (ρ : fun_env fval) (kvs : list (name * fval)) :=
    match kvs with
    | [] => ρ
    | (k,v) :: kvs' => ext_env (ext_env_list ρ kvs' ) k v
    end.


  Definition default_fun_env : fun_env fval := fun _ => fvConstr "Error" "Error" [].
  Definition pfun_env A := name -> res A.

  Definition penv_to_total ρ : fun_env fval :=
    fun k =>
    match ρ k with
    | Ok v => v
    | EvalError msg => fvConstr msg "Error" []
    | NotEnoughFuel => fvConstr "Not enough fuel" "Error" []
    end.

  Definition ext_env_rec (fixname : name) (var : name) (ty : type) (e : expr)
             (ρ : fun_env fval) :=
    fix rec_enc fuel : res (pfun_env fval) :=
        match fuel with
        | O => NotEnoughFuel
        | S n => Ok (fun k =>
                      if (eqb fixname k) then
                        match rec_enc n with
                          (* FIXME: [penv_to_total] is a hack*)
                        | Ok ρ' => Ok (fvClos (penv_to_total ρ') var ty e)
                        | EvalError msg => EvalError msg
                        | NotEnoughFuel => NotEnoughFuel
                        end
                      else Ok (ρ k))
        end.

  (* This is a simple fact, but it shows that we have two sources of partiality:
     possible non-termination of the recursive xontext extension and a corresoinding
     lookup operation (here it is just a function application, but it retirnes a
     value of type [res fvar] instead of plain [fvar] ) *)
  Lemma ext_env_rec_extend_lookup : forall n nm vn ty e ρ ρ',
      ext_env_rec nm vn ty e (penv_to_total ρ) n = Ok ρ ->
      ρ nm = Ok ρ' ->
    exists ρ'', ρ' = fvClos ρ'' vn ty e.
  Proof.
    intros n nm nv ty e ρ ρ' H1 H2. destruct n.
    + inversion H1.
    + destruct n.
      * inversion H1 as [H3]. rewrite <- H3 in H2. rewrite eqb_refl in H2.
        inversion H2.
      * inversion H1 as [H3]. simpl in *.
        rewrite <- H3 in H2.
        rewrite eqb_refl in H2.
        eexists.
        inversion_clear H2. f_equal.
  Qed.

  Import Basics.

  Open Scope program_scope.

  Fixpoint expr_eval_fun (fuel : nat) (Σ : global_env) (ρ : fun_env fval) (e : expr) : res fval :=
    match fuel with
    | O => NotEnoughFuel
    | S n =>
      match e with
      | eRel i => EvalError "Indices as variables are not supported"
      | eVar nm => Ok (ρ nm)
      | eLambda nm ty b =>
        Ok (fvClos ρ nm ty b)
      | eLetIn nm e1 ty e2 => todo
      | eApp e1 e2 =>
        match (expr_eval_fun n Σ ρ e1), (expr_eval_fun n Σ ρ e2) with
        | Ok (fvClos ρ' nm _ b), Ok v =>
          match (expr_eval_fun n Σ (ext_env ρ' nm v) b) with
          | Ok v' => Ok v'
          | err => err
          end
        | Ok (fvConstr ind n vs), Ok v => Ok (fvConstr ind n (List.app vs [v]))
        | EvalError msg, _ => EvalError msg
        | _, EvalError msg => EvalError msg
        | NotEnoughFuel,_ | _, NotEnoughFuel => NotEnoughFuel
        end
      | eConstr t i =>
        Ok (fvConstr t i [])
      | eConst nm => todo
      | eCase (ind,i) ty e bs =>
        match (expr_eval_fun n Σ ρ e) with
        | Ok (fvConstr ind' c vs) => if (string_dec ind ind') then
                                      match (match_pat c vs bs) with
                                      | Some (var_assign, v) =>
                                        expr_eval_fun n Σ (ext_env_list ρ var_assign) v
                                      | None => EvalError "No such constructor"
                                      end
                                    else EvalError ("Expecting inductive " ++ ind ++
                                                     " but found " ++ ind')
        | v => v
        end
      | eFix fixname vn ty1 ty2 e =>
        match (ext_env_rec fixname vn ty1 e ρ n) with
        | Ok ρ' => expr_eval_fun n Σ (penv_to_total ρ') (eLambda vn ty1 e)
        | EvalError msg => EvalError msg
        | NotEnoughFuel => NotEnoughFuel
        end
      end
    end.


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
    expr_eval 3 Σ [] prog1 = Ok (vConstr "Coq.Init.Datatypes.bool" "false" []).
  Proof. simpl. reflexivity. Qed.

End Interpreter.
