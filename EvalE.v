Require Import String.
Require Import List.
Require Import Ast.

Import ListNotations.

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
  | vClos   : env val -> name -> type -> expr -> val.

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

  Definition option_to_res {A : Type} (o : option A) (msg : string) :=
    match o with
    | Some v => Ok v
    | None => EvalError msg
    end.

  Definition todo := EvalError (A:=val) "Not implemented".

  Definition ind_name (v : val) :=
    match v with
    | vConstr ind_name _ _ => Some ind_name
    | _ => None
    end.

  (* FIXME: should be extended to match the arguments of the constructor *)
  Fixpoint match_pat (constr_name : name) (constr_args : list val) (bs : list (pat * expr)) :=
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
        | EvalError msg, Ok _ => EvalError msg
        | Ok _, EvalError msg => EvalError msg
        | _,_ => EvalError "Error in App "
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
                                                     "but found " ++ ind')
        | _ => EvalError "Error in Case"
        end
      | eFix nm ty b => todo
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
