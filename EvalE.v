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
  | vConstruct : inductive -> nat -> val
  | vClos : env val -> name -> type -> expr -> val.

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
        | _, _ => None
        end
      | eConstruct t i =>
        (* only nullary constructors *)
        Some (vConstruct t i)
      | eConst nm => None
      | eCase (ind,i) ty e bs =>
        match (expr_eval ρ e) with
        | Some (vConstruct ind' i) => if (string_dec ind ind') then
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

  Fixpoint expr_eval (fuel : nat) (ρ : env val) (e : expr) : res val :=
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
        match (expr_eval n ρ e1), (expr_eval n ρ e2) with
        | Ok (vClos ρ' nm _ b), Ok v =>
          match (expr_eval n (ρ' # [nm ~> v]) b) with
          | Ok v' => Ok v'
          | err => err
          end
        | _, _ => EvalError "Error in App"
        end
      | eConstruct t i =>
        (* only nullary constructors *)
        Ok (vConstruct t i)
      | eConst nm => todo
      | eCase (ind,i) ty e bs =>
        match (expr_eval n ρ e) with
        | Ok (vConstruct ind' i) => if (string_dec ind ind') then
                                        match (List.nth_error bs i) with
                                        | Some v => expr_eval n ρ (snd v)
                                        | _ => EvalError "No such constructor"
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
    expr_eval 3 [] prog1 = Ok (vConstruct "Coq.Init.Datatypes.bool" 1).
  Proof. simpl. reflexivity. Qed.

End Interpreter.