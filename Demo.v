Require Import String.
Require Import Ast.
Require Import EvalE.
Require Import List.
Import ListNotations.
From Template Require Ast.
From Template Require Import TemplateMonad.
From Template Require Import monad_utils.

Import BaseTypes.
Import StdLib.

Definition negb_app_true :=
    [|
     (\x : Bool ->
           case x : Bool_name return Bool of
           | true -> false
           | false -> true) true
     |].

Print negb_app_true.

Unset Printing Notations.
Print negb_app_true.

Set Printing Notations.

Import Interpreter.

(* Execute the program using interpreter *)
Compute (expr_eval 3 [] negb_app_true).


(* Make a Coq function from the AST of the program *)
Make Definition coq_negb_app_true := Eval compute in (expr_to_term (indexify nil negb_app_true)).

Print coq_negb_app_true.

(* Inductive equiv_val :  := *)
(* | *)

(* Lemma negb_app_true_sound : *)

Definition my_negb :=
    [| (\x : Bool -> \y : Bool ->
           case x : Bool_name return Bool of
           | true -> false
           | false -> true) true  |].

Compute (expr_eval 3 [] my_negb).

Make Definition coq_my_negb := Eval compute in (expr_to_term (indexify [] my_negb)).

Fixpoint remove_by_key {A : Set} (key : string) (ρ : env A) : env A :=
    match ρ with
      | [] => []
      | (key', y) :: ρ' => if (string_dec key key') then remove_by_key key ρ'
                else  (key',y) :: (remove_by_key key ρ')
    end.


(* NOTE: assumes, that [e] is a closed expression! *)
Fixpoint subst_env (ρ : env expr) (e : expr) : expr :=
  match e with
  | eRel i as e' => e'
  | eVar nm  => match ρ#(nm) with
                    | Some v => v
                    | None => e
                    end
  | eLambda nm ty b => eLambda nm ty (subst_env (remove_by_key nm ρ) b)
  | eLetIn nm e1 ty e2 => eLetIn nm (subst_env ρ e1) ty (subst_env (remove_by_key nm ρ) e2)
  | eApp e1 e2 => eApp (subst_env ρ e1) (subst_env ρ e2)
  | eConstruct t i as e' => e'
  | eConst nm => eConst nm
  | eCase nm_i ty e bs =>
    (* TODO: this case is not complete! We ignore variables bound by patterns *)
    eCase nm_i ty (subst_env ρ e) (map (fun x => (fst x, subst_env ρ (snd x))) bs)
  | eFix nm ty b => eFix nm ty (subst_env (remove_by_key nm ρ) b)
  end.


Fixpoint from_val (v : val) : expr :=
  match v with
  | vConstruct x i => eConstruct x i
  | vClos ρ nm ty e => subst_env (map (fun x => (fst x, from_val (snd x))) ρ) (eLambda nm ty e)
  end.

Import MonadNotation.

Run TemplateProgram
    (
      t <- tmEval lazy (expr_eval 3 [] my_negb);;
        match t with
          Ok v =>
          t' <- tmEval lazy (expr_to_term (indexify [] (from_val v))) ;;
          def <- tmUnquoteTyped (bool -> bool) t' ;;
          tmDefinition "eval_my_negb" def ;;
             print_nf "Done."
        | EvalError msg => print_nf msg
        | NotEnoughFuel => print_nf "Not enough fuel"
        end
    ).


Lemma my_negb_adequate : forall b, coq_my_negb b = eval_my_negb b.
Proof.
  intros b; destruct b;auto.
Qed.