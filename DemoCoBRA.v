Require Import String List.
Require Import Ast EvalE.

Import ListNotations.

Import BaseTypes.
Import StdLib.

Definition negb_app_true :=
    [| (\x : Bool ->
           case x : Bool return Bool of
           | true -> false
           | false -> true) true
     |].

Print negb_app_true.

Unset Printing Notations.
Print negb_app_true.

Set Printing Notations.

Import InterpreterEnvList.

(* Execute the program using the interpreter *)
Compute (expr_eval_n 3 Σ [] negb_app_true).

(* Execute the "indexified", i.e. nameless, program *)
Compute (expr_eval_i 3 Σ [] (indexify [] negb_app_true)).

Notation plus := "plus".

Definition plus_syn : expr :=
  [| fix plus (x : Nat) : Nat -> Nat :=
           case x : Nat return Nat -> Nat of
           | Z -> \y : Nat -> y
           | Suc y -> \z : Nat -> Suc (plus y z) |].

Definition two :=
  (vConstr Nat "Suc"
           [vConstr Nat "Suc" [vConstr Nat "Z" []]]).

Definition one_plus_one :=
  [| {plus_syn} 1 1 |].

Compute (expr_eval_n 10 Σ [] [| {plus_syn} 1 1 |]).

Example one_plus_one_two : expr_eval_n 10 Σ [] one_plus_one = Ok two.
Proof. reflexivity. Qed.

(* Unquote the translated expression *)
Make Definition my_plus :=
  Eval compute in (expr_to_term Σ (indexify [] plus_syn)).

Print my_plus.

(* our plus program corresponds to the addition of natural numbers *)
Lemma my_plus_correct n m :
  my_plus n m = n + m.
Proof. induction n;simpl;auto. Qed.
