Require Import String.
Require Import Ast.
Require Import EvalE.
Require Import List.
Import ListNotations.
From Template Require Ast.
From Template Require Import TemplateMonad.
From Template Require Import monad_utils.


Import MonadNotation.
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

Import InterpreterEnvList.

(* Execute the program using the interpreter *)
Compute (expr_eval_n 3 Σ enEmpty negb_app_true).

Compute (expr_eval_i 3 Σ enEmpty (indexify [] negb_app_true)).


(* Make a Coq function from the AST of the program *)
Make Definition coq_negb_app_true :=
  Eval compute in (expr_to_term Σ (indexify nil negb_app_true)).

Print coq_negb_app_true.

Definition my_negb :=
    [| (\x : Bool -> \y : Bool ->
           case x : Bool_name return Bool of
           | true -> false
           | false -> true) true  |].

Compute (expr_eval_n 3 Σ enEmpty my_negb).

Make Definition coq_my_negb := Eval compute in (expr_to_term Σ (indexify [] my_negb)).

Import MonadNotation.

Run TemplateProgram
    (
      t <- tmEval lazy (expr_eval_n 3 Σ InterpreterEnvList.enEmpty my_negb);;
        match t with
          Ok v =>
          t' <- tmEval lazy (expr_to_term Σ (indexify [] (InterpreterEnvList.from_val v))) ;;
          def <- tmUnquoteTyped (bool -> bool) t' ;;
          tmDefinition "eval_my_negb" def ;;
             print_nf "Done."
        | EvalError msg => print_nf msg
        | NotEnoughFuel => print_nf "Not enough fuel"
        end
    ).


Lemma my_negb_adequate : forall b, coq_my_negb b = eval_my_negb b.
Proof.
  intros [];auto.
Qed.

Definition is_zero_syn :=
  [|

      \x : Nat ->
           case x : Nat_name return Bool of
           | Z -> true
           | Suc y -> false

  |].

Make Definition is_zero' := Eval compute in (expr_to_term Σ (indexify nil is_zero_syn)).


Definition pred_syn :=
  [|

      \x : Nat ->
           case x : Nat_name return Nat of
           | Z -> x
           | Suc y -> y

  |].

Make Definition pred' := Eval compute in (expr_to_term Σ (indexify nil pred_syn)).

Definition prog2 := [| Suc (Suc Z) |].

Compute (expr_eval_n 3 Σ enEmpty prog2).

Inductive blah :=
  Bar : blah -> blah -> blah
| Baz : blah.

Definition Σ' : global_env :=
  [gdInd "blah" [("Bar", [tyInd "blah"; tyInd "blah"]); ("Baz", [])];
     gdInd Nat_name  [("Z", []); ("Suc", [tyInd Nat_name])]].

Notation "'Bar'" := (eConstr "blah" "Bar") (in custom expr).
Notation "'Baz'" := (eConstr "blah" "Baz") (in custom expr).

Definition prog3 := [| Bar (Bar Baz Baz) Baz |].

Compute (expr_eval_n 5 Σ enEmpty prog3).

(* Examples of a fixpoint *)

Definition factorial_syn :=
  [|
   fix "factorial" (x : Nat) : Nat :=
       case x : Nat_name return Nat of
       | Z -> 1
       | Suc y -> x * ("factorial" y)
  |].

Make Definition factorial :=
  Eval compute in ((expr_to_term Σ (indexify [] factorial_syn))).

Definition plus_syn :=
  [| \x : Nat ->
          (fix "plus" (y : Nat) : Nat :=
           case y : Nat_name return Nat of
           | Z -> x
           | Suc z -> Suc ("plus" z))
  |].

Make Definition my_plus :=
  Eval compute in ((expr_to_term Σ (indexify [] plus_syn))).

Lemma my_plus_0 : forall n, my_plus 0 n = n.
Proof.
  induction n;simpl;easy.
Qed.

Lemma my_plus_Sn : forall n m, my_plus (S n) m = S (my_plus n m).
Proof.
  induction m;simpl;easy.
Qed.

Lemma my_plus_comm : forall n m, my_plus n m = my_plus m n.
Proof.
  induction n; intros m;simpl.
  + rewrite my_plus_0. reflexivity.
  + rewrite my_plus_Sn. easy.
Qed.

(* my_plus corresponds to addition of natural numbers defined in the standard library *)
Lemma my_plus_correct : forall n m, my_plus n m = n + m.
Proof.
  intros n m.
  induction m;simpl;easy.
Qed.

Definition two :=
  (vConstr "Coq.Init.Datatypes.nat" "Suc"
           [vConstr "Coq.Init.Datatypes.nat" "Suc" [vConstr "Coq.Init.Datatypes.nat" "Z" []]]).

Definition one_plus_one :=
  [| {plus_syn} 1 1 |].

Compute (expr_eval_n 10 Σ enEmpty one_plus_one).

Example one_plus_one_two : expr_eval_n 10 Σ enEmpty one_plus_one = Ok two.
Proof. reflexivity. Qed.

Definition id_rec :=
  [| (fix "plus" (y : Nat) : Nat :=
           case y : Nat_name return Nat of
           | Z -> 0
           | Suc z -> Suc ("plus" z))
   |].

Compute (expr_eval_n 20 Σ enEmpty [| {id_rec} (Suc (Suc (Suc 1))) |]).
Compute (expr_eval_i 20 Σ enEmpty (indexify [] [| {id_rec} (Suc (Suc (Suc 1))) |])).

Example id_rec_named_and_indexed :
  let arg := [| Suc (Suc (Suc 1)) |] in
  expr_eval_n 20 Σ enEmpty [| {id_rec} {arg} |] =
  expr_eval_i 20 Σ enEmpty (indexify [] [| {id_rec} {arg} |]).
Proof. reflexivity. Qed.

Example plus_named_and_indexed :
  let two := [| (Suc 1)|] in
  let three := [| Suc {two} |] in
  expr_eval_n 20 Σ enEmpty [| ({plus_syn} {two}) {three} |] =
  expr_eval_i 20 Σ enEmpty (indexify [] [| ({plus_syn} {two}) {three} |]).
Proof. reflexivity. Qed.

Compute ( v <- (expr_eval_i 10 Σ enEmpty (indexify [] [| {one_plus_one} |]));;
          ret (from_val v)).

Compute (expr_eval_i 10 Σ enEmpty (indexify [] [| {plus_syn} 1 |])).

Compute ( v <- (expr_eval_n 10 Σ enEmpty [| {plus_syn} 1 |]);;
          ret (from_val v)).

Compute (indexify [] [| {plus_syn}|]).

Compute ( v <- (expr_eval_i 10 Σ enEmpty (indexify [] [| {plus_syn} |]));;
          ret (from_val v)).

Compute (expr_eval_n 10 Σ enEmpty [| {plus_syn} 0 |]).

Example plus_syn_partial_app :
  exists v, (expr_eval_i 10 Σ enEmpty (indexify [] [| {plus_syn} 0 |])) = Ok v /\
       from_val_i v = indexify [] id_rec.
Proof.
  eexists. split. compute. reflexivity.
  compute. reflexivity.
Qed.
