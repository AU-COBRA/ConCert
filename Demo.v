Require Import String.
Require Import Ast.
Require Import EvalE.
Require Import List.
Import ListNotations.
From Template Require Ast AstUtils.
Require Import Template.Typing.
From Template Require Import TemplateMonad.
From Template Require Import monad_utils.

Module TC := Template.Ast.

Import MonadNotation.
Import BaseTypes.
Import StdLib.

Definition negb_app_true :=
    [|
     (\x : Bool ->
           case x : Bool return Bool of
           | True -> False
           | False -> True) True
     |].

Print negb_app_true.

Unset Printing Notations.
Print negb_app_true.

Set Printing Notations.

Import InterpreterEnvList.

(* Execute the program using the interpreter *)
Compute (expr_eval_n 3 Σ [] negb_app_true).

Compute (expr_eval_i 3 Σ [] (indexify [] negb_app_true)).


(* Make a Coq function from the AST of the program *)
Make Definition coq_negb_app_true :=
  Eval compute in (expr_to_term Σ (indexify nil negb_app_true)).

Print coq_negb_app_true.

Definition my_negb_syn :=
  [| \x : Bool -> case x : Bool return Bool of
                   | True -> False
                   | False -> True  |].

Make Definition my_negb :=
  Eval compute in (expr_to_term Σ (indexify [] my_negb_syn)).

Lemma my_negb_coq_negb b :
  my_negb b = negb b.
Proof. reflexivity. Qed.

Compute (expr_eval_n 3 Σ [] my_negb_syn).

Make Definition coq_my_negb := Eval compute in (expr_to_term Σ (indexify [] my_negb_syn)).

Import MonadNotation.

Run TemplateProgram
    (
      t <- tmEval lazy (expr_eval_n 3 Σ [] my_negb_syn);;
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
           case x : Nat return Bool of
           | Z -> True
           | Suc y -> False

  |].

Make Definition is_zero' := Eval compute in (expr_to_term Σ (indexify nil is_zero_syn)).


Definition pred_syn :=
  [|

      \x : Nat ->
           case x : Nat return Nat of
           | Z -> x
           | Suc y -> y

  |].

Make Definition pred' := Eval compute in (expr_to_term Σ (indexify nil pred_syn)).

Definition prog2 := [| Suc (Suc Z) |].

Compute (expr_eval_n 3 Σ [] prog2).

Inductive blah :=
  Bar : blah -> blah -> blah
| Baz : blah.

Definition Σ' : global_env :=
  [gdInd "blah" [("Bar", [(TC.nAnon,tyInd "blah"); (TC.nAnon,tyInd "blah")]); ("Baz", [])] false;
     gdInd Nat  [("Z", []); ("Suc", [(TC.nAnon,tyInd Nat)])] false].

Notation "'Bar'" := (eConstr "blah" "Bar") (in custom expr).
Notation "'Baz'" := (eConstr "blah" "Baz") (in custom expr).

Definition prog3 := [| Bar (Bar Baz Baz) Baz |].

Compute (expr_eval_n 5 Σ' [] prog3).

(* Examples of a fixpoint *)

Definition factorial_syn :=
  [|
   fix "factorial" (x : Nat) : Nat :=
       case x : Nat return Nat of
       | Z -> 1
       | Suc y -> x * ("factorial" y)
  |].

Make Definition factorial :=
  Eval compute in ((expr_to_term Σ (indexify [] factorial_syn))).

Definition plus_syn : expr :=
  [| fix "plus" (x : Nat) : Nat -> Nat :=
           case x : Nat return Nat -> Nat of
           | Z -> \y : Nat -> y
           | Suc y -> \z : Nat -> Suc ("plus" y z) |].

Make Definition my_plus := Eval compute in (expr_to_term Σ (indexify [] plus_syn)).

Lemma my_plus_correct n m :
  my_plus n m = n + m.
Proof. induction n;simpl;auto. Qed.


Definition two :=
  (vConstr Nat "Suc"
           [vConstr Nat "Suc" [vConstr Nat "Z" []]]).

Definition one_plus_one :=
  [| {plus_syn} 1 1 |].

Compute (expr_eval_n 10 Σ [] [| {plus_syn} 1 1 |]).
(* = Ok (vConstr "nat" "Suc" [vConstr "nat" "Suc" [vConstr "nat" "Z" []]])*)

Definition two_arg_fun_syn := [| \x : Nat -> \y : Bool -> x |].

Make Definition two_arg_fun_app :=
  Eval compute in (expr_to_term Σ (indexify [] [| {two_arg_fun_syn} 1 True |])).

Parameter bbb: bool.

Quote Definition two_arg_fun_app_syn' := ((fun (x : nat) (_ : bool) => x) 1 bbb).

Example one_plus_one_two : expr_eval_n 10 Σ [] one_plus_one = Ok two.
Proof. reflexivity. Qed.

Definition plus_syn' :=
  [| \x : Nat ->
          (fix "plus" (y : Nat) : Nat :=
           case y : Nat return Nat of
           | Z -> x
           | Suc z -> Suc ("plus" z))
  |].

Make Definition my_plus' :=
  Eval compute in ((expr_to_term Σ (indexify [] plus_syn'))).

Lemma my_plus'_0 : forall n, my_plus' 0 n = n.
Proof.
  induction n;simpl;easy.
Qed.

Lemma my_plus'_Sn : forall n m, my_plus' (S n) m = S (my_plus' n m).
Proof.
  induction m;simpl;easy.
Qed.

Lemma my_plus'_comm : forall n m, my_plus' n m = my_plus' m n.
Proof.
  induction n; intros m;simpl.
  + rewrite my_plus'_0. reflexivity.
  + rewrite my_plus'_Sn. easy.
Qed.

(* my_plus corresponds to addition of natural numbers defined in the standard library *)
Lemma my_plus'_correct : forall n m, my_plus' n m = n + m.
Proof.
  intros n m.
  induction m;simpl;easy.
Qed.


Definition id_rec :=
  [| (fix "plus" (y : Nat) : Nat :=
           case y : Nat return Nat of
           | Z -> 0
           | Suc z -> Suc ("plus" z))
   |].

Compute (expr_eval_n 20 Σ [] [| {id_rec} (Suc (Suc (Suc 1))) |]).
Compute (expr_eval_i 20 Σ [] (indexify [] [| {id_rec} (Suc (Suc (Suc 1))) |])).

Example id_rec_named_and_indexed :
  let arg := [| Suc (Suc (Suc 1)) |] in
  expr_eval_n 20 Σ [] [| {id_rec} {arg} |] =
  expr_eval_i 20 Σ [] (indexify [] [| {id_rec} {arg} |]).
Proof. reflexivity. Qed.

Example plus_named_and_indexed :
  let two := [| (Suc 1)|] in
  let three := [| Suc {two} |] in
  expr_eval_n 20 Σ [] [| ({plus_syn} {two}) {three} |] =
  expr_eval_i 20 Σ [] (indexify [] [| ({plus_syn} {two}) {three} |]).
Proof. reflexivity. Qed.

Compute ( v <- (expr_eval_i 10 Σ [] (indexify [] [| {one_plus_one} |]));;
          ret (from_val v)).

Compute (expr_eval_i 10 Σ [] (indexify [] [| {plus_syn} 1 |])).

Compute ( v <- (expr_eval_n 10 Σ [] [| {plus_syn} 1 |]);;
          ret (from_val v)).

Compute (indexify [] [| {plus_syn}|]).

Compute ( v <- (expr_eval_i 10 Σ [] (indexify [] [| {plus_syn} |]));;
          ret (from_val v)).

Compute (expr_eval_n 10 Σ [] [| {plus_syn} 0 |]).

Definition fun_app := [| (\x : Nat -> \y : Nat -> y + x) Z |].

Compute (expr_eval_n 10 [] [] fun_app).

Example fun_app_from_val :
  exists v, (expr_eval_n 10 Σ' [] (indexify [] fun_app)) = Ok v /\
       from_val_i v = (indexify [] [|\y : Nat -> y + Z |]).
Proof.
  eexists. split. compute. reflexivity.
  simpl. compute. reflexivity.
Qed.


Example plus_syn_partial_app :
  exists v, (expr_eval_i 10 Σ [] (indexify [] [| {plus_syn'} 0 |])) = Ok v /\
       from_val_i v = indexify [] id_rec.
Proof.
  eexists. split. compute. reflexivity.
  compute. reflexivity.
Qed.

Inductive mybool :=
| mfalse
| mtrue.

Definition stupid_case (b : mybool) : nat :=
  match b with
  | mtrue => 1
  | mfalse => 0
  end.

Definition stupid_case' (b : mybool * mybool) : nat :=
  match b with
  | (mtrue, _) => 1
  | (mfalse, _) => 0
  end.


Definition is_zero (n : nat) :=
  match n with
  | S n => mfalse
  | O => mtrue
  end.

Quote Definition q_stupid_case := Eval compute in stupid_case.
(* Nested patters are transformed into the nested "case" expressions *)
Quote Definition q_stupid_case' := Eval compute in stupid_case'.

Inductive Bazz :=
  cBazz : nat -> nat -> nat -> Bazz.

Definition Bazz_match b :=
  match b with
    cBazz n m k => n
  end.

Quote Definition q_Bazz_match := Eval compute in Bazz_match.


(** Translation inductives *)

Definition Nat_syn :=
  [\ data "Nat" := "Z" : "Nat" | "Suc" : "Nat" -> "Nat" ; \].

Make Inductive (trans_global_dec Nat_syn).


(** Records *)

Import Template.Ast.

Definition State_syn :=
  [\ record "State" := { "balance" : "Nat" ; "day" : "Nat" }  \].

Make Inductive (trans_global_dec State_syn).

Check balance.
Check day.
