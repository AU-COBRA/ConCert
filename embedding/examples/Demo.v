(** * Simple examples on how to use our framework  **)
Require Import String Basics.
Require Import List.
From ConCert.Embedding Require Import Ast Notations EvalE PCUICtoTemplate PCUICTranslate.

From MetaCoq.Template Require Ast.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq.Template Require Import monad_utils.

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Module TC := Template.BasicAst.

Import ListNotations.
Import MonadNotation.
Import BaseTypes.
Import StdLib.

Module MC:=MetaCoq.Template.Ast.
Import BasicAst.


(** MetaCoq demo *)

(* Quote *)
MetaCoq Quote Definition id_nat_syn := (fun x : nat => x).
Print id_nat_syn.
(* Ast.tLambda (nNamed "x")
   (Ast.tInd {| TC.inductive_mind := "nat"; TC.inductive_ind := 0 |}
      []) (Ast.tRel 0) : Ast.term *)

(* Unquote *)
MetaCoq Unquote Definition plus_one :=
  (MC.tLambda (nNamed "x")
              (MC.tInd (mkInd (MPfile ["Datatypes"; "Init"; "Coq"], "nat") 0) nil)
              (MC.tApp (MC.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Coq"], "nat") 0) 1 nil)
                       (MC.tRel 0 :: nil))).

(* fun x : nat => S x : nat -> nat *)


Definition x := "x".
Definition y := "y".
Definition z := "z".


Definition negb_app_true :=
    [|
     (\x : Bool =>
           case x : Bool return Bool of
           | True -> False
           | False -> True) True
     |].


Unset Printing Notations.

Set Printing Notations.

(* Execute the program using the interpreter *)
Compute (expr_eval_n Σ 3 nil negb_app_true).

Compute (expr_eval_i Σ 3 nil (indexify nil negb_app_true)).

(* Make a Coq function from the AST of the program *)
MetaCoq Unquote Definition coq_negb_app_true :=
  (expr_to_tc Σ (indexify nil negb_app_true)).


Definition my_negb_syn :=
  [| \x : Bool => case x : Bool return Bool of
                   | True -> False
                   | False -> True  |].

MetaCoq Unquote Definition my_negb :=
  (expr_to_tc Σ (indexify nil my_negb_syn)).

Lemma my_negb_coq_negb b :
  my_negb b = negb b.
Proof. reflexivity. Qed.

Compute (expr_eval_n Σ 3 nil my_negb_syn).

Example eval_my_negb_true :
  expr_eval_i Σ 4 nil (indexify nil [| {my_negb_syn} True |]) = Ok (vConstr Bool "false" nil).
Proof. reflexivity. Qed.

MetaCoq Unquote Definition coq_my_negb := (expr_to_tc Σ (indexify nil my_negb_syn)).

Import MonadNotation.

Definition is_zero_syn :=
  [|

      \x : Nat =>
           case x : Nat return Bool of
           | Zero -> True
           | Suc y -> False

  |].

MetaCoq Unquote Definition is_zero' := (expr_to_tc Σ (indexify nil is_zero_syn)).

Definition pred_syn :=
  [|

      \x : Nat =>
           case x : Nat return Nat of
           | Zero -> x
           | Suc y -> y

  |].

MetaCoq Unquote Definition pred' := (expr_to_tc Σ (indexify nil pred_syn)).

Definition prog2 := [| Suc (Suc Zero) |].

Example value_eval : expr_eval_n Σ 3 nil prog2 = Ok (vConstr Nat "Suc"
                                                             [vConstr Nat "Suc"
                                                                      [vConstr Nat "Z" []]]).
Proof. reflexivity. Qed.

Example eval_is_zero_true :
  expr_eval_i Σ 4 nil (indexify nil [|{is_zero_syn} Zero |]) = Ok (vConstr Bool "true" []).
Proof. reflexivity. Qed.

Example eval_is_zero_false :
  expr_eval_i Σ 4 nil (indexify nil [|{is_zero_syn} {prog2} |]) = Ok (vConstr Bool "false" []).
Proof. reflexivity. Qed.

Inductive blah :=
  Bar : blah -> blah -> blah
| Baz : blah.


Definition Σ' : global_env :=
  [gdInd "blah" 0 [("Bar", [(None,tyInd "blah"); (None,tyInd "blah")]); ("Baz", [])] false;
     gdInd Nat  0 [("Z", []); ("Suc", [(None,tyInd Nat)])] false].

Notation "'Bar'" := (eConstr "blah" "Bar") (in custom expr).
Notation "'Baz'" := (eConstr "blah" "Baz") (in custom expr).

Definition prog3 := [| Bar (Bar Baz Baz) Baz |].

Compute (expr_eval_n Σ' 5 [] prog3).

(* Examples of a fixpoint *)

Definition fact := "fact".

Definition factorial_syn :=
  [|
   fix fact (x : Nat) : Nat :=
       case x : Nat return Nat of
       | Zero -> 1
       | Suc y -> x * (fact y)
  |].

MetaCoq Unquote Definition factorial :=
  (expr_to_tc Σ (indexify [] factorial_syn)).

Definition plus_syn : expr :=
  [| fix "plus" (x : Nat) : Nat -> Nat :=
       \y : Nat =>
           case x : Nat return Nat of
           | Zero -> y
           | Suc z -> Suc ("plus" z y) |].

MetaCoq Unquote Definition my_plus := (expr_to_tc Σ (indexify [] plus_syn)).

Lemma my_plus_correct n m :
  my_plus n m = n + m.
Proof. induction n;simpl;auto. Qed.


Definition two :=
  (vConstr Nat "Suc"
           [vConstr Nat "Suc" [vConstr Nat "Z" []]]).

Definition one_plus_one :=
  [| {plus_syn} 1 1 |].

Compute (expr_eval_n Σ 10 [] [| {plus_syn} 1 1 |]).
(* = Ok (vConstr "nat" "Suc" [vConstr "nat" "Suc" [vConstr "nat" "Z" []]])*)

Definition two_arg_fun_syn := [| \x : Nat => \y : Bool => x |].

MetaCoq Unquote Definition two_arg_fun_app :=
  (expr_to_tc Σ (indexify [] [| {two_arg_fun_syn} 1 True |])).

Parameter bbb: bool.

MetaCoq Quote Definition two_arg_fun_app_syn' := ((fun (x : nat) (_ : bool) => x) 1 bbb).

Example one_plus_one_two : expr_eval_n Σ 10 [] one_plus_one = Ok two.
Proof.  reflexivity. Qed.

Example one_plus_one_two_i : expr_eval_i Σ 10 [] (indexify [] one_plus_one) = Ok two.
Proof.  reflexivity. Qed.


Definition plus_syn' :=
  [| \x : Nat =>
          (fix "plus" (y : Nat) : Nat :=
           case y : Nat return Nat of
           | Zero -> x
           | Suc z -> Suc ("plus" z))
  |].

MetaCoq Unquote Definition my_plus' :=
  (expr_to_tc Σ (indexify [] plus_syn')).

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
           | Zero -> 0
           | Suc z -> Suc ("plus" z))
   |].

Compute (expr_eval_n Σ 20 [] [| {id_rec} (Suc (Suc (Suc 1))) |]).
Compute (expr_eval_i Σ 20 [] (indexify [] [| {id_rec} (Suc (Suc (Suc 1))) |])).

Example id_rec_named_and_indexed :
  let arg := [| Suc (Suc (Suc 1)) |] in
  expr_eval_n Σ 20 [] [| {id_rec} {arg} |] =
  expr_eval_i Σ 20 [] (indexify [] [| {id_rec} {arg} |]).
Proof. reflexivity. Qed.

Example plus_named_and_indexed :
  let two := [| (Suc 1)|] in
  let three := [| Suc {two} |] in
  expr_eval_n Σ 20 [] [| ({plus_syn} {two}) {three} |] =
  expr_eval_i Σ 20 [] (indexify [] [| ({plus_syn} {two}) {three} |]).
Proof. reflexivity. Qed.

Compute (expr_eval_i Σ 10 [] (indexify [] [| {plus_syn} 1 |])).

Compute (indexify [] [| {plus_syn}|]).
Compute (expr_eval_n Σ 10 [] [| {plus_syn} 0 |]).

Definition fun_app := [| (\x : Nat => \y : Nat => y + x) Zero |].

Compute (expr_eval_n Σ' 10 [] fun_app).


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

MetaCoq Quote Definition q_stupid_case := Eval compute in stupid_case.
(* Nested patters are transformed into the nested "case" expressions *)
MetaCoq Quote Definition q_stupid_case' := Eval compute in stupid_case'.

Inductive Bazz :=
  cBazz : nat -> nat -> nat -> Bazz.

Definition Bazz_match b :=
  match b with
    cBazz n m k => n
  end.

MetaCoq Quote Definition q_Bazz_match := Eval compute in Bazz_match.

(** Inductives *)
Definition Nat_syn :=
  [\ data "MyNat" =
       "Z" [_]
     | "Suc" ["MyNat", _] \].

MetaCoq Unquote Inductive (global_to_tc Nat_syn).


(** Records *)

Import Template.Ast.

Definition State_syn :=
  [\ record "State" := "mkState" { "balance" : Nat ; "day" : Nat }  \].

MetaCoq Unquote Inductive (global_to_tc State_syn).

Check balance.
Check day.
