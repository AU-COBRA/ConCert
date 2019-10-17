From ConCert Require Import Ast Notations PCUICTranslate PCUICtoTemplate.
From Coq Require Import Basics String List.

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Import ListNotations.
Import BaseTypes.
Import StdLib.


Definition x := "x".
Definition y := "y".
Definition z := "z".

Check [| ^0 |].

Check [| \x : Nat => y |].

Definition id_f_syn :=  [| (\x : Nat => ^0) 1 |].

Make Definition id_f_one := (expr_to_tc Σ id_f_syn).
Example id_f_eq : id_f_one = 1. Proof. reflexivity. Qed.

(* The same as [id_f_syn], but with named vars *)
Definition id_f_with_vars := [| (\x : Nat => x) 1 |].

Make Definition id_f_one' := (expr_to_tc Σ (indexify [] id_f_with_vars)).
Example id_f_eq' : id_f_one' = 1. Proof. reflexivity. Qed.

Definition simple_let_syn :=
  [|
   \x : Nat =>
     let y : Nat := 1 in ^0
   |].

Make Definition simple_let := (expr_to_tc Σ simple_let_syn).
Example simple_let_eq : simple_let 1 = 1. Proof. reflexivity. Qed.

Definition simple_let_with_vars_syn :=
  [|
   \x : Nat =>
     let y : Nat := 1 in y
   |].

Make Definition simple_let' := (expr_to_tc Σ (indexify [] simple_let_with_vars_syn)).
Example simple_let_eq' : simple_let' 0 = 1. Proof. reflexivity. Qed.


Definition negb_syn :=
  [|
   \x : Bool =>
          case x : Bool return Bool of
          | True -> False
          | False -> True
  |].

Make Definition negb' := (expr_to_tc Σ (indexify [] negb_syn)).

Example negb'_correct : forall b, negb' b = negb b.
Proof.
  destruct b;easy.
Qed.

Definition myplus_syn :=
  [| \x : Nat => \y : Nat => x + y |].

Make Definition myplus := (expr_to_tc Σ (indexify [] myplus_syn)).

Definition stupid_case :=
  fun y : Set => fun x : y => fun z : list y =>
                match z with
                | [] => x
                | _ => x
                end.

Quote Definition q_stupid_case := Eval compute in stupid_case.
Quote Recursively Definition q_stupid_case_rec := stupid_case.
Quote Definition cons_syn := (fun A : Set => cons A).

Definition case_ex :=
  [| \\y  => \x : 'y =>  \z : "list" 'y =>
         case z : "list" 'y return 'y of
         | Nil -> x
         | Cons "hd" "tl" -> x |].

Compute (expr_to_tc Σ (indexify [] case_ex)).

Make Definition case_ex_def :=  (expr_to_tc Σ (indexify [] case_ex)).

Definition case_ex1 :=
  [| \\y  => \"w" : 'y => \x : 'y =>  \z : "list" 'y =>
         case z : "list" 'y return "prod" 'y 'y of
         | Nil -> {eConstr "prod" "pair"} {eTy (tyVar y)} {eTy (tyVar y)} x x
         | Cons "hd" "tl" -> {eConstr "prod" "pair"} {eTy (tyVar y)} {eTy (tyVar y)} "hd" x |].

Compute (expr_to_tc Σ (indexify [] case_ex1)).

Make Definition case_ex_def1 :=  (expr_to_tc Σ (indexify [] case_ex1)).

Definition case_ex2 :=
  [| \\y => case ({eConstr "list" "nil"} "y") : "list" 'y return "list" 'y of
            | Nil -> {eConstr "list" "nil"} "y"
            | Cons "hd" "tl" -> {eConstr "list" "nil"} "y" |].

Compute indexify [] case_ex2.
Compute (expr_to_tc Σ (indexify [] case_ex2)).

Make Definition case_ex_def2 :=  (expr_to_tc Σ (indexify [] case_ex2)).

Make Definition ex_type_def := (type_to_tc (indexify_type [] example_type)).

Definition map_syn :=
gdInd "AMap" 2 [("ANil", []);
                  ("ACons", [(None,tyRel 1);(None,tyRel 0);
                               (None,(tyApp (tyApp (tyInd "AMap") (tyRel 1)) (tyRel 0)))])] false.

Make Inductive (global_to_tc map_syn).