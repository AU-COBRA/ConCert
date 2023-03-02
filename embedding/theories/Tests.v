(** * Various examples of using notations and conversion to the shallow embedding *)
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import PCUICtoTemplate.
From Coq Require Import Basics.
From Coq Require Import String.
From Coq Require Import List.

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Import ListNotations.
Import BaseTypes.
Import StdLib.

Definition x := "x".
Definition y := "y".
Definition z := "z".

Example ex1 :
  [| ^0 |] = eRel 0.
Proof. reflexivity. Qed.

Definition id_f_syn := [| (\x : Nat => ^0) 1 |].

MetaCoq Unquote Definition id_f_one := (expr_to_tc Σ id_f_syn).
Example id_f_eq :
  id_f_one = 1.
Proof. reflexivity. Qed.

(* The same as [id_f_syn], but with named vars *)
Definition id_f_with_vars := [| (\x : Nat => x) 1 |].

MetaCoq Unquote Definition id_f_one' := (expr_to_tc Σ (indexify [] id_f_with_vars)).
Example id_f_eq' :
  id_f_one' = 1.
Proof. reflexivity. Qed.

Definition simple_let_syn :=
  [|
   \x : Nat =>
     let y : Nat := 1 in ^0
   |].

MetaCoq Unquote Definition simple_let := (expr_to_tc Σ simple_let_syn).
Example simple_let_eq :
  simple_let 1 = 1.
Proof. reflexivity. Qed.

Definition simple_let_with_vars_syn :=
  [|
   \x : Nat =>
     let y : Nat := 1 in y
   |].

MetaCoq Unquote Definition simple_let' := (expr_to_tc Σ (indexify [] simple_let_with_vars_syn)).
Example simple_let_eq' :
  simple_let' 0 = 1.
Proof. reflexivity. Qed.


Definition negb_syn :=
  [|
   \x : Bool =>
          case x : Bool return Bool of
          | True -> False
          | False -> True
  |].

MetaCoq Unquote Definition negb' := (expr_to_tc Σ (indexify [] negb_syn)).

Example negb'_correct : forall b, negb' b = negb b.
Proof.
  destruct b; easy.
Qed.

Definition myplus_syn :=
  [| \x : Nat => \y : Nat => x + y |].

MetaCoq Unquote Definition myplus := (expr_to_tc Σ (indexify [] myplus_syn)).

Definition stupid_case :=
  fun y : Set => fun x : y => fun z : list y =>
                match z with
                | [] => x
                | _ => x
                end.

MetaCoq Quote Definition q_stupid_case := Eval compute in stupid_case.
MetaCoq Quote Recursively Definition q_stupid_case_rec := stupid_case.
MetaCoq Quote Definition cons_syn := (fun A : Set => cons A).

Definition case_ex :=
  [| \\y => \x : 'y => \z : List 'y =>
         case z : List 'y return 'y of
         | Nil -> x
         | Cons "hd" "tl" -> x |].

(* Compute (expr_to_tc Σ (indexify [] case_ex)). *)

MetaCoq Unquote Definition case_ex_def := (expr_to_tc Σ (indexify [] case_ex)).

Example case_ex_def_unquote :
  case_ex_def =
    fun (y : Set) (x : y) (z : list y) =>
      match z with
      | [] | _ => x
      end.
Proof. reflexivity. Qed.

Definition case_ex1 :=
  [| \\y => \"w" : 'y => \x : 'y => \z : List 'y =>
         case z : List 'y return Prod 'y 'y of
         | Nil -> {eConstr Prod "pair"} {eTy (tyVar y)} {eTy (tyVar y)} x x
         | Cons "hd" "tl" -> {eConstr Prod "pair"} {eTy (tyVar y)} {eTy (tyVar y)} "hd" x |].

(* Compute (expr_to_tc Σ (indexify [] case_ex1)). *)

MetaCoq Unquote Definition case_ex_def1 := (expr_to_tc Σ (indexify [] case_ex1)).

Definition case_ex2 :=
  [| \\y => case ({eConstr List "nil"} "y") : List 'y return List 'y of
            | Nil -> {eConstr List "nil"} "y"
            | Cons "hd" "tl" -> {eConstr List "nil"} "y" |].

(* Compute indexify [] case_ex2. *)
(* Compute (expr_to_tc Σ (indexify [] case_ex2)). *)

MetaCoq Unquote Definition case_ex_def2 := (expr_to_tc Σ (indexify [] case_ex2)).

Definition example_type := [! ∀ "A", ∀ "B", Prod '"A" '"B" !].

MetaCoq Unquote Definition ex_type_def := (type_to_tc (indexify_type [] example_type)).

Definition map_syn :=
gdInd "AMap" 2 [("ANil", []);
                  ("ACons", [(None,tyRel 1); (None,tyRel 0);
                               (None,(tyApp (tyApp (tyInd "AMap") (tyRel 1)) (tyRel 0)))])] false.

MetaCoq Unquote Inductive (global_to_tc map_syn).

Definition single_field_record_syn :=
  [\ record "sfrec" := "mkRec" {"fld" : Nat } \].

MetaCoq Unquote Inductive (global_to_tc single_field_record_syn).
