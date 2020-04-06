Require Import String Basics.
Require Import List.
Require Import Ast Notations EvalE PCUICtoTemplate PCUICTranslate.

From MetaCoq.Template Require Ast.
(* From MetaCoq.Template Require Import TemplateMonad. *)
(* From MetaCoq.Template Require Import monad_utils. *)

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Import ListNotations.
Module TC := Template.BasicAst.

(* Import MonadNotation. *)
Import BaseTypes.
Import StdLib.

Module MC:=MetaCoq.Template.Ast.
Import BasicAst.

(** ** MetaCoq demo *)

(** Quote *)
Quote Definition id_nat_syn := (fun x : nat => x).
(* Print id_nat_syn. *)
(* Ast.tLambda (nNamed "x")
   (Ast.tInd {| TC.inductive_mind := "nat"; TC.inductive_ind := 0 |}
      []) (Ast.tRel 0) : Ast.term *)

(** Unquote *)
Make Definition plus_one :=
  (MC.tLambda (nNamed "x") (MC.tInd (mkInd "nat"  0 ) nil)
              (MC.tApp (MC.tConstruct (mkInd "nat" 0) 1 nil)
                       (MC.tRel 0 :: nil))).

(* Print plus_one. *)
(* fun x : nat => S x : nat -> nat *)

Definition x := "x".
Definition y := "y".
Definition z := "z".

(** Negation function syntax *)
Definition my_negb_syn :=
  [| \x : Bool => case x : Bool return Bool of
                   | True -> False
                   | False -> True  |].

Unset Printing Notations.

(* Print my_negb_syn. *)

Set Printing Notations.

(* Execute the program using the interpreter *)
Compute (expr_eval_n Σ 3 nil [|{my_negb_syn} True |]).

Compute (expr_eval_i Σ 3 nil (indexify nil negb_app_true)).


(* Make a Coq function from the AST of the program *)
Make Definition coq_negb_app_true :=
  (expr_to_tc Σ (indexify nil negb_app_true)).

(* Print coq_negb_app_true. *)

Make Definition my_negb :=
  (expr_to_tc Σ (indexify nil my_negb_syn)).

Lemma my_negb_coq_negb b :
  my_negb b = negb b.
Proof. reflexivity. Qed.

Compute (expr_eval_n Σ 3 nil my_negb_syn).
