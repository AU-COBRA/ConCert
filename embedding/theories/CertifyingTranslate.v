(** * Certifying translation *)

(** Proving that concrete expressions translate correctly *)

From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import EvalE.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import EnvSubst.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import PCUICtoTemplate.
From Coq Require Import Basics.
From Coq Require Import String.
From Coq Require Import List.

Import ListNotations.
Import NamelessSubst.
Import BaseTypes.
Import StdLib.

Notation "'eval' ( Σ , n , e )" := (expr_eval_i Σ n [] e) (at level 100).

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Definition x := "x".
Definition y := "y".
Definition z := "z".


(** ** Negation on booleans *)

(** First we define a conversion function taking a bool
    and producing the corresponding syntactic λsmart value *)
Definition of_bool : bool -> val :=
  fun b => if b then vConstr Bool "true" []
        else vConstr Bool "false" [].

Definition my_negb_syn :=
  [| \x : Bool =>
          case x : Bool return Bool of
          | True -> False
          | False -> True |].

(* Compute expr_to_tc Σ (indexify nil my_negb_syn). *)

(** We translate and unquote using the ConCert embedding feature *)
MetaCoq Unquote Definition my_negb := (expr_to_tc Σ (indexify nil my_negb_syn)).

(** We prove that the running the interpreter with [my_negb_syn] applied
    to an expression originating from Coq' boolean value computes the same
    result as the unquoted function [my_negb]. As a result, we do not
    depend on correctness of [unquote] *)
Lemma my_negb_correct b :
  exists n v,
    eval(Σ, n,
         indexify nil ([| {my_negb_syn} {of_val_i (of_bool b)} |])) = Ok v
      /\ v = of_bool (negb b).
Proof.
  destruct b; exists 3; eexists; simpl; eauto.
Qed.

(** One can prove similar results any non-recursive definition.
    Proofs in this case would require just case analysis and computation.
    For recursive definitions proofs would require induction
    and some additional lemmas *)
