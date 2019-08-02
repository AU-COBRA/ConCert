(** * Examples of contracts originating from the actual Acorn contracts *)
Require Import String.
Require Import Ast CustomTactics.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
From Template Require Import All.

Import MonadNotation.

Import ListNotations.

Open Scope string.

Fixpoint translateDefs Σ (es : list (string * expr)) :=
  match es with
  | [] => tmPrint "Done."
  | (name, e) :: es' =>
    coq_expr <- tmEval all (expr_to_term Σ e) ;;
    tm <- tmUnquote coq_expr ;;
    def_txt <- tmEval all ("Definition " ++ name ++ " :=");;
    def_ty <- tmEval all (my_projT1 tm);;
    def <- tmEval cbn (my_projT2 tm);;
    (* tmDefinition name def;; *)
    tmMkDefinition name coq_expr;;
    tmPrint def_txt;;
    tmPrint def_ty;;
    tmPrint def;;
    translateDefs Σ es'
  end.


(** Concrete syntax *)

(*
module CoqExamples where

import Prim

data Msg = Inc [Int64] | Dec [Int64]

data CState = CState [Int64, {address}]

definition owner (s :: CState) =
   case s of
     CState _ d -> d

definition balance (s :: CState) =
   case s of
     CState x _ -> x

definition count (s :: CState) (msg :: Msg) =
  case msg of
    Inc a ->
      CState (Prim.plusInt64 (balance s) a) (owner s)
    Dec a ->
      CState (Prim.minusInt64 (balance s) a) (owner s)
 *)

(** For now, we assume that data types are already translated *)

Module Prim.
  Definition plusInt64 := plus.
  Definition minusInt64 := minus.
End Prim.

Inductive CState := CState_coq : nat -> string -> CState.

Import StdLib.

Definition Address_syn := "string".

Definition Nat_syn := "nat".

Inductive Msg := Inc_coq : nat -> Msg | Dec_coq : nat -> Msg.

Definition Σ' :=
  (Σ ++
     [ gdInd "CState" 0 [("CState_coq",
                           [(nAnon,tyInd Nat_syn); (nAnon,tyInd Address_syn)])] false
       ; gdInd "Msg" 0 [("Inc_coq", [(nAnon,tyInd Nat_syn)]);
                        ("Dec_coq", [(nAnon,tyInd Nat_syn)])] false]
      )%list.



Import Prim.

(** Corresponding representation of the module [CoqExamples] above *)
Definition acorn_module : list (string * expr) := [("owner", eLambda "x" (tyInd "CState") (eCase (tyInd "CState", 0) (tyInd "string") (eRel 0) [(pConstr "CState_coq" ["x0"
;"x1"], eRel 0)]))
;("balance", eLambda "x" (tyInd "CState") (eCase (tyInd "CState", 0) (tyInd "nat") (eRel 0) [(pConstr "CState_coq" ["x0"
;"x1"], eRel 1)]))
;("count", eLambda "x" (tyInd "CState") (eLambda "x" (tyInd "Msg") (eCase (tyInd "Msg", 0) (tyInd "CState") (eRel 0) [(pConstr "Inc_coq" ["x0"], eApp (eApp (eConstr "CState" "CState_coq") (eApp (eApp (eConst "plusInt64") (eApp (eConst "balance") (eRel 2))) (eRel 0))) (eApp (eConst "owner") (eRel 2)))
;(pConstr "Dec_coq" ["x0"], eApp (eApp (eConstr "CState" "CState_coq") (eApp (eApp (eConst "minusInt64") (eApp (eConst "balance") (eRel 2))) (eRel 0))) (eApp (eConst "owner") (eRel 2)))])))].

Run TemplateProgram (translateDefs Σ' acorn_module).

Lemma inc_correct init_state n i final_state :
  (* precondition *)
  balance init_state = n ->

  (* sending "increment" *)
  count init_state (Inc_coq i) = final_state ->

  (* result *)
  balance final_state = n + i.
Proof.
  intros Hinit Hrun. subst. reflexivity.
Qed.


Module ForPeresentation.

Definition owner : CState -> string := fun x =>
  match x with
  | CState_coq _ x1 => x1
  end.

Definition balance : CState -> nat := fun x =>
  match x with
  | CState_coq x0 _ => x0
  end.

Definition count
  : CState -> Msg -> CState := fun x x0 =>
 match x0 with
 | Inc_coq x1 =>
     CState_coq (plusInt64 (balance x) x1)
                (owner x)
 | Dec_coq x1 =>
   CState_coq (minusInt64 (balance x) x1)
              (owner x)
 end.

End ForPeresentation.