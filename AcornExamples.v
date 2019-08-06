(** * Examples of contracts originating from the actual Acorn contracts *)
Require Import ZArith.
Require Import String.
Require Import Ast CustomTactics.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
From Template Require Import All.

Import MonadNotation.

Import ListNotations.

Open Scope string.

Fixpoint translateData (es : list global_dec) :=
  match es with
  | [] => tmPrint "Done."
  | e :: es' =>
    coq_data <- tmEval all (trans_global_dec e) ;;
    tmMkInductive coq_data;;
    translateData es'
  end.

Fixpoint translateDefs Σ (es : list (string * expr)) :=
  match es with
  | [] => tmPrint "Done."
  | (name, e) :: es' =>
    coq_expr <- tmEval all (expr_to_term Σ (reindexify 0 e)) ;;
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

(** The [Bool] module from the standard library of Acorn *)
Module AcornBool.
  Definition AB_data := [gdInd "Bool" 0 [("True_coq", []);("False_coq", [])] false].
  (*---------------------*)
  Definition AB_functions := [("not", eLambda "x" ((tyInd "Bool")) (eCase ((tyInd "Bool"), 0) ((tyInd "Bool")) (eRel 0) [(pConstr "True_coq" [], eConstr "Bool" "False_coq");(pConstr "False_coq" [], eConstr "Bool" "True_coq")]))].
  Run TemplateProgram (translateData AB_data).

  Run TemplateProgram (translateDefs (StdLib.Σ ++ AB_data)%list AB_functions).
End AcornBool.

(** The [Maybe] module from the standard library of Acorn *)

Module AcornMaybe.
  Import AcornBool.

  Definition AM_data :=  [gdInd "Maybe" 1 [("Nothing_coq", []);("Just_coq", [(TC.nAnon, tyRel 0)])] false].
  (*---------------------*)
  Definition AM_functions := [("isJust", eTyLam "A" (eLambda "x" ((tyApp (tyInd "Maybe") (tyRel 0))) (eCase ((tyApp (tyInd "Maybe") (tyRel 0)), 0) ((tyInd "Bool")) (eRel 0) [(pConstr "Nothing_coq" [], eConstr "Bool" "False_coq");(pConstr "Just_coq" ["x0"], eConstr "Bool" "True_coq")])))].

  Run TemplateProgram (translateData AM_data).

  Run TemplateProgram (translateDefs (StdLib.Σ ++ AM_data ++ AB_data)%list AM_functions).

End AcornMaybe.

Import AcornMaybe.

Print isJust.

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
  Definition plusInt64 := Z.add.
  Definition minusInt64 := Z.sub.
End Prim.

(** Data type definitions corresponding representation of the module [CoqExamples] above *)
Definition acorn_datatypes :=
[gdInd "Msg" 0 [("Inc_coq", [(TC.nAnon, tyInd "Z")]);("Dec_coq", [(TC.nAnon, tyInd "Z")])] false;gdInd "CState" 0 [("CState_coq", [(TC.nAnon, tyInd "Z");(TC.nAnon, tyInd "string")])] false].

Run TemplateProgram (translateData acorn_datatypes).

Definition Σ' :=
  (StdLib.Σ ++ acorn_datatypes)%list.

Import Prim.

(** Function definitions corresponding representation of the module [CoqExamples] above *)
Definition acorn_module : list (string * expr) := [("owner", eLambda "x" (tyInd "CState") (eCase (tyInd "CState", 0) (tyInd "string") (eRel 0) [(pConstr "CState_coq" ["x0"
;"x1"], eRel 0)]))
;("balance", eLambda "x" (tyInd "CState") (eCase (tyInd "CState", 0) (tyInd "Z") (eRel 0) [(pConstr "CState_coq" ["x0"
;"x1"], eRel 1)]))
;("count", eLambda "x" (tyInd "CState") (eLambda "x" (tyInd "Msg") (eCase (tyInd "Msg", 0) (tyInd "CState") (eRel 0) [(pConstr "Inc_coq" ["x0"], eApp (eApp (eConstr "CState" "CState_coq") (eApp (eApp (eConst "plusInt64") (eApp (eConst "balance") (eRel 2))) (eRel 0))) (eApp (eConst "owner") (eRel 2)))
;(pConstr "Dec_coq" ["x0"], eApp (eApp (eConstr "CState" "CState_coq") (eApp (eApp (eConst "minusInt64") (eApp (eConst "balance") (eRel 2))) (eRel 0))) (eApp (eConst "owner") (eRel 2)))])))].

Run TemplateProgram (translateDefs Σ' acorn_module).

Open Scope Z_scope.

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

Definition balance : CState -> Z := fun x =>
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