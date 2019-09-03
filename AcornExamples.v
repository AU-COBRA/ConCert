(** * Examples of library code and contracts originating from the actual Acorn implementation  *)
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
    (* tm <- tmUnquote coq_expr ;; *)
    def_txt <- tmEval all ("Definition " ++ name ++ " :=");;
    (* def_ty <- tmEval all (my_projT1 tm);; *)
    (* def <- tmEval cbn (my_projT2 tm);; *)
    (* tmDefinition name def;; *)
    print_nf name;;
    print_nf coq_expr;;
    tmMkDefinition name coq_expr;;
    (* tmPrint def_txt;; *)
    (* tmPrint def_ty;; *)
    (* tmPrint def;; *)
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

Module AcornProd.

  Definition AP_data := [gdInd "Pair" 2 [("Pair_coq", [(TC.nAnon, tyRel 1);(TC.nAnon, tyRel 0)])] false].
  (*---------------------*)

  Definition AP_functions :=
    [("fst", eTyLam "A" (eTyLam "A" (eLambda "x" ((tyApp (tyApp (tyInd "Pair") (tyRel 1)) (tyRel 0))) (eCase ((tyApp (tyApp (tyInd "Pair") (tyRel 1)) (tyRel 0)), 0) (tyRel 1) (eRel 0) [(pConstr "Pair_coq" ["x0";"x1"], eRel 1)]))));("snd", eTyLam "A" (eTyLam "A" (eLambda "x" ((tyApp (tyApp (tyInd "Pair") (tyRel 1)) (tyRel 0))) (eCase ((tyApp (tyApp (tyInd "Pair") (tyRel 1)) (tyRel 0)), 0) (tyRel 0) (eRel 0) [(pConstr "Pair_coq" ["x0";"x1"], eRel 0)]))))].

  Run TemplateProgram (translateData AP_data).

  Run TemplateProgram (translateDefs (StdLib.Σ ++ AP_data)%list AP_functions).
End AcornProd.

Module AcornListBase.
  Import AcornBool.
  Import AcornMaybe.
  Import AcornProd.

  Definition ALB_data :=  [gdInd "List" 1 [("Nil_coq", []);("Cons_coq", [(TC.nAnon, tyRel 0);(TC.nAnon, (tyApp (tyInd "List") (tyRel 0)))])] false].

  (*---------------------*)

  Definition ALB_functions := [("singleton", eTyLam "A" (eLambda "x" (tyRel 0) (eApp (eApp (eApp (eConstr "List" "Cons_coq") (eTy (tyRel 0))) (eRel 0)) (eApp (eConstr "List" "Nil_coq") (eTy (tyRel 0))))))
  ;
("foldr", eTyLam "A" (eTyLam "A" (eLambda "x" (tyArr (tyRel 1) (tyArr (tyRel 0) (tyRel 0))) (eLambda "x" (tyRel 0) (eLetIn "f" (eFix "rec" "x" ((tyApp (tyInd "List") (tyRel 1))) (tyRel 0) (eCase ((tyApp (tyInd "List") (tyRel 1)), 1) (tyRel 0) (eRel 0) [(pConstr "Nil_coq" [], eRel 2);(pConstr "Cons_coq" ["x0";"x1"], eApp (eApp (eRel 5) (eRel 1)) (eApp (eRel 3) (eRel 0)))])) (tyArr ((tyApp (tyInd "List") (tyRel 1))) (tyRel 0)) (eRel 0))))))
 ;
  ("map", eTyLam "A" (eTyLam "A" (eLambda "x" (tyArr (tyRel 1) (tyRel 0)) (eApp (eApp (eApp (eApp (eConst "foldr") (eTy (tyRel 1))) (eTy ((tyApp (tyInd "List") (tyRel 0))))) (eLambda "x" (tyRel 1) (eApp (eApp (eConstr "List" "Cons_coq") (eTy (tyRel 0))) (eApp (eRel 1) (eRel 0))))) (eApp (eConstr "List" "Nil_coq") (eTy (tyRel 0)))))))
 ;

("foldl_alt", eTyLam "A" (eTyLam "A" (eLambda "x" (tyArr (tyRel 0) (tyArr (tyRel 1) (tyRel 0))) (eLetIn "f" (eFix "rec" "x" ((tyApp (tyInd "List") (tyRel 1))) (tyArr (tyRel 0) (tyRel 0)) (eLambda "x" (tyRel 0) (eCase ((tyApp (tyInd "List") (tyRel 1)), 0) (tyRel 0) (eRel 1) [(pConstr "Nil_coq" [], eRel 0);(pConstr "Cons_coq" ["x0";"x1"], eApp (eApp (eRel 4) (eRel 0)) (eApp (eApp (eRel 5) (eRel 2)) (eRel 1)))]))) (tyArr ((tyApp (tyInd "List") (tyRel 1))) (tyArr (tyRel 0) (tyRel 0))) (eRel 0)))))
;("foldl", eTyLam "A" (eTyLam "A" (eLambda "x" (tyArr (tyRel 0) (tyArr (tyRel 1) (tyRel 0))) (eLambda "x" (tyRel 0) (eLambda "x" ((tyApp (tyInd "List") (tyRel 1))) (eApp (eApp (eApp (eApp (eApp (eConst "foldl_alt") (eTy (tyRel 1))) (eTy (tyRel 0))) (eRel 2)) (eRel 0)) (eRel 1)))))))
 ;
 ("concat", eTyLam "A" (eLambda "x" ((tyApp (tyInd "List") (tyRel 0))) (eLambda "x" ((tyApp (tyInd "List") (tyRel 0))) (eApp (eApp (eApp (eApp (eApp (eConst "foldr") (eTy (tyRel 0))) (eTy ((tyApp (tyInd "List") (tyRel 0))))) (eApp (eConstr "List" "Cons_coq") (eTy (tyRel 0)))) (eRel 0)) (eRel 1)))))
;
 ("zipWith", eTyLam "A" (eTyLam "A" (eTyLam "A" (eLambda "x" (tyArr (tyRel 2) (tyArr (tyRel 1) (tyRel 0))) (eLetIn "f" (eFix "rec" "x" ((tyApp (tyInd "List") (tyRel 2))) (tyArr ((tyApp (tyInd "List") (tyRel 1))) ((tyApp (tyInd "List") (tyRel 0)))) (eLambda "x" ((tyApp (tyInd "List") (tyRel 1))) (eCase ((tyApp (tyInd "List") (tyRel 2)), 0) ((tyApp (tyInd "List") (tyRel 0))) (eRel 1) [(pConstr "Nil_coq" [], eApp (eConstr "List" "Nil_coq") (eTy (tyRel 0)));(pConstr "Cons_coq" ["x0";"x1"], eCase ((tyApp (tyInd "List") (tyRel 1)), 0) ((tyApp (tyInd "List") (tyRel 0))) (eRel 2) [(pConstr "Nil_coq" [], eApp (eConstr "List" "Nil_coq") (eTy (tyRel 0)));(pConstr "Cons_coq" ["x0";"x1"], eApp (eApp (eApp (eConstr "List" "Cons_coq") (eTy (tyRel 0))) (eApp (eApp (eRel 7) (eRel 3)) (eRel 1))) (eApp (eApp (eRel 6) (eRel 2)) (eRel 0)))])]))) (tyArr ((tyApp (tyInd "List") (tyRel 2))) (tyArr ((tyApp (tyInd "List") (tyRel 1))) ((tyApp (tyInd "List") (tyRel 0))))) (eRel 0))))));
("reverse", eTyLam "A" (eApp (eApp (eApp (eApp (eConst "foldl") (eTy (tyRel 0))) (eTy ((tyApp (tyInd "List") (tyRel 0))))) (eLambda "x" ((tyApp (tyInd "List") (tyRel 0))) (eLambda "x" (tyRel 0) (eApp (eApp (eApp (eConstr "List" "Cons_coq") (eTy (tyRel 0))) (eRel 0)) (eRel 1))))) (eApp (eConstr "List" "Nil_coq") (eTy (tyRel 0)))))
;("zip", eTyLam "A" (eTyLam "A" (eApp (eApp (eApp (eApp (eConst "zipWith") (eTy (tyRel 1))) (eTy (tyRel 0))) (eTy ((tyApp (tyApp (tyInd "Pair") (tyRel 1)) (tyRel 0))))) (eApp (eApp (eConstr "Pair" "Pair_coq") (eTy (tyRel 1))) (eTy (tyRel 0))))))
;("filter", eTyLam "A" (eLambda "x" (tyArr (tyRel 0) ((tyInd "Bool"))) (eApp (eApp (eApp (eApp (eConst "foldr") (eTy (tyRel 0))) (eTy ((tyApp (tyInd "List") (tyRel 0))))) (eLambda "x" (tyRel 0) (eLambda "x" ((tyApp (tyInd "List") (tyRel 0))) (eCase ((tyInd "Bool"), 0) ((tyApp (tyInd "List") (tyRel 0))) (eApp (eRel 2) (eRel 1)) [(pConstr "True_coq" [], eApp (eApp (eApp (eConstr "List" "Cons_coq") (eTy (tyRel 0))) (eRel 1)) (eRel 0));(pConstr "False_coq" [], eRel 0)])))) (eApp (eConstr "List" "Nil_coq") (eTy (tyRel 0))))))
].

  Run TemplateProgram (translateData ALB_data).

  Definition gEnv := (StdLib.Σ ++ ALB_data ++ AcornMaybe.AM_data ++ AcornBool.AB_data ++ AcornProd.AP_data)%list.

  Definition foldl_syn := eTyLam "A" (eTyLam "A" (eLambda "x" (tyArr (tyRel 0) (tyArr (tyRel 1) (tyRel 0))) (eLetIn "f" (eFix "rec" "x" (tyRel 0) (tyArr ((tyApp (tyInd "List") (tyRel 1))) (tyRel 0)) (eLambda "x" ((tyApp (tyInd "List") (tyRel 1))) (eCase ((tyApp (tyInd "List") (tyRel 1)), 0) (tyRel 0) (eRel 0) [(pConstr "Nil_coq" [], eRel 1);(pConstr "Cons_coq" ["x0";"x1"], eApp (eApp (eRel 4) (eApp (eApp (eRel 5) (eRel 3)) (eRel 1))) (eRel 0))]))) (tyArr (tyRel 0) (tyArr ((tyApp (tyInd "List") (tyRel 1))) (tyRel 0))) (eRel 0)))).

  Compute (expr_to_term gEnv (reindexify 0 foldl_syn)).


  Run TemplateProgram
      (translateDefs gEnv ALB_functions).

  Print foldr.
  Print zipWith.

  Definition OakList := List.

  Fixpoint from_oak {A : Set} (oakL : OakList A) : list A :=
    match oakL with
    | Cons_coq _ hd tl => hd :: from_oak tl
    | Nil_coq _ => []
    end.

  Fixpoint to_oak {A : Set} (coqL : list A) : OakList A :=
    match coqL with
    | hd :: tl => Cons_coq _ hd (to_oak tl)
    | nil => Nil_coq _
    end.

  Lemma to_from_oak (A : Set) (l : OakList A) : to_oak (from_oak l) = l.
  Proof.
    induction l;simpl;congruence.
  Qed.

  Lemma from_to_oak (A : Set) (l : list A) : from_oak (to_oak l) = l.
  Proof.
    induction l;simpl;congruence.
  Qed.

  Arguments foldr {_ _}.
  Arguments concat {_}.

  Lemma oak_foldr_coq_fold_right (A B : Set) (l : OakList A) (f : A -> B -> B) a :
    foldr f a l = fold_right f a (from_oak l).
  Proof.
    induction l;simpl;auto.
    f_equal. congruence.
  Qed.

  Open Scope list.

  Lemma concat_app (A : Set) (l1 l2 : OakList A) :
  concat l1 l2 = to_oak (from_oak l1 ++ from_oak l2).
  Proof.
    revert l2.
    induction l1;intros l2;destruct l2;simpl;try rewrite to_from_oak;auto.
    f_equal. rewrite app_nil_r. rewrite to_from_oak.
    clear IHl1; induction l1;simpl. congruence. now f_equal.
    change (a0 :: from_oak l2) with (from_oak (Cons_coq _ a0 l2)).
    now f_equal.
  Qed.

  Hint Rewrite oak_foldr_coq_fold_right concat_app from_to_oak : hints.

  Lemma concat_assoc :
    forall (A : Set) (l m n : OakList A), concat l (concat m n) = concat (concat l m) n.
  Proof.
    intros. autorewrite with hints. f_equal.
    apply app_assoc.
  Qed.

  Lemma foldr_concat (A B : Set) (f : A -> B -> B) (l l' : OakList A) (i : B) :
      foldr f i (concat l l') = foldr f (foldr f i l') l.
  Proof. autorewrite with hints;apply fold_right_app. Qed.

End AcornListBase.

Module AcornBlochain.

  Definition ABl_data :=  [gdInd "Caller" 0 [("CallerContract_coq", [(TC.nAnon, tyInd "nat")]);("CallerAccount_coq", [(TC.nAnon, tyInd "string")])] false;gdInd "ChainContext" 0 [("ChainContext_coq", [(TC.nAnon, tyInd "nat");(TC.nAnon, tyInd "nat");(TC.nAnon, tyInd "nat")])] false;gdInd "InitContext" 0 [("InitContext_coq", [(TC.nAnon, (tyInd "ChainContext"));(TC.nAnon, tyInd "string")])] false;gdInd "ReceiveContext" 0 [("ReceiveContext_coq", [(TC.nAnon, (tyInd "ChainContext"));(TC.nAnon, tyInd "string");(TC.nAnon, tyInd "nat")])] false].

  (*---------------------*)

  Definition ABl_functions := [("slotNumber", eLambda "x" ((tyInd "ChainContext")) (eCase ((tyInd "ChainContext"), 0) (tyInd "nat") (eRel 0) [(pConstr "ChainContext_coq" ["x0";"x1";"x2"], eRel 2)]))
;("blockHeight", eLambda "x" ((tyInd "ChainContext")) (eCase ((tyInd "ChainContext"), 0) (tyInd "nat") (eRel 0) [(pConstr "ChainContext_coq" ["x0";"x1";"x2"], eRel 1)]))
;("finalizedHeight", eLambda "x" ((tyInd "ChainContext")) (eCase ((tyInd "ChainContext"), 0) (tyInd "nat") (eRel 0) [(pConstr "ChainContext_coq" ["x0";"x1";"x2"], eRel 0)]))
;("initOrigin", eLambda "x" ((tyInd "InitContext")) (eCase ((tyInd "InitContext"), 0) (tyInd "string") (eRel 0) [(pConstr "InitContext_coq" ["x0";"x1"], eRel 0)]))
;("initChain", eLambda "x" ((tyInd "InitContext")) (eCase ((tyInd "InitContext"), 0) ((tyInd "ChainContext")) (eRel 0) [(pConstr "InitContext_coq" ["x0";"x1"], eRel 1)]))
;("receiveChain", eLambda "x" ((tyInd "ReceiveContext")) (eCase ((tyInd "ReceiveContext"), 0) ((tyInd "ChainContext")) (eRel 0) [(pConstr "ReceiveContext_coq" ["x0";"x1";"x2"], eRel 2)]))
;("receiveOrigin", eLambda "x" ((tyInd "ReceiveContext")) (eCase ((tyInd "ReceiveContext"), 0) (tyInd "string") (eRel 0) [(pConstr "ReceiveContext_coq" ["x0";"x1";"x2"], eRel 1)]))
;("receiveSelfAddress", eLambda "x" ((tyInd "ReceiveContext")) (eCase ((tyInd "ReceiveContext"), 0) (tyInd "nat") (eRel 0) [(pConstr "ReceiveContext_coq" ["x0";"x1";"x2"], eRel 0)]))].

  Run TemplateProgram (translateData ABl_data).
  Run TemplateProgram (translateDefs (StdLib.Σ ++ ABl_data)%list ABl_functions).
End AcornBlochain.

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

Module Recursion.

  Definition R_data := [gdInd "Nat" 0 [("Zero_coq", []);("Suc_coq", [(TC.nAnon, (tyInd "Nat"))])] false].
(*---------------------*)

  Open Scope nat.

  Definition R_functions := [("add", eLetIn "f" (eFix "rec" "x" ((tyInd "Nat")) (tyArr (tyInd "Nat") (tyInd "Nat")) (eLambda "x" ((tyInd "Nat")) (eCase ((tyInd "Nat"), 0) ((tyInd "Nat")) (eRel 1) [(pConstr "Zero_coq" [], eRel 0);(pConstr "Suc_coq" ["x0"], eApp (eConstr "Nat" "Suc_coq") (eApp (eApp (eRel 3) (eRel 0)) (eRel 1)))]))) (tyArr ((tyInd "Nat")) (tyArr (tyInd "Nat") (tyInd "Nat"))) (eRel 0))].

  Run TemplateProgram (translateData R_data).

  Run TemplateProgram (translateDefs (StdLib.Σ ++ R_data)%list R_functions).

  Print add.



  Fixpoint Nat_nat (n : Nat) : nat :=
    match n with
    | Zero_coq => O
    | Suc_coq n' => S (Nat_nat n')
    end.

  Fixpoint nat_Nat (n : nat) : Nat :=
    match n with
    | O => Zero_coq
    | S n' => Suc_coq (nat_Nat n')
    end.

  Lemma Nat_nat_left n : nat_Nat (Nat_nat n) = n.
  Proof. induction n;simpl;f_equal;auto. Qed.


  Lemma Nat_nat_right n : Nat_nat (nat_Nat n) = n.
  Proof. induction n;simpl;f_equal;auto. Qed.

  Hint Resolve Nat_nat_left Nat_nat_right : hints.

  Local Coercion Nat_nat : Nat >-> nat.
  Local Coercion nat_Nat : nat >-> Nat.

  Lemma add_correct (n m : Nat) :
  add n m = n + m.
  Proof. induction n;simpl;f_equal;auto with hints. Qed.


End Recursion.


(** Predicativity *)
Definition id := fun (A : Set) (a : A) => a.

Definition id_id_syn := eApp (eApp (eConst "id") (eTy (tyForall "A" (tyArr (tyRel 0) (tyRel 0))))) (eConst "id").

Compute (expr_to_term StdLib.Σ (reindexify 0 id_id_syn)).

Eval compute in (expr_to_term StdLib.Σ (reindexify 0 id_id_syn)).

Definition id_forall := eLambda "x" (tyForall "A" (tyArr (tyRel 0) (tyRel 0))) (eRel 0).

Compute (expr_to_term StdLib.Σ (reindexify 0 id_forall)).

(** Application [id id] fails, since [A] must be [Set], but type of
 [id] is [forall A, A -> A], which lives in [Type]  *)
Fail Make Definition id_id := Eval compute in (expr_to_term StdLib.Σ (reindexify 0 id_id_syn)).
