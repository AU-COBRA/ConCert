Require Import String Basics ZArith.
Require Import List.
Require Import Ast Notations EvalE PCUICtoTemplate PCUICTranslate AcornExamples.

From MetaCoq.Template Require Ast.

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Import ListNotations.
Module TC := Template.BasicAst.

Import BaseTypes.
Import StdLib.

Module MC:=MetaCoq.Template.Ast.
Import BasicAst.

(** ** MetaCoq demo *)

(** Quote *)
Quote Definition id_nat_syn := (fun x : nat => x).
Print id_nat_syn.
(* Ast.tLambda (nNamed "x")
   (Ast.tInd {| TC.inductive_mind := "nat"; TC.inductive_ind := 0 |}
      []) (Ast.tRel 0) : Ast.term *)

(** Unquote *)
Make Definition plus_one :=
  (MC.tLambda (nNamed "x") (MC.tInd (mkInd "nat"  0 ) nil)
              (MC.tApp (MC.tConstruct (mkInd "nat" 0) 1 nil)
                       (MC.tRel 0 :: nil))).

Print plus_one.
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

Print my_negb_syn.

Set Printing Notations.

(* Execute the program using the interpreter *)
Compute (expr_eval_n Σ 3 nil [|{my_negb_syn} True |]).

Compute (expr_eval_i Σ 3 nil (indexify nil [|{my_negb_syn} True |])).


(* Make a Coq function from the AST of the program *)
Make Definition my_negb :=
  (expr_to_tc Σ (indexify nil my_negb_syn)).

Print my_negb.

(** [my_neg] is equivalent to [negb] from the standard library *)
Lemma my_negb_coq_negb b :
  my_negb b = negb b.
Proof. reflexivity. Qed.

Module CounterContract.
  (** Concrete syntax in Acorn *)

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

  (** AST of Data type definitions and functions corresponding to the module [CoqExamples] above *)
  Definition CounterData := [gdInd "Msg" 0 [("Inc_coq", [(None, tyInd "Z")]);("Dec_coq", [(None, tyInd "Z")])] false;gdInd "CState" 0 [("CState_coq", [(None, tyInd "Z");(None, tyInd "string")])] false].
  (*---------------------*)
  Definition CounterFunctions := [("owner", eLambda "x" ((tyInd "CState")) (eCase ("CState", []) (tyInd "string") (eRel 0) [(pConstr "CState_coq" ["x0";"x1"], eRel 0)])) ;("balance", eLambda "x" ((tyInd "CState")) (eCase ("CState", []) (tyInd "Z") (eRel 0) [(pConstr "CState_coq" ["x0";"x1"], eRel 1)])); ("count", eLambda "x" ((tyInd "ReceiveContext")) (eLambda "x" ((tyInd "CState")) (eLambda "x" ((tyInd "Caller")) (eLambda "x" (tyInd "nat") (eLambda "x" ((tyApp (tyInd "Maybe") ((tyInd "Msg")))) (eCase ("Maybe", [(tyInd "Msg")]) ((tyApp (tyApp (tyInd "Pair") ((tyInd "CState"))) ((tyInd "Transaction")))) (eRel 0) [(pConstr "Nothing_coq" [], eApp (eApp (eApp (eApp (eConstr "Pair" "Pair_coq") (eTy ((tyInd "CState")))) (eTy ((tyInd "Transaction")))) (eRel 3)) (eConst "TxNone")); (pConstr "Just_coq" ["x0"], eCase ("Msg", []) ((tyApp (tyApp (tyInd "Pair") ((tyInd "CState"))) ((tyInd "Transaction")))) (eRel 0) [(pConstr "Inc_coq" ["x0"], eLetIn "x" (eApp (eApp (eConstr "CState" "CState_coq") (eApp (eApp (eConst "plusInt64") (eApp (eConst "balance") (eRel 5))) (eRel 0))) (eApp (eConst "owner") (eRel 5))) ((tyInd "CState")) (eApp (eApp (eApp (eApp (eConstr "Pair" "Pair_coq") (eTy ((tyInd "CState")))) (eTy ((tyInd "Transaction")))) (eRel 0)) (eConst "TxNone"))); (pConstr "Dec_coq" ["x0"], eLetIn "x" (eApp (eApp (eConstr "CState" "CState_coq") (eApp (eApp (eConst "minusInt64") (eApp (eConst "balance") (eRel 5))) (eRel 0))) (eApp (eConst "owner") (eRel 5))) ((tyInd "CState")) (eApp (eApp (eApp (eApp (eConstr "Pair" "Pair_coq") (eTy ((tyInd "CState")))) (eTy ((tyInd "Transaction")))) (eRel 0)) (eConst "TxNone")))])]))))))].

  (** We assume that primitive data types are available *)
  Module Prim.
    Inductive Transaction := txNone.
    Definition plusInt64 := Z.add.
    Definition minusInt64 := Z.sub.
    Definition TxNone := txNone.
  End Prim.

  (** We import Acorn "standard library" definitions before unquoting. These definitions were also produced by the same printing procedure.  *)
  Import Prim.
  Import AcornProd.
  Import AcornMaybe.
  Import AcornBlockchain.

  (** Now, we add all data types, required for the translation of the [counter] to the global environment *)
  Definition gEnv := ((StdLib.Σ ++ AcornMaybe.Data ++ AcornBlockchain.Data ++ AcornProd.Data ++ CounterData)%list).

  (** We translate data types and the [counter] contract to MetaCoq and unquote them using the template moand *)
  Run TemplateProgram (translateData CounterData).
  Run TemplateProgram (translateDefs gEnv CounterFunctions).

  (** After that, we can interact with the shallow embedding in a usual way *)
  Print Msg.
  (* Inductive Msg : Set :=  Inc_coq : Z -> Msg | Dec_coq : Z -> Msg *)

  Print count.
(* count =
  fun _ x0 _ _ x3 =>
  match x3 with
   | @Nothing_coq _ => Pair_coq CState Transaction x0 TxNone
   | @Just_coq _ (Inc_coq x5) =>
      Pair_coq CState Transaction
       (CState_coq (plusInt64 (balance x0) x5) (owner x0)) TxNone
   | @Just_coq _ (Dec_coq x5) =>
      Pair_coq CState Transaction
       (CState_coq (minusInt64 (balance x0) x5) (owner x0)) TxNone
  end
     : ReceiveContext -> CState -> Caller
       -> nat -> Maybe Msg -> Pair CState Transaction *)

  Open Scope Z_scope.

  (** Using the shallow embedding, we can show a simple functional correctness property *)
  Lemma inc_correct init n i fin tx ctx amount caller :
    (* precondition *)
    balance init = n ->

    (* sending "increment" *)
    count ctx init caller amount (Just_coq _ (Inc_coq i)) = Pair_coq _ _ fin tx ->

    (* result *)
    balance fin = n + i.
  Proof.
    intros Hinit Hrun. inversion Hrun. subst. reflexivity.
  Qed.

End CounterContract.