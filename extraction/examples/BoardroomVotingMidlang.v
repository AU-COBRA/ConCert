From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import LPretty Certified.
From ConCert.Extraction Require Import Counter.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Congress.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Definition foo (m : FMap nat nat) := FMap.find 0 m.

Definition testaa : TemplateMonad unit :=
  x <- tmQuoteConstant "foo" true ;;
  tmPrint x.

Run TemplateProgram testaa.

(*
bar =
tLambda (nNamed "m") (tConst "ConCert.Extraction.Examples.BoardroomVotingMidlang.Map" [])
  (tApp (tConst "ConCert.Extraction.Examples.BoardroomVotingMidlang.find" [])
     [tConstruct
        {| Ast.BasicTC.inductive_mind := "Coq.Init.Datatypes.nat"; Ast.BasicTC.inductive_ind := 0 |}
        0 []; tRel 0])
     : term
*)
