(* From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface. *)
(* From ConCert Require Import Serializable.
From ConCert Require Import LocalBlockchainTests.
(* From Coq Require Import Morphisms. *)
From ConCert Require Import Extras.
From ConCert Require Import Containers.
From ConCert Require Import BoundedN.
Global Set Warnings "-extraction-logical-axiom".
Require Import ZArith Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters SerializablePrinters TraceGens FA2Printers TestContracts.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Import ListNotations.
Import RecordSetNotations.
(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
Close Scope address_scope. *)
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
Import MonadNotation. 
(* Open Scope monad_scope. *)

(* From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters SerializablePrinters TraceGens FA2Printers TestContracts. *)

Definition a : G nat := 
  returnGen 1.

Definition b : G nat := 
	v <- a ;;
	returnGen v.
	
Sample b.
