Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import Containers.
From ConCert Require Import BAT.
Require Import Extras.

From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters SerializablePrinters BATPrinters BATGens TraceGens.

(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List Int.
Import BoundedN.Stdpp.
Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.

(* -------------------------- Tests of the BAT Implementation -------------------------- *)

Definition bat_setup : BAT.Setup := {|
  _batFund						:= 100%N;
  _fundDeposit 				:= BoundedN.of_Z_const AddrSize 42%Z;
  _batFundDeposit 		:= BoundedN.of_Z_const AddrSize 43%Z;
  _fundingStart	  		:= 0;
  _fundingEnd					:= 10;
  _tokenExchangeRate  := 1; (* one token corresponds to one ConCert currency *)
  _tokenCreationCap 	:= 500%N;
  _tokenCreationMin 	:= 300%N;
|}.

Definition deploy_bat : @ActionBody Base := create_deployment 0 BAT.contract bat_setup.

Let bat_caddr := BoundedN.of_Z_const AddrSize 128%Z.

Definition bat_chain :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_bat
  ]).

(* Sample (gBATAction bat_chain bat_caddr). *)