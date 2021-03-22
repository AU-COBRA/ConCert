Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import Containers.
From ConCert Require Import BAT.
From ConCert Require Import ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters BATPrinters BATGens TraceGens.

From Coq Require Import List.
Import ListNotations.
Import BoundedN.Stdpp.
Import LocalBlockchain.

(* -------------------------- Tests of the BAT Implementation -------------------------- *)

Existing Instance showBATState.

Definition ethFund : Address := BoundedN.of_Z_const AddrSize 16%Z.

Definition bat_setup := BAT.build_setup (20%N) ethFund creator 0 5 (3%N) (50%N) (40%N).
Definition deploy_bat := create_deployment 0 BAT.contract bat_setup.

Let contract_base_addr := BoundedN.of_Z_const AddrSize 128%Z.

(* In the initial chain we transfer some assets to a few accounts, just to make the addresses
   present in the chain state. The amount transferred is irrelevant. *)
Definition token_cb :=
  ResultMonad.unpack_result (TraceGens.add_block (lcb_initial AddrSize)
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 7);
    build_act creator (act_transfer person_3 6);
    build_act creator (act_transfer person_4 10);
    build_act creator deploy_bat
  ]).

Module TestInfo <: BATGensInfo.
  Definition contract_addr := contract_base_addr.
  Definition gAccount (c : Chain) := elems [person_1; person_2; person_3; person_4; person_5].
End TestInfo.
Module MG := BATGens TestInfo. Import MG.

Definition gTokenChain max_acts_per_block token_cb max_length := 
  let act_depth := 1 in 
  gChain token_cb
    (fun env act_depth => gBATAction env) max_length act_depth max_acts_per_block.
Sample (gTokenChain 2 token_cb 7).


