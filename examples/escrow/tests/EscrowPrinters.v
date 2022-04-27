(* Show instances for the Escrow types. Necessary for QuickChick testing. *)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Escrow Require Import Escrow.

Local Open Scope string_scope.

Derive Show for NextStep.
Derive Show for Msg.

Instance showEscrowSetup : Show Setup :=
{|
  show setup := "Setup{buyer: " ++ show setup.(setup_buyer) ++ "}"
|}.

Instance showEscrowState : Show Escrow.State :=
{|
  show s := "EscrowState{" ++
              "last_action: " ++ show s.(last_action) ++ sep ++
              "next_step: " ++ show s.(next_step) ++ sep ++
              "seller: " ++ show s.(seller) ++ sep ++
              "buyer: " ++ show s.(buyer) ++ sep ++
              "seller_withdrawable: " ++ show s.(seller_withdrawable) ++ sep ++
              "buyer_withdrawable: " ++ show s.(buyer_withdrawable) ++ "}"
|}.

Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg < Msg, Setup >.
