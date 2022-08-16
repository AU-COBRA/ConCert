From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.BAT Require Import BATCommon.
From ConCert.Examples.EIP20 Require Import EIP20TokenPrinters.

Local Open Scope string_scope.

Instance showTokenValue : Show TokenValue :=
{|
  show v := show v
|}.

Instance showMsg : Show BATCommon.Msg :=
{|
  show m := match m with
            | tokenMsg msg => show msg
            | create_tokens => "create_tokens"
            | finalize => "finalize"
            | refund => "refund"
            end
|}.

Instance showBATSetup : Show BATCommon.Setup :=
{|
  show setup := "Setup{" ++
    "initSupply: " ++ show setup.(_batFund) ++ sep ++
    "fundDeposit: " ++ show setup.(_fundDeposit) ++ sep ++
    "batFundDeposit: " ++ show setup.(_batFundDeposit) ++ sep ++
    "fundingStart: " ++ show setup.(_fundingStart) ++ sep ++
    "fundingEnd: " ++ show setup.(_fundingEnd) ++ sep ++
    "tokenExchangeRate: " ++ show setup.(_tokenExchangeRate) ++ sep ++
    "tokenCreationCap: " ++ show setup.(_tokenCreationCap) ++ sep ++
    "tokenCreationMin: " ++ show setup.(_tokenCreationMin) ++ "}"
|}.

Instance showBATState : Show BATCommon.State :=
{|
  show s := "State{" ++
    "initSupply: " ++ show s.(initSupply) ++ sep ++
    "token_state: " ++ show s.(token_state) ++ sep ++
    "isFinalized: " ++ show s.(isFinalized) ++ sep ++
    "fundDeposit: " ++ show s.(fundDeposit) ++ sep ++
    "batFundDeposit: " ++ show s.(batFundDeposit) ++ sep ++
    "fundingStart: " ++ show s.(fundingStart) ++ sep ++
    "fundingEnd: " ++ show s.(fundingEnd) ++ sep ++
    "tokenExchangeRate: " ++ show s.(tokenExchangeRate) ++ sep ++
    "tokenCreationCap: " ++ show s.(tokenCreationCap) ++ sep ++
    "tokenCreationMin: " ++ show s.(tokenCreationMin) ++ "}"
|}.

Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg < BATCommon.Msg, BATCommon.Setup >.
