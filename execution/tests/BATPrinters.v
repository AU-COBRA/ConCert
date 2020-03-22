From ConCert Require Import Blockchain LocalBlockchain.
From ConCert Require Import BAT.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils EIP20TokenPrinters.
Require Import Strings.String.
From QuickChick Require Import QuickChick.

Local Open Scope string_scope.

Instance showBATMsg : Show Msg :=
{|
  show m := match m with
            | tokenMsg msg => show msg
            | create_tokens => "create_tokens"
            | finalize => "finalize"
            | refund => "refund" 
            end
|}.

Instance showBATSetup : Show Setup :=
{|
  show s := "BATSetup{"
            ++ "batFund: " ++ show s.(_batFund) ++ sep
            ++ "fundDeposit: " ++ show s.(_fundDeposit) ++ sep
            ++ "batFundDeposit: " ++ show s.(_batFundDeposit) ++ sep
            ++ "fundingStart: " ++ show s.(_fundingStart) ++ sep
            ++ "fundingEnd: " ++ show s.(_fundingEnd) ++ sep
            ++ "tokenExchangeRate: " ++ show s.(_tokenExchangeRate) ++ sep
            ++ "tokenCreationCap: " ++ show s.(_tokenCreationCap) ++ sep
            ++ "tokenCreationMin: " ++ show s.(_tokenCreationMin) ++ "}"
|}.

Instance showBATState : Show BAT.State :=
{|
  show s := "BATState{"
            ++ "Token" ++ show s.(token_state) ++ sep
            ++ "isFinalized: " ++ show s.(isFinalized) ++ sep 
            ++ "fundDeposit: " ++ show s.(fundDeposit) ++ sep
            ++ "batFundDeposit: " ++ show s.(batFundDeposit) ++ sep
            ++ "fundingStart: " ++ show s.(fundingStart) ++ sep
            ++ "fundingEnd: " ++ show s.(fundingEnd) ++ sep
            ++ "tokenExchangeRate: " ++ show s.(tokenExchangeRate) ++ sep
            ++ "tokenCreationCap: " ++ show s.(tokenCreationCap) ++ sep
            ++ "tokenCreationMin: " ++ show s.(tokenCreationMin) ++ "}"
|}.

Local Close Scope string_scope.