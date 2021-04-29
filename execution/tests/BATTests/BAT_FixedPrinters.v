From ConCert Require Import Blockchain.
From ConCert Require Import BAT_Fixed.
From QuickChick Require Import QuickChick.

From ConCert.Execution.QCTests Require Import
  TestUtils EIP20TokenPrinters.

Section BATFixedPrinters.
Context `{Show Address}.
Local Open Scope string_scope.

Existing Instance EIP20TokenPrinters.showMsg.
Existing Instance EIP20TokenPrinters.showTokenState.

Instance showTokenValue : Show TokenValue :=
{|
  show v := show v
|}.

Instance showMsg : Show BAT_Fixed.Msg :=
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
  show setup := "Setup{" ++
    "batFund: " ++ show setup.(_batFund) ++ sep ++
    "fundDeposit: " ++ show setup.(_fundDeposit) ++ sep ++
    "batFundDeposit: " ++ show setup.(_batFundDeposit) ++ sep ++
    "fundingStart: " ++ show setup.(_fundingStart) ++ sep ++
    "fundingEnd: " ++ show setup.(_fundingEnd) ++ sep ++
    "tokenExchangeRate: " ++ show setup.(_tokenExchangeRate) ++ sep ++
    "tokenCreationCap: " ++ show setup.(_tokenCreationCap) ++ sep ++
    "tokenCreationMin: " ++ show setup.(_tokenCreationMin) ++ "}"
|}.

Instance showBATState : Show BAT_Fixed.State :=
{|
  show s := "State{" ++
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

End BATFixedPrinters.
