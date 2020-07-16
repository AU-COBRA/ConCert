From ConCert Require Import Blockchain LocalBlockchain.
From ConCert Require Import EIP20Token.
From ConCert.Execution.QCTests Require Import TestUtils ChainPrinters.
Require Import Strings.String.
From QuickChick Require Import QuickChick.

Local Open Scope string_scope.

Instance showTokenValue : Show TokenValue :=
{|
  show v := show v
|}.

Instance showMsg : Show Msg :=
{|
  show m := match m with
            | transfer to amount => "transfer " ++ show to ++ " " ++ show amount
            | transfer_from from to amount =>
              "transfer_from " ++ show from ++ " " ++ show to ++ " " ++ show amount
            | approve delegate amount => "approve " ++ show delegate ++ " " ++ show amount
            end
|}.

Instance showTokenSetup : Show Setup :=
{|
  show setup := "Setup{owner: " ++ show setup.(owner) ++ sep ++ "init_amount: " ++ show setup.(init_amount) ++ "}"
|}.

Instance showTokenState : Show EIP20Token.State :=
{|
  show s := "State{total_supply: " ++ show s.(total_supply) ++ sep
               ++ "balances: " ++ show s.(balances) ++ sep
               ++ "allowances: " ++ show s.(allowances) ++ "}"
|}.
