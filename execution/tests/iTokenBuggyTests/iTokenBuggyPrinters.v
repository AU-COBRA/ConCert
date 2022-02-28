From ConCert Require Import Blockchain Serializable.
From ConCert Require Import iTokenBuggy.
From ConCert.Execution.QCTests Require Import TestUtils SerializablePrinters.
From QuickChick Require Import QuickChick.


Local Open Scope string_scope.
Instance showMsg : Show Msg :=
{|
  show m := match m with
            | transfer_from from to amount =>
              "transfer_from " ++ show from ++ " " ++ show to ++ " " ++ show amount
            | approve delegate amount => "approve " ++ show delegate ++ " " ++ show amount
            | mint amount => "mint " ++ show amount
            | burn amount => "burn " ++ show amount
            end
|}.

Instance showTokenSetup : Show Setup :=
{|
  show setup := "Setup{owner: " ++ show setup.(owner) ++ sep ++ "init_amount: " ++ show setup.(init_amount) ++ "}"
|}.

Instance showTokenState : Show iTokenBuggy.State :=
{|
  show s := "State{total_supply: " ++ show s.(total_supply) ++ sep
               ++ "balances: " ++ show s.(balances) ++ sep
               ++ "allowances: " ++ show s.(allowances) ++ "}"
|}.

Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg < Msg, Setup >.
