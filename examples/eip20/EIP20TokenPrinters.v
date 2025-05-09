From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
#[warnings="-notation-incompatible-prefix"]
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.EIP20 Require Import EIP20Token.

Local Open Scope string_scope.

#[export]
Instance showTokenValue : Show TokenValue :=
{|
  show v := show v
|}.

#[export]
Instance showMsg : Show Msg :=
{|
  show m :=
    match m with
    | transfer to amount =>
        "transfer " ++ show to ++ " " ++ show amount
    | transfer_from from to amount =>
        "transfer_from " ++ show from ++ " " ++ show to ++ " " ++ show amount
    | approve delegate amount =>
        "approve " ++ show delegate ++ " " ++ show amount
    end
|}.

#[export]
Instance showTokenSetup : Show Setup :=
{|
  show setup := "Setup{owner: "
              ++ show setup.(owner)
              ++ sep
              ++ "init_amount: "
              ++ show setup.(init_amount)
              ++ "}"
|}.

#[export]
Instance showTokenState : Show EIP20Token.State :=
{|
  show s := "State{total_supply: " ++ show s.(total_supply) ++ sep
               ++ "balances: " ++ show s.(balances) ++ sep
               ++ "allowances: " ++ show s.(allowances) ++ "}"
|}.

#[export]
Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg < Msg, Setup >.
