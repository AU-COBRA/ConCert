From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2Printers.
From ConCert.Examples.ExchangeBuggy Require Import ExchangeBuggy.

Local Open Scope string_scope.

Instance showExchangeExchangeParam : Show ExchangeBuggy.exchange_param :=
{|
  show t := "exchange{"
          ++ "exchange_owner: " ++ show t.(exchange_owner) ++ sep
          ++ "exchange_token_id: " ++ show t.(exchange_token_id) ++ sep
          ++ "tokens_sold: " ++ show t.(tokens_sold)
          ++ "}"
|}.

Instance showExchangeMsgMsg : Show ExchangeBuggy.ExchangeMsg :=
{|
  show m := match m with
            | tokens_to_asset param => "token_to_asset " ++ show param
            | add_to_tokens_reserve tokenid => "add_to_tokens_reserve (token_id=" ++ show tokenid ++ ")"
            end
|}.

Instance showExchangeMsg : Show ExchangeBuggy.Msg :=
{|
  show m := show m
|}.

Instance showExchangeState : Show ExchangeBuggy.State :=
{|
  show t := "ExchangeState{"
          ++ "fa2_caddr: " ++ show t.(fa2_caddr) ++ sep
          ++ "ongoing_exchanges: " ++ show t.(ongoing_exchanges)
          ++ "}"
|}.

Instance showExchangeSetup : Show ExchangeBuggy.Setup :=
{|
  show t := "ExchangeSetup{"
          ++ "fa2_caddr_: " ++ show t.(fa2_caddr_)
          ++ "}"
|}.

Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg <
    FA2Token.Msg,
    ExchangeBuggy.Msg,
    FA2LegacyInterface.fa2_token_sender,
    FA2Token.Setup,
    ExchangeBuggy.Setup,
    unit >.
