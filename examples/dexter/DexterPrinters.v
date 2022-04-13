From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.QCTest Require Import ChainPrinters.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2Printers.
From ConCert.Examples.Dexter Require Import Dexter.
From QuickChick Require Import QuickChick.

Local Open Scope string_scope.

Instance showDexterExchangeParam : Show Dexter.exchange_param :=
{|
  show t := "exchange{"
            ++ "exchange_owner: " ++ show t.(exchange_owner) ++ sep
            ++ "exchange_token_id: " ++ show t.(exchange_token_id) ++ sep
            ++ "tokens_sold: " ++ show t.(tokens_sold)
            ++ "}"
|}.

Instance showDexterMsgMsg : Show Dexter.DexterMsg :=
{|
  show m := match m with
            | tokens_to_asset param => "token_to_asset " ++ show param
            | add_to_tokens_reserve tokenid => "add_to_tokens_reserve (token_id=" ++ show tokenid ++ ")"
            end
|}.

Instance showDexterMsg : Show Dexter.Msg :=
{|
  show m := show m
|}.

Instance showDexterState : Show Dexter.State :=
{|
  show t := "DexterState{"
            ++ "fa2_caddr: " ++ show t.(fa2_caddr) ++ sep
            ++ "ongoing_exchanges: " ++ show t.(ongoing_exchanges)
            ++ "}"
|}.

Instance showDexterSetup : Show Dexter.Setup :=
{|
  show t := "FA2TokenSetup{"
            ++ "fa2_caddr_: " ++ show t.(fa2_caddr_)
            ++ "}"
|}.

Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg <
    FA2Token.Msg,
    Dexter.Msg,
    FA2Token.Setup,
    Dexter.Setup >.
