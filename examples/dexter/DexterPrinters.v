From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Dexter Require Import Dexter.
From ConCert.Examples.EIP20 Require Import EIP20Token.
From ConCert.Examples.EIP20 Require Import EIP20TokenPrinters.

Local Open Scope string_scope.

Instance showDexterExchangeParam : Show Dexter.exchange_param :=
{|
  show t := "exchange{"
            ++ "exchange_owner: " ++ show t.(exchange_owner) ++ sep
            ++ "tokens_sold: " ++ show t.(tokens_sold)
            ++ "}"
|}.

Instance showDexterMsg : Show Dexter.Msg :=
{|
  show m := match m with
            | tokens_to_asset param => "token_to_asset " ++ show param
            | add_to_tokens_reserve => "add_to_tokens_reserve"
            end
|}.

Instance showDexterState : Show Dexter.State :=
{|
  show t := "DexterState{"
            ++ "token_caddr: " ++ show t.(token_caddr) ++ sep
            ++ "token_pool: " ++ show t.(token_pool) ++ sep
            ++ "price_history: " ++ show t.(price_history)
            ++ "}"
|}.

Instance showDexterSetup : Show Dexter.Setup :=
{|
  show t := "DexterSetup{"
            ++ "token_caddr_: " ++ show t.(token_caddr_) ++ sep
            ++ "token_pool_: " ++ show t.(token_pool_)
            ++ "}"
|}.

Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg <
    Dexter.Msg,
    Dexter.Setup,
    EIP20Token.Msg,
    EIP20Token.Setup
  >.
