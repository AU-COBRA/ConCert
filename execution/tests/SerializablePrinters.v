From ConCert Require Import Blockchain LocalBlockchain.
From ConCert Require Import Serializable.
From QuickChick Require Import QuickChick.
From ConCert.Execution.QCTests Require Import CongressPrinters EIP20TokenPrinters FA2Printers TestContracts DexterPrinters.

Local Open Scope string_scope.

(* Currently we hack it to always deserialize to some known Msg types *)

Instance showSerializedValue : Show SerializedValue :=
{|
  show v := match @deserialize FA2Token.Msg _ v with
    | Some v => show v
    | None =>
    match @deserialize Dexter.Msg _ v with
    | Some v => show v
    | None =>
    match @deserialize TestContracts.ClientMsg _ v with
    | Some v => show v
    | None =>
    match @deserialize TestContracts.TransferHookMsg _ v with
    | Some v => show v
    | None =>
    match @deserialize EIP20Token.Msg _ v with
    | Some v => show v
    | None =>
    match @deserialize Congress.Msg _ v with
    | Some v => show v
    | None => "<FAILED DESERIALIZATION>"
    end
    end
    end
    end
    end
    end
|}.
Close Scope string_scope.
