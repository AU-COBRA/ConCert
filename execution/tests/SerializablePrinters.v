From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From QuickChick Require Import QuickChick.
From ConCert.Execution.QCTests Require Import 
  ChainPrinters CongressPrinters EIP20TokenPrinters FA2Printers TestContracts 
  DexterPrinters EscrowPrinters iTokenBuggyPrinters BATPrinters.
Local Open Scope string_scope.

Existing Instance EIP20TokenPrinters.showMsg.
Existing Instance CongressPrinters.showMsg.
Existing Instance showFA2TokenMsg.
Existing Instance showDexterMsg.
Existing Instance showDexterMsgMsg.
Existing Instance showFA2ClientContractMsg.
Existing Instance showTransferHookMsg.
Existing Instance iTokenBuggyPrinters.showMsg.
Existing Instance BATPrinters.showMsg.
(* Existing Instance showEscrowMsg. *)
(* Currently we hack it to always deserialize to some known Msg types *)

Ltac make_show ts :=
  match ts with
  | (?t, ?tail) =>
    let rest := make_show tail in
    constr:(
      fun (v : SerializedValue) =>
        match @deserialize t _ v with
        | Some v => show v
        | None => rest v
        end)
  | tt => constr:(fun (v : SerializedValue) => "<FAILED DESERIALIZATION>")
  end.

Notation "'Derive' 'Show' 'Msg' < c0 , .. , cn >" :=
  (let pairs := pair c0 .. (pair cn tt) .. in
   ltac:(
     match goal with
     | [pairs := ?x |- _] => 
      let s := make_show x in
      let s' := eval cbn beta in s in
        exact {| show := s' |}
     end))
    (at level 0, c0, cn at level 9, only parsing).

Global Instance showSerializedValue : Show SerializedValue :=
  Derive Show Msg <
    FA2Token.Msg,
    Dexter.Msg,
    TestContracts.ClientMsg,
    TestContracts.TransferHookMsg,
    EIP20Token.Msg,
    BATCommon.Msg,
    Escrow.Msg,
    iTokenBuggy.Msg,
    Congress.Msg >.
Close Scope string_scope.

Instance showChainTraceSigT : Show {to : ChainState & ChainTrace empty_state to} :=
{|
  show a := show (projT2 a)
|}.
