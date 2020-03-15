From ConCert Require Import Blockchain LocalBlockchain Congress EIP20Token.

From ConCert Require Import Serializable.
From QuickChick Require Import QuickChick. Import QcNotation.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters EIP20TokenPrinters.

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

Local Open Scope string_scope.
Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.



(* Currently we hack it to always deserialize to Msg types - only works for Congress! TODO: fix *)
Instance showSerializedValue {ty : Type} `{Serializable ty} `{Show ty} : Show SerializedValue := 
{|
  show v :=
    match @deserialize EIP20Token.Msg _ v with
    | Some v => show v
		| None =>
		match @deserialize Congress.Msg _ v with
		| Some v => show v
		| None => "<FAILED DESERIALIZATION>" 
		end
		end
  (* ++ show (ser_value_type v) ++ sep *)
  (* ++ string_of_interp_type (ser_value_type v) (ser_value v) ++ "}"  *)
|}.

Close Scope string_scope.