From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From QuickChick Require Import QuickChick.
From ConCert.Execution.QCTests Require Import 
  ChainPrinters.
Local Open Scope string_scope.


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
Close Scope string_scope.

Instance showChainTraceSigT `{Show SerializedValue} : Show {to : ChainState & ChainTrace empty_state to} :=
{|
  show a := show (projT2 a)
|}.
