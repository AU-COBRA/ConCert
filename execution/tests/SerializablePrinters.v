From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.QCTests Require Import ChainPrinters.
From QuickChick Require Import QuickChick.

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
Close Scope string_scope.
  
(** Tactic to automatically derive [Show] instances for [SerializedValue].
    Takes as input a list of types and will produce a show instance that tries to deserialize
    the serialized value to one of those types and print that value.
    The instance will attempt to deserialize to the types in the order that they are given.
    Prints an error message in case all deserializations failed. The tactic will fail if
    the types given do not have [Show] and [Serializable] instances.
*)
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

Instance showChainTraceSigT `{Show SerializedValue} : Show {to : ChainState & ChainTrace empty_state to} :=
{|
  show a := show (projT2 a)
|}.
