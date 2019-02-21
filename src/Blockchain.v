From Coq Require Import String.

Definition Address := nat.
Definition Amount := nat.
Definition BlockId := nat.
Definition BlockHash := string.
Definition Version := nat.

Inductive TxBody :=
| Empty : TxBody.

Record ContractCallDetails :=
  { from : Address ;
    to : Address ;
    amount : Amount
  }.

Record Contract (stateTy : Type) :=
  {
    getState : stateTy
  }.

Record StoredContract :=
  {
    stateTy : Type ;
    contract : Contract stateTy
  }.

Definition beq_address := Nat.eqb.