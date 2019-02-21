From Coq Require Import String.
From Coq Require OrderedTypeEx.

Definition address := nat.
Definition amount := nat.
Definition block_id := nat.
Definition block_hash := string.
Definition version := nat.

Inductive tx_body :=
| Empty : tx_body.

Record contract_call_details :=
  { from : address ;
    to : address ;
    value : amount
  }.

Module Address.
  Definition eqb := Nat.eqb.
  Module as_modern_OT := PeanoNat.Nat.
  Module as_old_OT := OrderedTypeEx.Nat_as_OT.
End Address.