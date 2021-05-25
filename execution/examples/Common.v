(** * Definitions shared among the examples *)

Require Import Containers.
From ConCert.Execution Require Import Blockchain.

(** A type of  finite maps (dictionaries) with addresses as keys.
Basically, it's just a specilisation of [FMap] to [Address] as keys.
This definitions is more extraction-friendly. *)

Module AddressMap.

  Definition AddrMap `{ChainBase} := FMap Address.

  Definition find `{ChainBase} {V : Type} (addr : Address) (m : AddrMap V) : option V :=
    FMap.find addr m.

  Definition add  `{ChainBase} {V : Type} (addr : Address) (val : V) (m : AddrMap V) : AddrMap V :=
    FMap.add addr val m.

  Definition empty  `{ChainBase} {V : Type} : AddrMap V := FMap.empty.

End AddressMap.

(** The specialised version is convertible to [FMap.find] after resolving the instances *)
Lemma AddressMap_find_convertible  `{ChainBase} {V : Type} :
  AddressMap.find (V:=V) = FMap.find.
Proof. reflexivity. Qed.

Lemma AddressMap_add_convertible  `{ChainBase} {V : Type} :
  AddressMap.add (V:=V) = FMap.add.
Proof. reflexivity. Qed.
