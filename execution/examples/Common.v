(** * Definitions shared among the examples *)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Extras.
From Coq Require Import ZArith.

(** A type of  finite maps (dictionaries) with addresses as keys.
Basically, it's just a specilisation of [FMap] to [Address] as keys.
This definitions is more extraction-friendly. *)

Module AddressMap.

  Definition AddrMap `{ChainBase} := FMap Address.

  Definition find `{ChainBase} {V : Type} (addr : Address) (m : AddrMap V) : option V :=
    FMap.find addr m.

  Definition add  `{ChainBase} {V : Type} (addr : Address) (val : V) (m : AddrMap V) : AddrMap V :=
    FMap.add addr val m.

  Definition values  `{ChainBase} {V : Type} (m : AddrMap V) : list V :=
    FMap.values m.

  Definition keys  `{ChainBase} {V : Type} (m : AddrMap V) : list Address :=
    FMap.keys m.
      
  Definition of_list  `{ChainBase} {V : Type} (l : list (Address * V)) : AddrMap V :=
    FMap.of_list l.

  Definition empty  `{ChainBase} {V : Type} : AddrMap V := FMap.empty.

End AddressMap.

(** The specialised version is convertible to [FMap.find] after resolving the instances *)
Lemma AddressMap_find_convertible  `{ChainBase} {V : Type} :
  AddressMap.find (V:=V) = FMap.find.
Proof. reflexivity. Qed.


Open Scope N_scope.
Definition maybe (n : N) : option N := if n =? 0 then None else Some n.

Lemma maybe_cases : forall n,
  (maybe n = None /\ n = 0) \/ (maybe n = Some n /\ n > 0).
Proof.
  destruct n.
  - auto.
  - now right.
Qed.

Lemma maybe_sub_add : forall n value,
  value <= n ->
  (maybe (with_default 0 (maybe (n - value)) + value) = None /\ n = 0) \/
  maybe (with_default 0 (maybe (n - value)) + value) = Some n.
Proof.
  intros.
  specialize (maybe_cases (n - value)) as [[-> n_eq_value] | [-> _]]; cbn.
  - rewrite N.sub_0_le in n_eq_value.
    erewrite (N.le_antisymm _ n) by eassumption.
    now specialize (maybe_cases) as [[-> ?H] | [-> _]]; cbn.
  - rewrite N.sub_add by auto.
    now specialize (maybe_cases) as [[-> ?H] | [-> _]]; cbn.
Qed.
Close Scope N_scope.
