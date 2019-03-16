From Coq Require Import ProofIrrelevance.
From Coq Require Import ZArith.
From stdpp Require gmap.
From Coq Require Import List.
From SmartContracts Require Import Monads.
Import ListNotations.

Notation FMap := gmap.gmap.

Module FMap.
  Generalizable All Variables.
  Notation empty := stdpp.base.empty.
  Notation add := stdpp.base.insert.
  Notation find := stdpp.base.lookup.
  Definition mem `{base.Lookup K V M} (i : K) (m : M) :=
    match base.lookup i m with
    | Some _ => true
    | None => false
    end.

  Notation remove := stdpp.base.delete.
  Notation elements := fin_maps.map_to_list.
  Notation size := stdpp.base.size.
  Notation of_list := fin_maps.list_to_map.

  Proposition of_elements_eq
              {A B : Type}
              `{countable.Countable A}
              (m : FMap A B)
              : of_list (elements m) = m.
  Proof.
    apply fin_maps.list_to_map_to_list.
  Qed.
End FMap.

Instance empty_set_eq_dec : stdpp.base.EqDecision Empty_set.
Proof. decidable.solve_decision. Defined.
Program Instance empty_set_countable : countable.Countable Empty_set :=
  {| countable.encode e := 1%positive; countable.decode d := None; |}.
Solve Obligations with contradiction.
