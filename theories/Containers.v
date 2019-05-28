From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From stdpp Require gmap.
From SmartContracts Require Import Monads.
From SmartContracts Require Import BoundedN.
From SmartContracts Require Import Automation.
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
  Notation union := stdpp.base.union.
  Notation alter := stdpp.base.alter.
  Notation partial_alter := stdpp.base.partial_alter.

  Definition values {K V : Type} `{countable.Countable K} (m : FMap K V) : list V :=
    map snd (elements m).

  Section Theories.
    Context {K V : Type} `{countable.Countable K}.

    Proposition of_elements_eq (m : FMap K V) :
      of_list (elements m) = m.
    Proof. apply fin_maps.list_to_map_to_list. Qed.

    Lemma find_union_None (m1 m2 : FMap K V) (k : K) :
      find k m1 = None ->
      find k m2 = None ->
      find k (union m1 m2) = None.
    Proof.
      intros find1 find2.
      apply fin_maps.lookup_union_None; auto.
    Qed.

    Lemma find_union_Some_l (m1 m2 : FMap K V) (k : K) (v : V) :
      find k m1 = Some v ->
      find k (union m1 m2) = Some v.
    Proof. apply fin_maps.lookup_union_Some_l. Qed.

    Lemma find_add (m : FMap K V) (k : K) (v : V) :
      find k (add k v m) = Some v.
    Proof. apply fin_maps.lookup_insert. Qed.

    Lemma find_add_ne (m : FMap K V) (k k' : K) (v : V) :
      k <> k' -> find k' (add k v m) = find k' m.
    Proof. apply fin_maps.lookup_insert_ne. Qed.

    Lemma find_partial_alter (m : FMap K V) f k :
      find k (partial_alter f k m) = f (find k m).
    Proof. apply fin_maps.lookup_partial_alter. Qed.

    Lemma find_partial_alter_ne (m : FMap K V) f k k' :
      k <> k' ->
      find k' (partial_alter f k m) = find k' m.
    Proof. apply fin_maps.lookup_partial_alter_ne. Qed.

    Lemma find_empty k :
      FMap.find k (FMap.empty : FMap K V) = None.
    Proof. apply fin_maps.lookup_empty. Qed.

    Lemma elements_add (m : FMap K V) k v :
      find k m = None ->
      Permutation (elements (add k v m)) ((k, v) :: elements m).
    Proof. apply fin_maps.map_to_list_insert. Qed.

    Lemma elements_empty : (elements empty : list (K * V)) = [].
    Proof. now rewrite fin_maps.map_to_list_empty. Qed.

    Lemma elements_add_empty (k : K) (v : V) :
      FMap.elements (FMap.add k v FMap.empty) = [(k, v)].
    Proof. now rewrite fin_maps.insert_empty, fin_maps.map_to_list_singleton. Qed.

    Lemma add_remove (m : FMap K V) k v :
      add k v (remove k m) = add k v m.
    Proof. apply fin_maps.insert_delete. Qed.

    Lemma remove_add (m : FMap K V) k v :
      find k m = None ->
      remove k (add k v m) = m.
    Proof. apply fin_maps.delete_insert. Qed.

    Lemma find_remove (m : FMap K V) k :
      find k (remove k m) = None.
    Proof. apply fin_maps.lookup_delete. Qed.

    Lemma add_commute (m : FMap K V) (k k' : K) (v v' : V) :
      k <> k' ->
      FMap.add k v (FMap.add k' v' m) = FMap.add k' v' (FMap.add k v m).
    Proof. apply fin_maps.insert_commute. Qed.

    Lemma add_id (m : FMap K V) k v :
      find k m = Some v ->
      add k v m = m.
    Proof. apply fin_maps.insert_id. Qed.
  End Theories.
End FMap.

Hint Resolve
     FMap.find_union_None
     FMap.find_union_Some_l
     FMap.find_add
     FMap.find_add_ne : core.

Instance empty_set_eq_dec : stdpp.base.EqDecision Empty_set.
Proof. decidable.solve_decision. Defined.
Program Instance empty_set_countable : countable.Countable Empty_set :=
  {| countable.encode e := 1%positive; countable.decode d := None; |}.
Solve Obligations with contradiction.
