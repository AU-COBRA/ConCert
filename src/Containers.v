From Coq Require Import ProofIrrelevance.
From Containers Require Export OrderedType.
From Containers Require OrderedTypeEx.
From Containers Require SetListInstance.
From Containers Require MapListInstance.
From Containers Require MapFacts.
From Containers Require SetProperties.
From Coq Require Import List.
Import ListNotations.

Notation FSet := SetInterface.set.

Module FSet.
  Notation empty := SetInterface.empty.
  Notation add := SetInterface.add.
  Notation mem := SetInterface.mem.
  Notation remove := SetInterface.remove.
  Notation elements := SetInterface.elements.
  Notation size := SetInterface.cardinal.
  Notation of_list := SetProperties.of_list.

  (* TODO: We should really use setoids instead of this hacky crap... *)
  Proposition of_elements_eq
              {A : Type}
              {a_order : OrderedType A}
              (s : FSet A)
              : of_list (elements s) = s.
  Proof.
    destruct s as [l l_sorted].
    unfold SetProperties.of_list.
    Transparent SetInterface.empty.
    Transparent SetInterface.elements.
    unfold SetInterface.empty.
    unfold SetListInstance.SetList_FSet.
    unfold SetList.empty.
    unfold SetList.S.empty.
    simpl.
    induction l as [| hd tl IHl].
    - simpl.
      assert (SetList.S.empty_sort a_order = l_sorted) by apply proof_irrelevance.
      subst; reflexivity.
    - assert (decomposable: forall s1 s2 : SetList.set A, SetList.this s1 = SetList.this s2 -> s1 = s2).
      + intros [l1 l1_sorted] [l2 l2_sorted].
        simpl.
        intros l1_eq_l2.
        subst.
        replace l2_sorted with l1_sorted by apply proof_irrelevance.
        reflexivity.
      + apply decomposable.
        inversion l_sorted as [| a b tl_sorted hd_sorted]; subst.
        simpl in *.
        rewrite IHl with (l_sorted := tl_sorted).
        Transparent SetInterface.add.
        unfold SetInterface.add.
        unfold SetList.add.
        simpl.
        unfold SetList.S.add.
        destruct tl as [| hd' tl_tl].
        * reflexivity.
        * inversion hd_sorted as [|? ? hd_hd'_lt]; subst.
          destruct (OrderedType.compare_dec hd hd').
          -- reflexivity.
          -- order.
          -- order.
  Qed.
End FSet.

Notation FMap := MapInterface.dict.

Module FMap.
  Notation empty := MapInterface.empty.
  Arguments empty {_ _ _ _}.
  Notation add := MapInterface.add.
  Notation find := MapInterface.find.
  Notation mem := MapInterface.mem.
  Notation remove := MapInterface.remove.
  Notation elements := MapInterface.elements.
  Notation size := MapInterface.cardinal.
  Notation of_list := MapFacts.of_list.

  Proposition of_elements_eq
              {A B : Type}
              {_ : OrderedType A}
              (m : FMap A B)
              : of_list (elements m) = m.
  Proof.
    destruct m as [l l_sorted].
    unfold MapList.M.dict in *.
    unfold MapFacts.of_list.
    Transparent MapInterface.empty.
    Transparent MapInterface.elements.
    unfold MapInterface.empty.
    unfold MapListInstance.MapList_FMap.
    unfold MapList.empty.
    unfold MapList.M.empty.
    simpl.
    induction l as [| hd tl IHl].
    - simpl.
      assert (MapList.M.empty_sorted B = l_sorted) by apply proof_irrelevance.
      subst; reflexivity.
    - assert (decomposable: forall m1 m2 : MapList.dict A B, MapList.this m1 = MapList.this m2 -> m1 = m2).
      + intros [l1 l1_sorted] [l2 l2_sorted].
        simpl.
        intros l1_eq_l2.
        subst.
        replace l2_sorted with l1_sorted by apply proof_irrelevance.
        reflexivity.
      + apply decomposable.
        simpl.
        inversion l_sorted as [| a b tl_sorted hd_sorted].
        subst.
        rewrite IHl with (l_sorted := tl_sorted).
        Transparent MapInterface.add.
        unfold MapInterface.add.
        unfold MapList.add.
        simpl.
        unfold MapList.M.add.
        destruct hd as [k v].
        simpl.
        destruct tl as [| [k' v'] tl_tl].
        * reflexivity.
        * inversion hd_sorted as [|? ? k_k'_lt]; subst.
          unfold MapList.M.K.ltk in k_k'_lt.
          simpl in *.
          destruct (compare_dec k k').
          -- reflexivity.
          -- order.
          -- order.
  Qed.
End FMap.
