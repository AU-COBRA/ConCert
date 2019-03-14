From Coq Require Import ProofIrrelevance.
From Coq Require Import ZArith.
From stdpp Require Import gmap.
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

(* The default list countable instance is exponential. For instance,
   1000%positive takes around 10 bits to describe, but
   countable.encode [1000%positive] returns a positive taking around
   1000 bits to describe. This is because it writes everything out
   in unary. Here is a more efficient implementation that works by
   duplicating the bits of each element and separating them by
   1~0. *)
Remove Hints countable.list_countable : typeclass_instances.
Section ListCountable.
  Context `{countable.Countable A}.
  Open Scope positive.

  Fixpoint encode_single (p acc : positive) : positive :=
    match p with
    | 1 => acc
    | p'~0 => encode_single p' (acc~0~0)
    | p'~1 => encode_single p' (acc~1~1)
    end.

  Fixpoint encode_list' (l : list A) (acc : positive) : positive :=
    match l with
    | [] => acc
    | hd :: tl => encode_list' tl (encode_single (encode hd) (acc~1~0))
    end.

  Definition encode_list l := encode_list' l 1.

  Fixpoint decode_list'
           (p : positive)
           (acc_l : list A)
           (acc_elm : positive)
    : option (list A) :=
      match p with
      | 1 => Some acc_l
      | p'~0~0 => decode_list' p' acc_l (acc_elm~0)
      | p'~1~1 => decode_list' p' acc_l (acc_elm~1)
      | p'~1~0 => do elm <- countable.decode acc_elm;
                  decode_list' p' (elm :: acc_l) 1
      | _ => None
      end.

  Definition decode_list (p : positive) : option (list A) :=
    decode_list' p [] 1.

  Lemma encode_single_app (p acc : positive) :
    encode_single p acc = acc ++ encode_single p 1.
  Proof.
    generalize dependent acc.
    induction p.
    - intros acc.
      simpl.
      rewrite IHp.
      rewrite (IHp 7).
      rewrite Papp_assoc.
      reflexivity.
    - intros acc.
      simpl.
      rewrite IHp.
      rewrite (IHp 4).
      rewrite Papp_assoc.
      reflexivity.
    - intros acc.
      reflexivity.
  Qed.

  Lemma encode_list'_app (l : list A) (acc : positive) :
    encode_list' l acc = acc ++ encode_list' l 1.
  Proof.
    generalize dependent acc.
    induction l as [| hd tl IHl].
    - intros acc; reflexivity.
    - intros acc.
      simpl.
      rewrite IHl.
      rewrite (IHl (encode_single _ _)).
      rewrite Papp_assoc.
      rewrite (encode_single_app _ 6).
      rewrite Papp_assoc.
      simpl.
      rewrite <- encode_single_app.
      reflexivity.
  Qed.

  Lemma decode_list'_single (p prefix : positive) (l : list A) :
    decode_list' (prefix ++ encode_single p 1) l 1 = decode_list' prefix l p.
  Proof.
    generalize dependent prefix.
    induction p.
    - intros.
      simpl.
      rewrite encode_single_app.
      rewrite Papp_assoc.
      rewrite IHp.
      reflexivity.
    - intros.
      simpl.
      rewrite encode_single_app.
      rewrite Papp_assoc.
      rewrite IHp.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma decode_list'_list (prefix : positive) (l acc : list A) :
    decode_list' (prefix ++ encode_list' l 1) acc 1 = decode_list' prefix (l ++ acc) 1.
  Proof.
    generalize dependent prefix.
    generalize dependent acc.
    induction l as [| hd tl IHl].
    - reflexivity.
    - intros acc prefix.
      simpl.
      rewrite encode_list'_app.
      rewrite Papp_assoc.
      rewrite IHl.
      rewrite encode_single_app.
      rewrite Papp_assoc.
      rewrite decode_list'_single.
      simpl.
      rewrite decode_encode.
      reflexivity.
  Qed.

  Global Program Instance list_countable : countable.Countable (list A) :=
    {| encode := encode_list; decode := decode_list; |}.
  Next Obligation.
    intros l.
    unfold encode_list, decode_list.
    replace (encode_list' _ _) with (1 ++ encode_list' l 1) by apply Papp_1_l.
    rewrite decode_list'_list.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.
End ListCountable.
