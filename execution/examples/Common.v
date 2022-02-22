(** * Definitions shared among the examples *)

From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Extras.
From Coq Require Import ZArith.

(** A type of  finite maps (dictionaries) with addresses as keys.
Basically, it's just a specilisation of [FMap] to [Address] as keys.
This definitions is more extraction-friendly. *)

Module AddressMap.

  Notation AddrMap := (FMap Address).

  (* Definition AddrMap `{ChainBase} := FMap Address. *)

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

  Definition update `{ChainBase} {V : Type} (addr : Address) (val : option V) (m : AddrMap V) : AddrMap V :=
    FMap.update addr val m.

End AddressMap.

(** The specialised version is convertible to [FMap.find] after resolving the instances *)
Lemma AddressMap_find_convertible  `{ChainBase} {V : Type} :
  AddressMap.find (V:=V) = FMap.find.
Proof. reflexivity. Qed.

Lemma AddressMap_add_convertible  `{ChainBase} {V : Type} :
  AddressMap.add (V:=V) = FMap.add.
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


Definition throwIf (cond : bool) := if cond then None else Some tt.

Ltac destruct_throw_if H :=
  match type of H with
  | throwIf _ = None =>
    let G := fresh "G" in
      unfold throwIf in H;
      destruct_match eqn:G in H; try congruence;
      clear H;
      rename G into H
  | throwIf _ = Some ?u =>
    let G := fresh "G" in
      unfold throwIf in H;
      destruct_match eqn:G in H; try congruence;
      clear H u;
      rename G into H
  end.

Ltac destruct_match_some m H :=
  let a := fresh "H" in
    destruct m eqn:a in H;
    try setoid_rewrite a;
    cbn in H; cbn;
    try congruence.

Tactic Notation "destruct_match_some" constr(m) "in" hyp(H) :=
  destruct_match_some m H.

Ltac contract_simpl_step receive init :=
  match goal with
  | H : context[receive] |- _ => try (unfold receive in H); cbn in H
  | |- context[receive] => try (unfold receive); cbn
  | H : context[init] |- _ => try (unfold init in H); cbn in H
  | |- context[init] => try (unfold init); cbn
  | H : context[Blockchain.receive] |- _ => unfold Blockchain.receive in H; cbn in H
  | |- context[Blockchain.receive] => unfold Blockchain.receive; cbn
  | H : context[Blockchain.init] |- _ => unfold Blockchain.init in H; cbn in H
  | |- context[Blockchain.init] => unfold Blockchain.init; cbn
  | p : (_ * list ActionBody) |- _ => destruct p
  | H : throwIf _ = None |- _ => destruct_throw_if H
  | H : throwIf _ = Some ?u |- _ => destruct_throw_if H
  | H : Some _ = Some _ |- _ =>
      inversion H; clear H; subst
  | H : _ match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
      destruct_match_some m in H
  | H : match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
      destruct_match_some m in H
  | H : _ (if ?m then None else _) = Some _ |- _ =>
      destruct_match_some m in H
  | H : _ (if ?m then _ else None) = Some _ |- _ =>
      destruct_match_some m in H
  | H : (if ?m then None else _) = Some _ |- _ =>
      destruct_match_some m in H
  | H : (if ?m then _ else None) = Some _ |- _ =>
      destruct_match_some m in H
  | |- context [_ (match ?m with Some _ => _ | None => _ end) = Some _] =>
      destruct m eqn:?H
  | |- context [match ?m with Some _ => _ | None => _ end = Some _] =>
      destruct m eqn:?H
  end.

Tactic Notation "contract_simpl" constr(r) constr(i) := repeat contract_simpl_step r i.
