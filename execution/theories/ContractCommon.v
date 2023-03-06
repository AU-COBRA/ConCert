(** * Definitions shared among the examples *)

From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith_base.

(** A type of finite maps (dictionaries) with addresses as keys.
Basically, it's just a specilization of [FMap] to [Address] as keys.
This definition is more extraction-friendly. *)

Module AddressMap.

  Notation AddrMap := (FMap Address).

  (* Definition AddrMap `{ChainBase} := FMap Address. *)

  Definition find `{ChainBase} {V : Type} (addr : Address) (m : AddrMap V) : option V :=
    FMap.find addr m.

  Definition add `{ChainBase} {V : Type} (addr : Address) (val : V) (m : AddrMap V) : AddrMap V :=
    FMap.add addr val m.

  Definition values `{ChainBase} {V : Type} (m : AddrMap V) : list V :=
    FMap.values m.

  Definition keys `{ChainBase} {V : Type} (m : AddrMap V) : list Address :=
    FMap.keys m.

  Definition of_list `{ChainBase} {V : Type} (l : list (Address * V)) : AddrMap V :=
    FMap.of_list l.

  Definition empty `{ChainBase} {V : Type} : AddrMap V :=
    FMap.empty.

  Definition update `{ChainBase} {V : Type} (addr : Address) (val : option V) (m : AddrMap V) : AddrMap V :=
    FMap.update addr val m.

End AddressMap.

(** The specialized version is convertible to [FMap.find] after resolving the instances *)
Lemma AddressMap_find_convertible `{ChainBase} {V : Type} :
  AddressMap.find (V := V) = FMap.find.
Proof. reflexivity. Qed.

Lemma AddressMap_add_convertible `{ChainBase} {V : Type} :
  AddressMap.add (V := V) = FMap.add.
Proof. reflexivity. Qed.

Section Utility.
  Open Scope N_scope.
  Definition maybe (n : N) : option N :=
    if n =? 0 then None else Some n.

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

  Definition throwIf {E : Type}
                    (cond : bool)
                    (err : E)
                    : result unit E :=
    if cond then Err err else Ok tt.

  Context `{Base : ChainBase}.
  Definition without_actions {T E : Type}
                             (x : result T E)
                             : result (T * list ActionBody) E :=
    x >>= (fun new_state => Ok (new_state, [])).

  Definition not_payable {T E : Type}
                         (ctx : ContractCallContext)
                         (x : result T E)
                         (err : E)
                         : result T E :=
    do _ <- throwIf (ctx.(ctx_amount) >? 0)%Z err; x.

End Utility.

Ltac destruct_throw_if H :=
  match type of H with
  | throwIf _ _ = @Err _ _ _ =>
    let G := fresh "G" in
      unfold throwIf in H;
      destruct_match eqn:G in H; try congruence;
      clear H;
      rename G into H
  | throwIf _ _ = @Ok _ _ ?u =>
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
  | H : throwIf _ _ = @Err _ _ _ |- _ => destruct_throw_if H
  | H : throwIf _ _ = @Ok _ _ ?u |- _ => destruct_throw_if H
  | H : @Ok _ _ _ = @Ok _ _ _ |- _ =>
      first [injection H as H; subst | injection H as <- | injection H as ->]
  | H : @Some _ _ = @Some _ _ |- _ =>
      first [injection H as H; subst | injection H as <- | injection H as ->]

  | H : _ match ?m with | @Ok _ _ _ => _ | @Err _ _ _ => @Err _ _ _ end = @Ok _ _ _ |- _ =>
      destruct_match_some m in H
  | H : match ?m with | @Ok _ _ _ => _ | @Err _ _ _ => @Err _ _ _ end = @Ok _ _ _ |- _ =>
      destruct_match_some m in H
  | H : _ (if ?m then @Err _ _ _ else _) = @Ok _ _ _ |- _ =>
      destruct_match_some m in H
  | H : _ (if ?m then _ else @Err _ _ _) = @Ok _ _ _ |- _ =>
      destruct_match_some m in H
  | H : (if ?m then @Err _ _ _ else _) = @Ok _ _ _ |- _ =>
      destruct_match_some m in H
  | H : (if ?m then _ else @Err _ _ _) = @Ok _ _ _ |- _ =>
      destruct_match_some m in H
  | |- context [_ (match ?m with @Ok _ _ _ => _ | @Err _ _ _ => _ end) = @Ok _ _ _] =>
      destruct m eqn:?H
  | |- context [match ?m with @Ok _ _ _ => _ | @Err _ _ _ => _ end = @Ok _ _ _] =>
      destruct m eqn:?H

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

Ltac result_to_option :=
  match goal with
  | H : result_of_option _ _ = @Ok _ _ _ |- _ => apply result_of_option_eq_some in H; try (rewrite H in *)
  | H : result_of_option _ _ = @Err _ _ _ |- _ => apply result_of_option_eq_none in H; try (rewrite H in *)
  end.

Ltac solve_facts :=
  repeat match goal with
    | H := ?f : nat -> nat -> nat -> nat -> nat -> nat -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ _ => Logic.True)
    | H := ?f : _ -> ContractCallContext -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ => Logic.True)
    | H := ?f : Chain -> ContractCallContext -> _ ->
    list ActionBody -> option (list (ContractCallInfo _)) -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ => Logic.True)
    end;
    unset_all; subst;
    destruct_chain_step; [
       auto
     | destruct_action_eval; [
         auto
       | auto
       | auto; intros ?cstate ?deployed ?deployed_state;
          cbn; subst
       ]
     | auto
     | auto
    ].
