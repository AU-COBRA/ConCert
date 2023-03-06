(** * Dexter 2 FA1.2 Liquidity token contract *)
(** This file contains an implementation of Dexter2 liquidity contract
    https://gitlab.com/dexter2tz/dexter2tz/-/blob/1cec9d9333eba756603d6cd90ea9c70d482a5d3d/lqt_fa12.mligo
    In addition this file contains proof of functional correctness w.r.t the
    informal specification https://gitlab.com/dexter2tz/dexter2tz/-/blob/1cec9d9333eba756603d6cd90ea9c70d482a5d3d/docs/informal-spec/dexter2-lqt-fa12.md

    This contract is an extension of a basic FA1.2 token contract with
    an extra entrypoint that allows an admin to mint and burn tokens.
    It is used in the Dexter2 exchange paired with an instance of the
    Dexter2 CPMM contract. The purpose of this contract is to keep track
    of ownership of the exchanges funds. A user who owns x% of the supply
    of liquidity tokens owns x% of the exchanges trading reserve.
*)
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import InterContractCommunication.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Examples.Dexter2 Require Import Dexter2FA12. Import DEX2LQT.
From Coq Require Import ZArith_base.
From Coq Require Import Bool.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.



(** * Properties *)
Section Theories.
  Context `{ChainBase}.
  Open Scope N_scope.

  (* begin hide *)
  (* always unfold, if applied *)
  Arguments AddressMap.update _ _ _ _ _ /.
  Arguments AddressMap.find _ _ _ _/.
  Arguments AddressMap.empty _ _/.

  Arguments find_allowance _ _ _ /.
  Arguments update_allowance _ _ _ _ /.

  Arguments non_zero_amount _ /.

  Set Keyed Unification.
  (* end hide *)

  (** ** Contract rejects money *)
  (** [receive_lqt] only returns Some if the sender amount is zero *)
  Lemma contract_not_payable : forall prev_state new_state chain ctx msg new_acts,
    receive_lqt chain ctx prev_state msg = Ok (new_state, new_acts) ->
      ((ctx_amount ctx) <= 0)%Z.
  Proof.
    intros * receive_some.
    unfold receive_lqt, throwIf in receive_some; cbn in receive_some.
    destruct (0 <? _)%Z eqn:amount in receive_some.
    - (* case: ctx_amount > 0 *)
      congruence.
    - (* case: ctx_amount <= 0 *)
      now rewrite Z.ltb_ge in amount.
  Qed.

  Lemma contract_not_payable' : forall prev_state chain ctx msg,
    (0 < (ctx_amount ctx))%Z ->
      receive_lqt chain ctx prev_state msg = Err default_error.
  Proof.
    intros * ctx_amount_positive.
    unfold receive_lqt,throwIf; cbn.
    destruct (0 <? _)%Z eqn:amount.
    - (* case: ctx_amount > 0 *)
      reflexivity.
    - (* case: ctx_amount <= 0 *)
      now apply Z.ltb_ge in amount.
  Qed.

  (* begin hide *)
  Tactic Notation "contract_simpl" := contract_simpl @receive_lqt @init_lqt.

  Ltac destruct_message :=
    repeat match goal with
    | msg : option Msg |- _ => destruct msg
    | msg : Msg |- _ => destruct msg
    | H : Blockchain.receive _ _ _ _ None = Ok _ |- _ => now contract_simpl
    | H : receive_lqt _ _ _ None = Ok _ |- _ => now contract_simpl
    end.
  (* end hide *)



  (* Admin cannot be changed *)
  Lemma admin_constant : forall prev_state new_state chain ctx new_acts msg,
    receive_lqt chain ctx prev_state msg = Ok (new_state, new_acts) ->
      admin prev_state = admin new_state.
  Proof.
    intros * receive_some.
    destruct_message;
      now contract_simpl.
  Qed.



  (** ** Default entrypoint correct *)
  (* Default entrypoint should never succeed *)
  Lemma default_entrypoint_none : forall prev_state chain ctx,
    receive_lqt chain ctx prev_state None = Err default_error.
  Proof.
    intros *.
    contract_simpl.
    destruct_match eqn:e;
      destruct_throw_if e.
  Qed.



  (** ** Transfer correct *)
  Definition transfer_balance_update_correct old_state new_state from to amount :=
    let get_balance addr state := with_default 0 (FMap.find addr state.(tokens)) in
    let from_balance_before := get_balance from old_state in
    let to_balance_before := get_balance to old_state in
    let from_balance_after := get_balance from new_state in
    let to_balance_after := get_balance to new_state in
    (* If the transfer is a self-transfer, balances should remain unchained *)
    if address_eqb from to
    then
      (from_balance_before =? from_balance_after) &&
      (to_balance_before =? to_balance_after)
    else
      (from_balance_before =? from_balance_after + amount) &&
      (to_balance_before + amount =? to_balance_after).

  (** [try_transfer] correctly moves [amount] from [from] to [to] *)
  Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_transfer param)) = Ok (new_state, new_acts) ->
    transfer_balance_update_correct prev_state new_state param.(from) param.(to) param.(value) = true.
  Proof.
    intros * receive_some.
    contract_simpl.
    match goal with
      [ H : with_default 0 _ <? _ = false |- _ ] => rename H into enough_balance
    end.
    rewrite N.ltb_ge in enough_balance.
    unfold transfer_balance_update_correct.
    cbn.
    destruct_match eqn:from_to_eqb.
    - (* from = to *)
      destruct (address_eqb_spec param.(from) param.(to)) as [<-|]; auto.
      rewrite !FMap.map_update_idemp.
      rewrite !FMap.find_update_eq with (map := prev_state.(tokens)).
      destruct (FMap.find (from param) _) eqn:from_prev; cbn in *.
      + now apply maybe_sub_add in enough_balance as [[-> ->] | ->]; rewrite N.eqb_refl.
      + rewrite N.add_0_l.
        apply N.le_0_r in enough_balance.
        now rewrite enough_balance.
    - (* from <> to *)
      destruct (address_eqb_spec param.(from) param.(to)) as [| from_to_eq]; auto.
      rewrite !FMap.find_update_ne with (map := prev_state.(tokens)) by auto.
      rewrite !FMap.find_update_ne by auto.
      rewrite !FMap.find_update_eq.
      destruct (FMap.find (from param) _) eqn:from_prev; cbn;
        [| apply N.le_0_r in enough_balance; rewrite enough_balance];
      destruct (FMap.find (to param) _) eqn:to_prev; cbn;
      rewrite ?N.add_0_l, ?N.add_0_r, ?N.sub_add, ?N.eqb_refl by auto;
      rewrite andb_true_iff, ?N.eqb_eq;
      cbn in enough_balance.
      * specialize (maybe_cases (n - value param)) as [[-> ?H] | [-> _]];
        specialize (maybe_cases (n0 + value param)) as [[-> ?H] | [-> _]];
        cbn; lia.
      * specialize (maybe_cases (n - value param)) as [[-> ?H] | [-> _]];
        specialize (maybe_cases (value param)) as [[-> ?H] | [-> _]];
        cbn; lia.
      * now specialize (maybe_cases n) as [[-> ?H] | [-> _]].
      * auto.
  Qed.

  Definition transfer_allowances_update_correct old_state new_state sender from amount :=
    let get_allowance addr1 addr2 state := with_default 0 (FMap.find (addr1, addr2) state.(allowances)) in
    let allowance_before := get_allowance from sender old_state in
    let allowance_after := get_allowance from sender new_state in
    (* If from and sender is equal, allowances should remain unchained *)
    if address_eqb sender from
    then
      (allowance_before =? allowance_after)
    else
      (allowance_before =? allowance_after + amount).

  (** [try_transfer] correctly subtracts [amount] from allowances if [sender] is not [from] *)
  Lemma try_transfer_allowance_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_transfer param)) = Ok (new_state, new_acts) ->
    transfer_allowances_update_correct prev_state new_state ctx.(ctx_from) param.(from) param.(value) = true.
  Proof.
    intros * receive_some.
    contract_simpl.
    unfold transfer_allowances_update_correct.
    cbn.
    destruct_match eqn:sender_from_eqb.
    - (* sender = from *)
      match goal with
      [ H : Ok (allowances _) = Ok _ |- _ ] => rename H into allowances_eq
      end.
      inversion_clear allowances_eq.
      now rewrite N.eqb_refl.
    - (* sender <> from *)
      contract_simpl.
      match goal with
      [ H : with_default 0 (FMap.find _ (allowances _)) <? _ = false |- _ ] => rename H into enough_allowance
      end.
      rewrite N.ltb_ge in enough_allowance.
      rewrite FMap.find_update_eq.
      destruct (FMap.find (from param, ctx_from ctx) (allowances prev_state)) eqn:from_prev; cbn.
      + unfold maybe.
        destruct (n - value param =? 0) eqn:n_eq_value; cbn.
        * apply N.eqb_eq in n_eq_value.
          rewrite N.sub_0_le in n_eq_value.
          erewrite (N.le_antisymm n _) by eassumption.
          now rewrite !N.eqb_refl.
        * now rewrite N.sub_add, N.eqb_refl.
      + apply N.le_0_r in enough_allowance.
        now rewrite enough_allowance.
  Qed.

  (** [try_transfer] does not produce any new actions *)
  Lemma try_transfer_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_transfer param)) = Ok (new_state, new_acts) ->
      new_acts = [].
  Proof.
    intros * receive_some.
    contract_simpl.
  Qed.

  (** [try_transfer] does not change the total supply of tokens *)
  Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_transfer param)) = Ok (new_state, new_acts) ->
      total_supply prev_state = total_supply new_state.
  Proof.
    intros * receive_some.
    contract_simpl.
  Qed.

  (** [try_transfer] only modifies the [from] and [to] balances *)
  Lemma try_transfer_preserves_other_balances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_transfer param)) = Ok (new_state, new_acts) ->
      forall account, account <> param.(from) -> account <> param.(to) ->
        FMap.find account (tokens prev_state) = FMap.find account (tokens new_state).
  Proof.
    intros * receive_some account account_not_from account_not_to.
    contract_simpl.
    cbn.
    now rewrite !FMap.find_update_ne.
  Qed.

  (** [try_transfer] only modifies the [sender] and [from] allowances *)
  Lemma try_transfer_preserves_other_allowances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_transfer param)) = Ok (new_state, new_acts) ->
      forall allowance_key, allowance_key <> (param.(from), ctx.(ctx_from)) ->
        FMap.find allowance_key (allowances prev_state) = FMap.find allowance_key (allowances new_state).
  Proof.
    intros * receive_some account allowance_key_ne.
    contract_simpl.
    cbn.
    match goal with
      [ H : _ = Ok _ |- _ ] => rename H into allowance_eq
    end.
    destruct_address_eq.
    - (* from = sender *)
      now inversion_clear allowance_eq.
    - (* from <> sender *)
      destruct_match in allowance_eq;
        inversion_clear allowance_eq.
      now rewrite !FMap.find_update_ne.
  Qed.

  (** [try_transfer] removes empty entries from allowances map *)
  Lemma try_transfer_remove_empty_allowances : forall prev_state new_state chain ctx new_acts param,
    (forall n, FMap.find (param.(from), ctx.(ctx_from)) (allowances prev_state) = Some n -> n > 0) ->
    receive_lqt chain ctx prev_state (Some (msg_transfer param)) = Ok (new_state, new_acts) ->
      forall n, FMap.find (param.(from), ctx.(ctx_from)) (allowances new_state) = Some n -> n > 0.
  Proof.
    intros * IH receive_some *.
    contract_simpl.
    destruct_match in *.
    - now contract_simpl.
    - contract_simpl.
      rewrite !FMap.find_update_eq.
      now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
  Qed.

  (** [try_transfer] removes empty entries from balance map *)
  Lemma try_transfer_remove_empty_balances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_transfer param)) = Ok (new_state, new_acts) ->
      forall n,
      (FMap.find param.(from) (tokens new_state) = Some n -> n > 0) /\
      (FMap.find param.(to) (tokens new_state) = Some n -> n > 0).
  Proof.
    intros * receive_some *.
    contract_simpl.
    rewrite N.ltb_ge in *.
    destruct (address_eqb_spec param.(from) param.(to)) as [<-|]; auto.
    - rewrite !FMap.find_update_eq.
      now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
    - rewrite !FMap.find_update_ne by auto.
      rewrite !FMap.find_update_eq.
      rewrite !FMap.find_update_ne with (map := prev_state.(tokens)) by auto.
      specialize (maybe_cases ) as [[-> ?H] | [-> ?H]];
      now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
  Qed.

  (** If the requirements are met then receive on transfer msg must succeed and
      if receive on transfer msg succeeds then requirements must hold *)
  Lemma try_transfer_is_some : forall state chain ctx param,
    (ctx_amount ctx <= 0)%Z /\
    param.(value) <= with_default 0 (FMap.find param.(from) (tokens state)) /\
    (param.(from) <> ctx.(ctx_from) ->
      param.(value) <= with_default 0 (FMap.find (param.(from), ctx.(ctx_from)) (allowances state)))
      <-> exists new_state new_acts, receive_lqt chain ctx state (Some (msg_transfer param)) = Ok (new_state, new_acts).
  Proof.
    split.
    - intros (amount_zero & enough_balance & enough_allowance).
      apply Z.ltb_ge in amount_zero.
      cbn.
      rewrite amount_zero; cbn.
      destruct_match eqn:receive_some;
      destruct_match eqn:allowances_eq in receive_some;
      destruct_match eqn:sender_from_eqb in allowances_eq; try congruence;
      try destruct_match eqn:enough_allowance_check in allowances_eq; try congruence;
      try destruct_match eqn:new_balance in receive_some;
      try destruct_match eqn:enough_balance_check in new_balance; try congruence.
      + (* case no contradictions *)
        now inversion_clear allowances_eq.
      + (* case: no contradictions *)
        now inversion_clear allowances_eq.
      + (* enough balances contradiction *)
        contract_simpl.
        apply N.ltb_lt in enough_balance_check.
        now apply N.le_ngt in enough_balance.
      + (* enough balances contradiction *)
        contract_simpl.
        apply N.ltb_lt in enough_balance_check.
        now apply N.le_ngt in enough_balance.
      + (* enough allowance contradiction *)
        contract_simpl.
        apply N.ltb_lt in enough_allowance_check.
        destruct (address_eqb_spec ctx.(ctx_from) param.(from)) as [| sender_from_ne]; try discriminate.
        now apply not_eq_sym, enough_allowance, N.le_ngt in sender_from_ne.
    - intros (new_state & new_acts & receive_some).
      contract_simpl.
      rewrite Z.ltb_ge in *.
      split; try assumption.
      rewrite N.ltb_ge in *.
      destruct_match eqn:sender_from_eqb in *.
        destruct (address_eqb_spec ctx.(ctx_from) param.(from)) as
          [send_from_eq | sender_from_ne]; contract_simpl; try discriminate.
      + (* sender = from *)
        now split.
      + (* sender <> from *)
        destruct_match eqn:enough_allowance in *; try congruence.
        contract_simpl.
        now apply N.ltb_ge in enough_allowance.
  Qed.



  (** ** Approve correct *)
  (** [try_approve] correctly sets allowance of [(sender, spender)] to [value_] *)
  Lemma try_approve_allowance_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_approve param)) = Ok (new_state, new_acts) ->
      FMap.find (ctx.(ctx_from), param.(spender)) (allowances new_state) = maybe param.(value_).
  Proof.
    intros * receive_some.
    contract_simpl.
    cbn.
    now rewrite !FMap.find_update_eq.
  Qed.

  (** [try_approve] does not produce any new actions *)
  Lemma try_approve_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_approve param)) = Ok (new_state, new_acts) ->
      new_acts = [].
  Proof.
    intros * receive_some.
    contract_simpl.
  Qed.

  (** [try_approve] does not change allowances map of other addresses *)
  Lemma try_approve_preserves_other_allowances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_approve param)) = Ok (new_state, new_acts) ->
      forall allowance_key, allowance_key <> (ctx.(ctx_from), param.(spender)) ->
        FMap.find allowance_key (allowances prev_state) = FMap.find allowance_key (allowances new_state).
  Proof.
    intros * receive_some allowance_key allowance_key_ne.
    contract_simpl.
    cbn.
    now rewrite FMap.find_update_ne.
  Qed.

  (** [try_approve] does not change total supply of tokens *)
  Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_approve param)) = Ok (new_state, new_acts) ->
      total_supply prev_state = total_supply new_state.
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_approve] does not change balances *)
  Lemma try_approve_preserves_balances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_approve param)) = Ok (new_state, new_acts) ->
      tokens prev_state = tokens new_state.
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_approve] removes empty entries from allowances map *)
  Lemma try_approve_remove_empty_allowances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_approve param)) = Ok (new_state, new_acts) ->
      forall n, FMap.find (ctx.(ctx_from), param.(spender)) (allowances new_state) = Some n -> n > 0.
  Proof.
    intros * IH receive_some *.
    contract_simpl.
    cbn.
    rewrite FMap.find_update_eq.
    now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
  Qed.

  (** If the requirements are met then receive on approve msg must succeed and
      if receive on approve msg succeeds then requirements must hold *)
  Lemma try_approve_is_some : forall state chain ctx param,
    (ctx_amount ctx <= 0)%Z /\
    (with_default 0 (FMap.find (ctx.(ctx_from), param.(spender)) (allowances state)) = 0 \/ param.(value_) = 0)
      <-> exists new_state new_acts, receive_lqt chain ctx state (Some (msg_approve param)) = Ok (new_state, new_acts).
  Proof.
    split;
      intros;
      destruct_hyps;
      contract_simpl;
      propify;
      try easy.
    destruct_match eqn:H4 in H3; try congruence.
    destruct_throw_if H4.
    now propify.
  Qed.



  (** ** Mint or burn correct *)
  (** [try_mint_or_burn] correctly mints/burns [amount] from/to [target] *)
  Lemma try_mint_or_burn_balance_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_mint_or_burn param)) = Ok (new_state, new_acts) ->
      (Z.of_N (with_default 0%N (FMap.find param.(target) (tokens prev_state))) + param.(quantity) =
      Z.of_N (with_default 0%N (FMap.find param.(target) (tokens new_state))))%Z.
  Proof.
    intros * receive_some.
    contract_simpl.
    rewrite Z.ltb_ge in *.
    cbn.
    rewrite FMap.find_update_eq.
    unfold maybe.
    unfold FMap.find in *. (* NOTE: after using AddressMap, unification fails sometime, unless we unfold [FMap.find] and other definitions. *)
    destruct (Z.to_N (Z.of_N (with_default 0 _) + quantity param) =? 0) eqn:eq_zero; cbn.
    - apply N.eqb_eq in eq_zero. unfold FMap.find in *.
      lia.
    - rewrite <- Z2N.id by lia.
      lia.
  Qed.

  (** [try_mint_or_burn] correctly updates [total_supply] *)
  Lemma try_mint_or_burn_total_supply_correct : forall prev_state new_state chain ctx new_acts param,
    with_default 0 (FMap.find param.(target) (tokens prev_state)) <= total_supply prev_state ->
    receive_lqt chain ctx prev_state (Some (msg_mint_or_burn param)) = Ok (new_state, new_acts) ->
      (Z.of_N prev_state.(total_supply) + param.(quantity) =
      Z.of_N new_state.(total_supply))%Z.
  Proof.
    intros * balance_le_total_supply receive_some.
    contract_simpl.
    rewrite Z.ltb_ge in *.
    cbn.
    rewrite N2Z.inj_abs_N, Z.abs_eq; auto.
    unfold FMap.find in *; lia.
  Qed.


  (** [try_mint_or_burn] produces no new actions *)
  Lemma try_mint_or_burn_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_mint_or_burn param)) = Ok (new_state, new_acts) ->
      new_acts = [].
  Proof.
    intros.
    contract_simpl.
  Qed.

  (** [try_mint_or_burn] only modifies the [target] balance *)
  Lemma try_mint_or_burn_preserves_other_balances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_mint_or_burn param)) = Ok (new_state, new_acts) ->
      forall account, account <> param.(target) ->
        FMap.find account (tokens prev_state) = FMap.find account (tokens new_state).
  Proof.
    intros * receive_some account account_not_target.
    contract_simpl.
    cbn.
    now rewrite FMap.find_update_ne.
  Qed.

  (** [try_mint_or_burn] does not change allowances *)
  Lemma try_mint_or_burn_preserves_allowances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_mint_or_burn param)) = Ok (new_state, new_acts) ->
        allowances prev_state = allowances new_state.
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_mint_or_burn] removes empty entries from balance map *)
  Lemma try_mint_or_burn_remove_empty_balances : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_mint_or_burn param)) = Ok (new_state, new_acts) ->
      forall n, FMap.find param.(target) (tokens new_state) = Some n -> n > 0.
  Proof.
    intros * receive_some *.
    contract_simpl.
    rewrite Z.ltb_ge in *.
    cbn.
    rewrite FMap.find_update_eq.
    now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
  Qed.

  (** If the requirements are met then receive on mint_or_burn msg must succeed and
      if receive on mint_or_burn msg succeeds then requirements must hold *)
  Lemma try_mint_or_burn_is_some : forall state chain ctx param,
    (ctx_amount ctx <= 0)%Z /\
    ctx.(ctx_from) = state.(admin) /\
    (0 <= Z.of_N (with_default 0%N (FMap.find param.(target) (tokens state))) + param.(quantity))%Z
      <-> exists new_state new_acts, receive_lqt chain ctx state (Some (msg_mint_or_burn param)) = Ok (new_state, new_acts).
  Proof.
    split;
      intros;
      destruct_hyps;
      contract_simpl;
      propify;
      try easy;
      try now destruct_address_eq.
    destruct_match eqn:H5 in H4; try congruence.
    destruct_match eqn:H6 in H4; try congruence.
    destruct_throw_if H5.
    destruct_throw_if H6.
    now propify.
    now destruct_address_eq.
  Qed.



  (** ** Get allowance correct *)
  (** [try_get_allowance] produces a callback to the correct contract with
      the requested allowance, the call should carry no balance *)
  Lemma try_get_allowance_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_get_allowance param)) = Ok (new_state, new_acts) ->
      new_acts = [
        act_call param.(allowance_callback) 0%Z (serialize
          (receive_allowance (with_default 0 (FMap.find param.(request) (allowances prev_state)))))
      ].
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_get_allowance] does not modify state *)
  Lemma try_get_allowance_preserves_state : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_get_allowance param)) = Ok (new_state, new_acts) ->
      prev_state = new_state.
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** If the requirements are met then receive on get_allowance msg must succeed and
      if receive on get_allowance msg succeeds then requirements must hold *)
  Lemma try_get_allowance_is_some : forall prev_state chain ctx param,
    (ctx_amount ctx <= 0)%Z <->
    exists new_state new_acts, receive_lqt chain ctx prev_state (Some (msg_get_allowance param)) = Ok (new_state, new_acts).
  Proof.
    split;
      intros;
      destruct_hyps;
      contract_simpl;
      now propify.
  Qed.



  (** ** Get balance correct *)
  (** [try_get_balance] produces a callback to the correct contract with
      the requested balance, the call should carry no balance *)
  Lemma try_get_balance_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_get_balance param)) = Ok (new_state, new_acts) ->
      new_acts = [
        act_call param.(balance_callback) 0%Z (serialize
          (receive_balance_of (with_default 0 (FMap.find param.(owner_) (tokens prev_state)))))
      ].
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_get_balance] does not modify state *)
  Lemma try_get_balance_preserves_state : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_get_balance param)) = Ok (new_state, new_acts) ->
      prev_state = new_state.
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** If the requirements are met then receive on get_balance msg must succeed and
      if receive on get_balance msg succeeds then requirements must hold *)
  Lemma try_get_balance_is_some : forall prev_state chain ctx param,
    (ctx_amount ctx <= 0)%Z <->
    exists new_state new_acts, receive_lqt chain ctx prev_state (Some (msg_get_balance param)) = Ok (new_state, new_acts).
  Proof.
    split;
      intros;
      destruct_hyps;
      contract_simpl;
      now propify.
  Qed.



  (** ** Get total supply correct *)
  (** [try_get_total_supply] produces a callback to the correct contract with
      the total supply of tokens, the call should carry no balance *)
  Lemma try_get_total_supply_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_get_total_supply param)) = Ok (new_state, new_acts) ->
      new_acts = [
        act_call param.(supply_callback) 0%Z (serialize
          (receive_total_supply prev_state.(total_supply)))
      ].
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_get_total_supply] does not modify state *)
  Lemma try_get_total_supply_preserves_state : forall prev_state new_state chain ctx new_acts param,
    receive_lqt chain ctx prev_state (Some (msg_get_total_supply param)) = Ok (new_state, new_acts) ->
      prev_state = new_state.
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** If the requirements are met then receive on get_total_supply msg must succeed and
      if receive on get_total_supply msg succeeds then requirements must hold *)
  Lemma try_get_total_supply_is_some : forall prev_state chain ctx param,
    (ctx_amount ctx <= 0)%Z <->
    exists new_state new_acts, receive_lqt chain ctx prev_state (Some (msg_get_total_supply param)) = Ok (new_state, new_acts).
  Proof.
    split;
      intros;
      destruct_hyps;
      contract_simpl;
      now propify.
  Qed.



  (** ** Init correct *)
  (** After initialization no accounts should hold tokens *)
  Lemma init_balances_correct : forall chain ctx setup state,
    init_lqt chain ctx setup = Ok state ->
      state.(tokens) = FMap.add setup.(lqt_provider) setup.(initial_pool) FMap.empty.
  Proof.
    intros * init_some.
    now inversion init_some.
  Qed.

  (** After initialization no allowances should be set *)
  Lemma init_allowances_correct : forall chain ctx setup state,
    init_lqt chain ctx setup = Ok state ->
      state.(allowances) = FMap.empty.
  Proof.
    intros * init_some.
    now inversion init_some.
  Qed.

  Lemma init_admin_correct : forall chain ctx setup state,
    init_lqt chain ctx setup = Ok state ->
      state.(admin) = setup.(admin_).
  Proof.
    intros * init_some.
    now inversion init_some.
  Qed.

  Lemma init_total_supply_correct : forall chain ctx setup state,
    init_lqt chain ctx setup = Ok state ->
      state.(total_supply) = setup.(initial_pool).
  Proof.
    intros * init_some.
    now inversion init_some.
  Qed.

  (** initialization should always succeed *)
  Lemma init_is_some : forall chain ctx setup,
    exists state, init_lqt chain ctx setup = state.
  Proof.
    intros.
    eauto.
  Qed.

  (* begin hide *)
  Ltac try_solve_acts_correct :=
    match goal with
    | [ H : receive_lqt _ _ _ _ = Ok _ |- _ ] =>
      first [apply try_transfer_new_acts_correct in H
            |apply try_approve_new_acts_correct in H
            |apply try_mint_or_burn_new_acts_correct in H
            |apply try_get_allowance_new_acts_correct in H
            |apply try_get_balance_new_acts_correct in H
            |apply try_get_total_supply_new_acts_correct in H ];
      subst; eauto
    end.

  Ltac try_solve_preserves_state :=
    match goal with
    | [ H : receive_lqt _ _ _ _ = Ok _ |- _ ] =>
      first [apply try_get_allowance_preserves_state in H
            |apply try_get_balance_preserves_state in H
            |apply try_get_total_supply_preserves_state in H];
      subst; eauto
    end.
  (* end hide *)



  (** ** Outgoing acts facts *)
  (** If contract emits self calls then they are for the receive entrypoints (which do not exist) *)
  Lemma only_getter_self_calls bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    Forall (fun act_body =>
      match act_body with
      | act_transfer to _ => False
      | act_call to _ msg => to = caddr ->
          (exists n, msg = serialize (receive_allowance n)) \/
          (exists n, msg = serialize (receive_balance_of n)) \/
          (exists n, msg = serialize (receive_total_supply n))
      | _ => False
      end) (outgoing_acts bstate caddr).
  Proof.
    contract_induction; intros; auto.
    - now inversion IH.
    - apply Forall_app; split; auto.
      clear IH. simpl in *.
      destruct msg.
      + destruct m;
          try_solve_acts_correct.
      + contract_simpl.
    - inversion_clear IH as [|? ? head_not_me tail_not_me].
      destruct head;
        try contradiction.
      destruct action_facts as (? & ? & ? & ?).
      subst.
      destruct head_not_me as [[] | [[] | []]]; auto;
        subst;
        now contract_simpl.
    - now rewrite <- perm.
    - solve_facts.
  Qed.

  (** Contract never calls itself *)
  Lemma no_self_calls : forall bstate origin from_addr to_addr amount msg acts ctx prev_state new_state resp_acts,
    reachable bstate ->
    env_contracts bstate to_addr = Some (contract : WeakContract) ->
    chain_state_queue bstate =
    {| act_origin := origin;
      act_from := from_addr;
      act_body :=
        match msg with
        | Some msg => act_call to_addr amount msg
        | None => act_transfer to_addr amount
      end |} :: acts ->
    wc_receive contract bstate ctx prev_state msg = Ok (new_state, resp_acts) ->
    from_addr <> to_addr.
  Proof.
    intros * reach deployed queue receive_some.
    apply only_getter_self_calls in deployed as no_self_calls; auto.
    unfold outgoing_acts in no_self_calls.
    rewrite queue in no_self_calls.
    cbn in no_self_calls.
    destruct_address_eq; auto.
    inversion_clear no_self_calls as [|? ? hd _].
    destruct msg; auto.
    destruct hd as [[] | [[] | []]];
      auto; subst;
      eapply wc_receive_strong in receive_some as (_ & ? & _ & _ & msg_correct & _);
      now destruct_match in msg_correct.
  Qed.

  (** The contract never produces actions carrying money *)
  Lemma new_acts_amount_zero : forall prev_state chain ctx msg new_state new_acts,
    receive_lqt chain ctx prev_state msg = Ok (new_state, new_acts) ->
      sumZ (fun act => act_body_amount act) new_acts = 0%Z.
  Proof.
    intros * receive_some.
    destruct msg.
    - destruct m; try_solve_acts_correct.
    - contract_simpl.
  Qed.

  Lemma outgoing_acts_amount_zero : forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    Forall (fun act => act_body_amount act = 0%Z) (outgoing_acts bstate caddr).
  Proof.
    intros * reach deployed.
    apply (lift_outgoing_acts_prop contract); auto.
    intros * receive_some. simpl in *.
    destruct msg.
    - destruct m; try_solve_acts_correct.
    - contract_simpl.
  Qed.

  (** Contract only produces contract call actions *)
  Lemma outgoing_acts_are_calls : forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    Forall (fun act_body =>
      match act_body with
      | act_call _ _ _ => True
      | _ => False
      end) (outgoing_acts bstate caddr).
  Proof.
    intros * reach deployed.
    apply (lift_outgoing_acts_prop contract); auto.
    intros * receive_some; simpl in *.
    destruct msg.
    - destruct m; try_solve_acts_correct.
    - contract_simpl.
  Qed.



  (** ** Contract balance facts *)
  (* Contract balance should never change and thus always be equal to the deploy amount *)
  Lemma contract_balance_bound' : forall bstate caddr (trace : ChainTrace empty_state bstate),
    let effective_balance := (env_account_balances bstate caddr - (sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr)))%Z in
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists deploy_info,
      deployment_info Setup trace caddr = Some deploy_info
      /\ effective_balance = deploy_info.(deployment_amount).
  Proof.
    intros.
    subst effective_balance.
    contract_induction; intros; auto.
    - cbn.
      lia.
    - cbn in IH.
      lia.
    - instantiate (CallFacts := fun _ ctx _ _ _ =>
        (0 <= ctx_amount ctx)%Z /\ ctx_from ctx <> ctx_contract_address ctx).
      destruct facts as (ctx_amount_positive & _).
      simpl in *.
      apply contract_not_payable in receive_some as not_payable.
      apply new_acts_amount_zero in receive_some as amount_zero_new_acts.
      apply Z.le_antisymm in ctx_amount_positive; auto.
      rewrite ctx_amount_positive, Z.sub_0_r in IH.
      now rewrite sumZ_app, amount_zero_new_acts, Z.add_0_l.
    - now destruct facts.
    - now erewrite sumZ_permutation in IH by eauto.
    - solve_facts.
      split.
      + now apply Z.ge_le.
      + rewrite deployed in *.
        match goal with
        | H : Some ?x = Some _ |- _ => inversion H; subst x; clear H
        end.
        eapply no_self_calls; eauto.
        now constructor.
  Qed.

  Lemma contract_balance_bound : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists deploy_info,
      deployment_info Setup trace caddr = Some deploy_info
      /\ env_account_balances bstate caddr = deploy_info.(deployment_amount).
  Proof.
    intros * deployed.
    specialize contract_balance_bound' as (dep_info & deployment_info_eq & balance_bound); eauto.
    eexists.
    rewrite deployment_info_eq.
    split; eauto.
    rewrite <- balance_bound.
    rewrite Zminus_0_l_reverse, Z.sub_cancel_l at 1.
    apply outgoing_acts_amount_zero in deployed as act_amount_zero;
      try now constructor.
    clear balance_bound deployment_info_eq dep_info trace deployed.
    induction (outgoing_acts bstate caddr).
    - reflexivity.
    - cbn.
      apply list.Forall_cons in act_amount_zero as (act_amount_zero & acts_amount_zero).
      rewrite act_amount_zero, Z.add_0_l.
      now apply IHl.
  Qed.



  (** ** Total supply / token balance facts *)
  (** Sum of all token balances *)
  Definition sum_balances state :=
    sumN (fun '(k, v) => v) (FMap.elements (tokens state)).

  (** The balance of a single account is always less than
    or equal to the sum of all balances *)
  Lemma balance_le_sum_balances : forall addr state,
    with_default 0 (FMap.find addr (tokens state)) <= sum_balances state.
  Proof.
    intros.
    destruct FMap.find eqn:balance.
    - eapply FMap.In_elements, sumN_in_le in balance.
      eapply N.le_trans; cycle 1; eauto.
    - apply N.le_0_l.
  Qed.

  (** [total_supply] is always equal to the sum of all account token balances *)
  Lemma sum_balances_eq_total_supply : forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate
      /\ total_supply cstate = sum_balances cstate.
  Proof.
    intros * reach deployed.
    apply (lift_contract_state_prop contract);
      intros *; simpl in *; auto; clear reach deployed bstate caddr.
    - intros init_some.
      unfold sum_balances. cbn in *.
      erewrite init_total_supply_correct, init_balances_correct; eauto.
      rewrite FMap.elements_add, FMap.elements_empty by auto.
      now cbn.
    - intros IH receive_some.
      destruct msg. destruct m.
      + erewrite <- try_transfer_preserves_total_supply; eauto.
        rename t into param.
        unfold sum_balances.
        contract_simpl.
        cbn.
        rewrite N.ltb_ge in *.
        destruct (address_eqb_spec param.(from) param.(to)) as
          [<-| from_to_ne];
          [rewrite FMap.find_update_eq | rewrite FMap.find_update_ne by auto];
          destruct (FMap.find (from param) _) eqn:from_balance;
          destruct (FMap.find (to param) (tokens cstate)) eqn:to_balance;
          destruct param; cbn in *;
            unshelve (repeat match goal with
              | H : ?x = ?y |- context [ ?x ] => rewrite H
              | H : _ <= 0 |- _ => apply N.lt_eq_cases in H as [H | H]; try lia; subst
              | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => rewrite FMap.find_add
              | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => rewrite FMap.add_add
              | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
              | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
              | H : ?x <> ?y |- context [ FMap.find ?x (FMap.remove ?y _) ] => rewrite FMap.find_remove_ne; eauto
              | H : ?y <> ?x |- context [ FMap.find ?x (FMap.remove ?y _) ] => rewrite FMap.find_remove_ne; eauto
              | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add_existing; eauto
              | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add; eauto
              | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
              | H : FMap.find ?x ?m = Some _ |- context [ sumN _ ((_, _) :: FMap.elements (FMap.remove ?x ?m)) ] => rewrite fin_maps.map_to_list_delete; auto
              | H : FMap.find ?x _ = Some ?n |- context [ sumN _ ((?x, ?n) :: (_, _) :: FMap.elements (FMap.remove ?x _)) ] => rewrite sumN_swap, fin_maps.map_to_list_delete; auto
              | |- context [ sumN _ ((?t, ?n + ?m) :: _) ] => erewrite sumN_split with (x := (t, n)) (y := (_, m)) by lia
              | |- context [ sumN _ ((_, 0) :: (?x, ?n) :: _) ] => erewrite <- sumN_split with (z := (x, n)) by auto
              | |- context [ sumN _ ((_, ?n) :: (?x, ?m - ?n) :: _) ] => erewrite <- sumN_split with (z := (x, n + m - n))
              | |- context [ sumN _ ((?x, ?m - ?n) :: (_, ?n) :: _) ] => erewrite <- sumN_split with (z := (x, n + m - n))
              | |- context [ with_default _ None ] => unfold with_default
              | |- context [ with_default _ (Some _) ] => unfold with_default
              | |- context [ FMap.update _ None _ ] => unfold FMap.update
              | |- context [ FMap.update _ (Some _) _ ] => unfold FMap.update
              | |- context [ 0 + _ ] => rewrite N.add_0_l
              | |- context [ _ + 0 ] => rewrite N.add_0_r
              | |- context [ 0 - _ ] => rewrite N.sub_0_l
              | |- context [ _ - 0 ] => rewrite N.sub_0_r
              | H : ?x <= ?y, G : ?y - ?x = 0 |- _ => rewrite N.sub_0_le in G; apply N.le_antisymm in G
              | H : ?x + ?y = 0 |- _ => apply N.eq_add_0 in H as []
              | H : ?x = 0 |- _ => subst x
              | |- context [ FMap.update ?k _ (FMap.update ?k _ _) ] => rewrite FMap.map_update_idemp
              | H : ?y <= ?x |- context [ maybe (with_default 0 (maybe (?x - ?y)) + ?y) ] => apply maybe_sub_add in H as [[-> ->] | ->]
              | H : FMap.find ?x ?m = Some 0 |- context [ FMap.elements (FMap.remove ?x _) ] =>
                  rewrite <- N.add_0_r; change 0 with ((fun '(_, v) => v) (x, 0)); rewrite sumN_inv; rewrite fin_maps.map_to_list_delete
              | H : FMap.find ?k ?m = None |- context [ FMap.remove ?k _ ] => rewrite fin_maps.delete_notin
              | |- context [ maybe _ ] => specialize maybe_cases as [[-> ?H] | [-> _]]
              | H : ?y <> ?x |- context [ sumN _ ((?x, ?n) :: FMap.elements (FMap.remove ?y _)) ] =>
                  cbn; rewrite N.add_comm; change n with ((fun '(_, v) => v) (y, n)); rewrite sumN_inv
            end); try easy.
      + erewrite <- try_approve_preserves_total_supply; eauto.
        unfold sum_balances.
        erewrite <- try_approve_preserves_balances; eauto.
      + rename m into param.
        unfold sum_balances.
        contract_simpl.
        cbn.
        rewrite Z.ltb_ge in *.
        destruct (FMap.find (target param) _) eqn:target_balance; cbn.
        * assert (N_add_sub_move : forall n m p, p <= n -> n - p = m -> n = m + p) by lia.
          specialize (balance_le_sum_balances param.(target) cstate) as n_le_supply.
          rewrite target_balance in n_le_supply.
          cbn in n_le_supply.
          specialize maybe_cases as [[-> quantity_eq] | [-> _]]; cbn.
        -- cbn in *.
            rewrite <- N2Z.id in quantity_eq.
            apply Z2N.inj in quantity_eq; auto.
            rewrite Z.add_move_0_l in quantity_eq.
            rewrite quantity_eq, Zabs2N.abs_N_nonneg, Z.add_opp_r, Z2N.inj_sub.
            apply N.add_sub_eq_l.
            rewrite !N2Z.id, N.add_comm.
            change n with ((fun '(_, v) => v) (target param, n)).
            now rewrite sumN_inv, fin_maps.map_to_list_delete by assumption.
            all: lia.
        -- rewrite FMap.elements_add_existing by eauto.
            cbn.
            rewrite N.add_comm.
            apply N_add_sub_move; try lia.
            rewrite <- Zabs2N.abs_N_nonneg by assumption.
            rewrite <- Zabs2N.inj_sub by (split; [assumption | lia]).
            rewrite Z.add_add_simpl_r_r, Zabs2N.inj_sub, !Zabs2N.id by lia.
            apply N.add_sub_eq_r.
            change n with ((fun '(_, v) => v) (target param, n)).
            now rewrite sumN_inv, fin_maps.map_to_list_delete by assumption.
        * specialize maybe_cases as [[-> quantity_eq] | [-> _]]; cbn;
          unfold sum_balances in IH.
        -- rewrite fin_maps.delete_notin by auto.
            cbn in *.
            lia.
        -- rewrite FMap.elements_add by auto. cbn in *.
            lia.
      + try_solve_preserves_state.
      + try_solve_preserves_state.
      + try_solve_preserves_state.
      + now rewrite default_entrypoint_none in receive_some.
  Qed.

  (** Account token balances are always less than or equal to [total_supply] *)
  Lemma token_balance_le_total_supply : forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate
      /\ forall addr, with_default 0 (FMap.find addr (tokens cstate)) <= total_supply cstate.
  Proof.
    intros * reach deployed.
    apply sum_balances_eq_total_supply in deployed as
      (cstate & deployed_state & sum_eq_supply); auto.
    eexists.
    rewrite deployed_state, sum_eq_supply.
    clear reach deployed_state sum_eq_supply caddr bstate.
    split; auto.
    intros.
    apply balance_le_sum_balances.
  Qed.



  (** ** Empty map entries removed *)
  (** The [tokens] map never stores entries of zero *)
  Lemma zero_balances_removed : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists depinfo cstate,
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      let initial_tokens := initial_pool (deployment_setup depinfo) in
      initial_tokens > 0 ->
      forall addr n, FMap.find addr (tokens cstate) = Some n -> n > 0.
  Proof.
    intros * deployed.
    apply (lift_dep_info_contract_state_prop contract);
      auto; intros *; clear deployed trace bstate caddr.
    - intros init_some initial_pool_positive * addr_some.
      cbn in *.
      erewrite init_balances_correct in addr_some; eauto.
      destruct (address_eqb_spec addr (lqt_provider setup)) as [<-| addr_ne] in addr_some.
      + now rewrite FMap.find_add in addr_some.
      + now rewrite FMap.find_add_ne in addr_some.
    - intros IH receive_some initial_pool_positive * addr_some.
      unfold Blockchain.receive in receive_some.
      simpl in receive_some.
      destruct msg. destruct m.
      + destruct t.
        specialize (address_eqb_spec addr from) as [<- | addr_from_ne];
        only 2: specialize (address_eqb_spec addr to) as [<- | addr_to_ne].
        * (* case: addr = from *)
          now eapply try_transfer_remove_empty_balances in receive_some.
        * (* case: addr = to *)
          now eapply try_transfer_remove_empty_balances in receive_some.
        * (* case: addr is not related to transaction *)
          eapply try_transfer_preserves_other_balances in receive_some; eauto.
          now rewrite <- receive_some in addr_some.
      + now erewrite <- try_approve_preserves_balances in addr_some.
      + destruct m.
        specialize (address_eqb_spec addr target) as [<- | addr_from_ne].
        * (* case: addr = target *)
          now eapply try_mint_or_burn_remove_empty_balances in receive_some.
        * (* case: addr is not related to transaction *)
          eapply try_mint_or_burn_preserves_other_balances in receive_some; eauto.
          now rewrite <- receive_some in addr_some.
      + apply try_get_allowance_preserves_state in receive_some.
        now subst.
      + apply try_get_balance_preserves_state in receive_some.
        now subst.
      + apply try_get_total_supply_preserves_state in receive_some.
        now subst.
      + contract_simpl.
  Qed.

  (** The [allowances] map never stores entries of zero *)
  Lemma zero_allowances_removed : forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      forall sender from n, FMap.find (sender, from) (allowances cstate) = Some n -> n > 0.
  Proof.
    intros * reach deployed.
    apply (lift_contract_state_prop contract);
      intros *; auto; clear reach deployed bstate caddr.
    - intros init_some * addr_some. cbn in *.
      erewrite init_allowances_correct in addr_some by eauto.
      now rewrite FMap.find_empty in addr_some.
    - intros IH receive_some * addr_some.
      unfold Blockchain.receive in receive_some.
      simpl in receive_some.
      destruct msg. destruct m.
      + destruct t.
        specialize (address_eqb_spec ctx.(ctx_from) from) as [<- | addr_from_ne];
        only 1: specialize (address_eqb_spec from0 sender) as [<- | addr_from_ne].
        * now eapply try_transfer_remove_empty_allowances in receive_some.
        * eapply try_transfer_preserves_other_allowances in receive_some.
        -- now rewrite <- receive_some in addr_some.
        -- intros HH.
            now inversion HH.
        * eapply try_transfer_preserves_other_allowances in receive_some.
        -- now rewrite <- receive_some in addr_some.
        -- intros HH.
            now inversion HH.
      + destruct a.
        specialize (address_eqb_spec ctx.(ctx_from) sender) as [<- | addr_from_ne];
        only 1: specialize (address_eqb_spec spender from) as [<- | addr_from_ne].
        * now eapply try_approve_remove_empty_allowances in receive_some.
        * eapply try_approve_preserves_other_allowances in receive_some.
        -- now rewrite <- receive_some in addr_some.
        -- intros HH.
            now inversion HH.
        * eapply try_approve_preserves_other_allowances in receive_some.
        -- now rewrite <- receive_some in addr_some.
        -- intros HH.
            now inversion HH.
      + apply try_mint_or_burn_preserves_allowances in receive_some.
        now rewrite receive_some in *.
      + apply try_get_allowance_preserves_state in receive_some.
        now subst.
      + apply try_get_balance_preserves_state in receive_some.
        now subst.
      + apply try_get_total_supply_preserves_state in receive_some.
        now subst.
      + contract_simpl.
  Qed.



  (** ** Total supply correct *)

  Open Scope Z_scope.

  (** [total_supply] is equal to the initial tokens + minted tokens - burned tokens *)
  Lemma total_supply_correct : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate depinfo inc_calls,
      contract_state bstate caddr = Some cstate /\
      deployment_info Setup trace caddr = Some depinfo /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      let initial_tokens := initial_pool (deployment_setup depinfo) in
      Z.of_N cstate.(total_supply) = (Z.of_N initial_tokens) + sumZ (fun callInfo => mintedOrBurnedTokens callInfo.(call_msg)) (filter (callFrom cstate.(admin)) inc_calls).
  Proof.
    contract_induction;
      intros; auto.
    - now cbn in *; erewrite init_total_supply_correct by eauto.
    - instantiate (CallFacts := fun _ ctx state _ _ =>
        total_supply state = sum_balances state /\
        ctx_from ctx <> ctx_contract_address ctx).
      destruct facts as (balances_eq_total_supply & _).
      unfold callFrom in *.
      unfold Blockchain.receive in receive_some.
      erewrite <- admin_constant; eauto.
      simpl in *.
      destruct msg. destruct m.
      + erewrite <- try_transfer_preserves_total_supply; eauto.
        now destruct_address_eq; cbn; rewrite IH.
      + erewrite <- try_approve_preserves_total_supply; eauto.
        now destruct_address_eq; cbn; rewrite IH.
      + cbn.
        apply try_mint_or_burn_total_supply_correct in receive_some as state_eq.
        * rewrite <- state_eq, IH.
          specialize (try_mint_or_burn_is_some) as (_ & (_ & <- & _)); eauto.
          rewrite address_eq_refl.
          cbn. lia.
        * rewrite balances_eq_total_supply.
          apply balance_le_sum_balances.
      + eapply try_get_allowance_preserves_state in receive_some.
        now destruct_address_eq; subst.
      + eapply try_get_balance_preserves_state in receive_some.
        now destruct_address_eq; subst.
      + eapply try_get_total_supply_preserves_state in receive_some.
        now destruct_address_eq; subst.
      + contract_simpl.
    - now destruct facts.
    - solve_facts.
      split.
      + specialize sum_balances_eq_total_supply as (? & ? & ?); eauto.
        now constructor.
        easy.
      + rewrite deployed in *.
        match goal with
        | H : Some ?x = Some _ |- _ => inversion H; subst x; clear H
        end.
        eapply no_self_calls; eauto.
        now constructor.
  Qed.

  Instance LqtFA12Token : LqtTokenInterface :=
    { lqt_contract := DEX2LQT.contract;
      lqt_total_supply_correct := total_supply_correct }.

  Arguments lqt_contract {_ _ _ _} _.
  Arguments lqt_total_supply_correct {_ _ _ _} _.

End Theories.
