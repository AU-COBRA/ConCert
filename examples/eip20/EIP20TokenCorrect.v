(** * EIP20 Token Implementation *)
(**
  This file contains correctness proofs of the EIP20 token implementation.
*)
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Examples.EIP20 Require Import EIP20Token.



(** * Properties *)
Section Theories.
  Context {BaseTypes : ChainBase}.
  Open Scope N_scope.
  Open Scope bool.

  (** ** EIP20 functions not payable *)

  (** [receive] only returns Some if the sender amount is zero *)
  Lemma EIP20_not_payable : forall prev_state new_state chain ctx msg new_acts,
    receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
      ((ctx_amount ctx) <= 0)%Z.
  Proof.
    intros * receive_some.
    unfold receive in receive_some.
    destruct_match eqn:amount in receive_some.
    - (* case: ctx_amount > 0 *)
      discriminate.
    - (* case: ctx_amount <= 0 *)
      now rewrite Z.gtb_ltb, Z.ltb_ge in amount.
  Qed.

  (** Lemma for simplifying the [receive] function by eliminating the case
      where sender amount is larger than zero *)
  Lemma receive_not_payable : forall prev_state new_state chain ctx msg new_acts,
    receive chain ctx prev_state (Some msg) = Ok (new_state, new_acts) ->
      match msg with
      | transfer to amount => (try_transfer (ctx_from ctx) to amount prev_state) >>= (fun new_state : State => Ok (new_state, []))
      | transfer_from from to amount =>
          (try_transfer_from (ctx_from ctx) from to amount prev_state) >>= (fun new_state : State => Ok (new_state, []))
      | approve delegate amount =>
          (try_approve (ctx_from ctx) delegate amount prev_state) >>= (fun new_state : State => Ok (new_state, []))
      end = Ok (new_state, new_acts).
  Proof.
    intros * receive_some.
    apply EIP20_not_payable in receive_some as amount_zero.
    unfold receive in receive_some.
    rewrite <- Z.ltb_ge, <- Z.gtb_ltb in amount_zero.
    now rewrite amount_zero in receive_some.
  Qed.



  (** ** EIP20 functions produce no acts *)

  (** [receive] never produces any [new_acts] *)
  Lemma EIP20_no_acts : forall prev_state new_state chain ctx msg new_acts,
    receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
      new_acts = [].
  Proof.
    intros * receive_some.
    unfold receive, option_map in receive_some.
    repeat (destruct_match in receive_some; cbn in *); easy.
  Qed.

  Lemma receive_no_acts : forall prev_state new_state chain ctx msg new_acts,
    receive chain ctx prev_state (Some msg) = Ok (new_state, new_acts) ->
      receive chain ctx prev_state (Some msg) = Ok (new_state, []).
  Proof.
    intros.
    now erewrite <- EIP20_no_acts.
  Qed.



  (** Default entrypoint always fail *)
  Lemma default_none : forall prev_state chain ctx,
    receive chain ctx prev_state None = Err default_error.
  Proof.
    intros.
    unfold receive.
    now destruct_match.
  Qed.



  (* begin hide *)
  (* FMap partial alter is FMap add *)
  Lemma add_is_partial_alter_plus : forall (account : Address) amount (balances : FMap Address N) (f : N -> N),
    FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) account balances =
    FMap.add account (with_default 0 (FMap.find account balances) + amount) balances.
  Proof.
    intros.
    now apply fin_maps.partial_alter_ext.
  Qed.

  Lemma increment_balanace_is_partial_alter_plus : forall (addr : Address) amount (m : FMap Address N),
    increment_balance m addr amount =
    FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) addr m.
  Proof.
    intros.
    unfold increment_balance, AddressMap.add, AddressMap.find.
    rewrite add_is_partial_alter_plus by auto.
    destruct_match eqn:addr_in_map;
      now setoid_rewrite addr_in_map.
  Qed.



  (* Tactic to simplify proof steps *)
  Ltac eip_simpl :=
    match goal with
    | H : receive _ _ _ (Some _) = Ok (_, _) |- _ =>
      apply receive_no_acts, receive_not_payable in H; cbn in H
    | |- receive _ _ _ (Some _) = Ok (_, _) =>
      apply receive_no_acts, receive_not_payable; cbn
    | H : context[try_transfer] |- _ => unfold try_transfer in H
    | H : context[try_transfer_from] |- _ => unfold try_transfer_from in H
    | H : context[try_approve] |- _ => unfold try_approve in H
    | H : context[error] |- _ => unfold error in H
    | |- context[try_transfer] => unfold try_transfer
    | |- context[try_transfer_from] => unfold try_transfer_from
    | |- context[try_approve] => unfold try_approve
    | |- context[error] => unfold error
    end.

  Ltac address_map_convert :=
    match goal with
    | H : context [ AddressMap.find _ _ ] |- _ => rewrite AddressMap_find_convertible in H
    | H : context [ AddressMap.add _ _ _ ] |- _ => rewrite AddressMap_add_convertible in H
    | H : context [ increment_balance _ _ _ ] |- _ => rewrite increment_balanace_is_partial_alter_plus in H
    | |- context [ AddressMap.find _ _ ] => rewrite AddressMap_find_convertible
    | |- context [ AddressMap.add _ _ _ ] => rewrite AddressMap_add_convertible
    | |- context [ increment_balance _ _ _ ] => rewrite increment_balanace_is_partial_alter_plus
    end.

  Tactic Notation "contract_simpl" :=
    repeat (
      try eip_simpl;
      try address_map_convert;
      try contract_simpl_step @receive @init).

  Ltac FMap_simpl_step :=
    match goal with
      | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => setoid_rewrite FMap.find_add
      | H : FMap.find ?t ?m = Some _ |- FMap.find ?t ?m = Some _ => cbn; rewrite H; f_equal; lia
      | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => setoid_rewrite FMap.find_add_ne; eauto
      | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => setoid_rewrite FMap.find_add_ne; eauto
      | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] => setoid_rewrite FMap.elements_add_existing; eauto
      | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => setoid_rewrite FMap.add_add
      | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => setoid_rewrite FMap.elements_add; eauto
      | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
      | |- context [ FMap.find ?x (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter
      | H : ?x' <> ?x |- context [ FMap.find ?x' (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter_ne; auto
      | H : ?x <> ?x' |- context [ FMap.find ?x' (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter_ne
      | H : context [ AddressMap.find _ _ ] |- _ => rewrite AddressMap_find_convertible in H
      | H : context [ AddressMap.add _ _ _ ] |- _ => rewrite AddressMap_add_convertible in H
      | H : context [ increment_balance _ _ _ ] |- _ => rewrite increment_balanace_is_partial_alter_plus in H
      | |- context [ AddressMap.find _ _ ] => rewrite AddressMap_find_convertible
      | |- context [ AddressMap.add _ _ _ ] => rewrite AddressMap_add_convertible
      | |- context [ increment_balance _ _ _ ] => rewrite increment_balanace_is_partial_alter_plus
    end.

  Tactic Notation "FMap_simpl" := repeat (FMap_simpl_step; cbn).

  Ltac destruct_message :=
    repeat match goal with
    | msg : option Msg |- _ => destruct msg
    | msg : Msg |- _ => destruct msg
    | H : Blockchain.receive _ _ _ _ None = Ok _ |- _ => now contract_simpl
    | H : receive _ _ _ None = Ok _ |- _ => now contract_simpl
    end.



  (* sumN function *)
  (* sumN of balances is the same after transfer changes if sender has enough balance *)
  Lemma sumN_FMap_add_sub : forall from to amount (balances : FMap Address N),
    amount <= with_default 0 (FMap.find from balances) ->
      (sumN (fun '(_, v) => v) (FMap.elements balances)) =
      (sumN(fun '(_, v) => v)
        (FMap.elements
            (FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) to
              (FMap.add from (with_default 0 (FMap.find from balances) - amount) balances)))).
  Proof.
    intros from to amount balances from_enough_balance.
    rewrite add_is_partial_alter_plus; auto.
    edestruct (address_eqb from to) eqn:from_to_eq;
      destruct FMap.find eqn:from_prev;
      destruct_address_eq; try discriminate; subst; cbn in *;
      repeat match goal with
      | H : _ <= 0 |- _ => apply N.lt_eq_cases in H as [H | H]; try lia; subst
      | |- context [ with_default _ (FMap.find to balances) ] => destruct (FMap.find to balances) eqn:to_prev; cbn
      | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => rewrite FMap.find_add
      | H : FMap.find ?t ?m = Some _ |- FMap.find ?t ?m = Some _ => cbn; rewrite H; f_equal; lia
      | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
      | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
      | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add_existing; eauto
      | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => rewrite FMap.add_add
      | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add; eauto
      | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
      | H : FMap.find ?x ?m = Some _ |- context [ sumN _ ((_, _) :: FMap.elements (FMap.remove ?x ?m)) ] => rewrite fin_maps.map_to_list_delete; auto
      | H : FMap.find ?x _ = Some ?n |- context [ sumN _ ((?x, ?n) :: FMap.elements (FMap.remove ?x _)) ] => rewrite fin_maps.map_to_list_delete; auto
      | H : FMap.find ?x _ = Some ?n |- context [ sumN _ ((?x, ?n) :: (_, _) :: FMap.elements (FMap.remove ?x _)) ] => rewrite sumN_swap, fin_maps.map_to_list_delete; auto
      | |- context [ _ + 0 ] => rewrite N.add_0_r
      | |- context [ 0 + _ ] => rewrite N.add_0_l
      | |- context [ sumN _ ((?t, ?n + ?m) :: _) ] => erewrite sumN_split with (x := (t, n)) (y := (_, m)) by lia
      | |- context [ sumN _ ((_, ?n) :: (_, ?m - ?n) :: _) ] => erewrite <- sumN_split with (z := (_, n + m - n)) by lia
    end.
    Unshelve. eauto.
  Qed.

  (* end hide *)



  (** ** Expected behaviour of EIP20 functions *)
  Definition transfer_balance_update_correct old_state new_state from to tokens :=
    let get_balance addr state := with_default 0 (FMap.find addr state.(balances)) in
    let from_balance_before := get_balance from old_state in
    let to_balance_before := get_balance to old_state in
    let from_balance_after := get_balance from new_state in
    let to_balance_after := get_balance to new_state in
    (** if the transfer is a self-transfer, balances should remain unchained *)
    if address_eqb from to
    then
      (from_balance_before =? from_balance_after) &&
      (to_balance_before =? to_balance_after)
    else
      (from_balance_before =? from_balance_after + tokens) &&
      (to_balance_before + tokens =? to_balance_after).

  Definition transfer_from_allowances_update_correct (old_state new_state : State) (from delegate : Address) (tokens : TokenValue) :=
    let delegate_allowance_before := get_allowance old_state from delegate in
    let delegate_allowance_after := get_allowance new_state from delegate in
      delegate_allowance_before =? delegate_allowance_after + tokens.

  Definition approve_allowance_update_correct (new_state : State) (from delegate : Address) (tokens : TokenValue) :=
    let delegate_allowance_after := get_allowance new_state from delegate in
      delegate_allowance_after =? tokens.



  (** ** Transfer correct *)

  (** [try_transfer] correctly moves [amount] from [sender] to [to] *)
  Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx to amount new_acts,
    receive chain ctx prev_state (Some (transfer to amount)) = Ok (new_state, new_acts) ->
    transfer_balance_update_correct prev_state new_state ctx.(ctx_from) to amount = true.
  Proof.
    intros * receive_some.
    unfold transfer_balance_update_correct.
    contract_simpl.
    rename H0 into sender_enough_balance.
    apply N.ltb_ge in sender_enough_balance.
    destruct_address_eq; destruct (FMap.find (ctx_from ctx) (balances prev_state)) eqn:from_prev;
      try congruence; subst; try (rewrite from_prev || setoid_rewrite from_prev);
      clear from_prev new_acts chain; cbn in *.
      - (* case: from = to && find from = Some n && amount <= n *)
        FMap_simpl.
        now rewrite N.sub_add, N.eqb_refl.
      - (* case: from = to && find from = None && amount = 0 *)
        apply N.lt_eq_cases in sender_enough_balance as []; [lia | subst].
        now FMap_simpl.
      - (* case: from <> to && find from = Some n && amount <= n *)
        FMap_simpl.
        rewrite N.sub_add; auto.
        now rewrite !N.eqb_refl.
      - (* case: from <> to && find from = None && amount = 0 *)
        apply N.lt_eq_cases in sender_enough_balance as []; [lia | subst].
        FMap_simpl.
        apply N.eqb_refl.
  Qed.

  (** [try_transfer] does not change the total supply of tokens *)
  Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx to amount new_acts,
    receive chain ctx prev_state (Some (transfer to amount)) = Ok (new_state, new_acts) ->
      (total_supply prev_state) = (total_supply new_state).
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_transfer] does not change allowances *)
  Lemma try_transfer_preserves_allowances : forall prev_state new_state chain ctx to amount new_acts,
    receive chain ctx prev_state (Some (transfer to amount)) = Ok (new_state, new_acts) ->
      (allowances prev_state) = (allowances new_state).
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_transfer] only modifies the [sender] and [to] balances *)
  Lemma try_transfer_preserves_other_balances : forall prev_state new_state chain ctx to amount new_acts,
    receive chain ctx prev_state (Some (transfer to amount)) = Ok (new_state, new_acts) ->
      forall account, account <> (ctx_from ctx) -> account <> to ->
        FMap.find account (balances prev_state) = FMap.find account (balances new_state).
  Proof.
    intros * receive_some account account_not_sender account_not_receiver.
    contract_simpl.
    cbn.
    FMap_simpl.
  Qed.

  (** If the requirements are met then receive on transfer msg must succeed and
      if receive on transfer msg succeeds then requirements must hold *)
  Lemma try_transfer_is_some : forall state chain ctx to amount,
    (ctx_amount ctx <= 0)%Z /\
    amount <= with_default 0 (FMap.find (ctx_from ctx) (balances state))
      <-> isOk (receive chain ctx state (Some (transfer to amount))) = true.
  Proof.
    intros.
    split.
    - intros (amount_positive & sender_enough_balance);
      contract_simpl; destruct_match eqn:amount_from; auto.
      + now propify.
      + rewrite <- N.ltb_ge in sender_enough_balance.
        now setoid_rewrite sender_enough_balance.
    - intros receive_some.
      contract_simpl.
      destruct_match eqn:amount_positive in receive_some;
        try now inversion receive_some.
      destruct_match eqn:amount_from in receive_some.
      + destruct_match eqn:amount_from_ in amount_from.
        * discriminate.
        * now propify.
      + now propify.
  Qed.



  (** ** Transfer_from correct *)

  (** [try_transfer_from] correctly updates balance and allowance *)
  Lemma try_transfer_from_balance_correct : forall prev_state new_state chain ctx from to amount new_acts,
    receive chain ctx prev_state (Some (transfer_from from to amount)) = Ok (new_state, new_acts) ->
    transfer_balance_update_correct prev_state new_state from to amount = true /\
    transfer_from_allowances_update_correct prev_state new_state from ctx.(ctx_from) amount = true.
  Proof.
    intros * receive_some.
    unfold transfer_balance_update_correct,
      transfer_from_allowances_update_correct,
      get_allowance.
    contract_simpl.
    rename H0 into from_allowances.
    rename H1 into sender_allowance.
    rewrite result_of_option_eq_some in from_allowances.
    rewrite result_of_option_eq_some in sender_allowance.
    propify.
    destruct H2 as (sender_enough_allowance & from_enough_balance).
    split.
      + (* proof of balance updated correct *)
      destruct_address_eq;
        destruct (FMap.find from (balances prev_state)) eqn:from_bal_prev;
        subst; try (rewrite from_bal_prev || setoid_rewrite from_bal_prev); cbn in *.
        * (* case: from = to && find from = Some n && amount <= n *)
          FMap_simpl.
          now rewrite N.sub_add, N.eqb_refl.
        * (* case: from = to && find from = None && amount = 0 *)
          apply N.lt_eq_cases in from_enough_balance as []; [lia | subst].
          now FMap_simpl.
        * (* case: from <> to && find from = Some n && amount <= n *)
          FMap_simpl.
          rewrite N.sub_add by auto.
          now rewrite ?N.eqb_refl.
        * (* case: from <> to && find from = None && amount = 0 *)
          apply N.lt_eq_cases in from_enough_balance as []; [lia | subst].
          FMap_simpl.
          apply N.eqb_refl.
      + (* proof of allowances updated correct *)
        rewrite from_allowances.
        cbn.
        setoid_rewrite sender_allowance.
        FMap_simpl.
        now rewrite N.sub_add.
  Qed.

  (** [try_transfer_from] does not change total supply of tokens *)
  Lemma try_transfer_from_preserves_total_supply : forall prev_state new_state chain ctx from to amount new_acts,
    receive chain ctx prev_state (Some (transfer_from from to amount)) = Ok (new_state, new_acts) ->
      (total_supply prev_state) = (total_supply new_state).
  Proof.
    intros * receive_some.
    now contract_simpl.
  Qed.

  (** [try_transfer_from] only changes [from] and [to] balances *)
  Lemma try_transfer_from_preserves_other_balances : forall prev_state new_state chain ctx from to amount new_acts,
    receive chain ctx prev_state (Some (transfer_from from to amount)) = Ok (new_state, new_acts) ->
      forall account, account <> from -> account <> to ->
        FMap.find account (balances prev_state) = FMap.find account (balances new_state).
  Proof.
    intros * receive_some account account_not_from account_not_to.
    contract_simpl.
    cbn.
    FMap_simpl.
  Qed.

  (** [try_transfer_from] only changes allowance map of [from] *)
  Lemma try_transfer_from_preserves_other_allowances : forall prev_state new_state chain ctx from to amount new_acts,
    receive chain ctx prev_state (Some (transfer_from from to amount)) = Ok (new_state, new_acts) ->
      forall account, account <> from ->
        FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
  Proof.
    intros * receive_some account account_not_from.
    contract_simpl.
    cbn.
    FMap_simpl.
  Qed.

  (** [try_transfer_from] only changes allowance of [sender] *)
  Lemma try_transfer_from_preserves_other_allowance : forall prev_state new_state chain ctx from to amount new_acts,
    receive chain ctx prev_state (Some (transfer_from from to amount)) = Ok (new_state, new_acts) ->
      forall account, account <> (ctx_from ctx) ->
        get_allowance prev_state from account = get_allowance new_state from account.
  Proof.
    intros * receive_some account account_not_sender.
    unfold get_allowance.
    contract_simpl.
    rewrite result_of_option_eq_some in H0.
    rewrite result_of_option_eq_some in H1.
    rewrite H0.
    cbn.
    FMap_simpl.
  Qed.

  Set Keyed Unification.

  (** If the requirements are met then receive on transfer_from msg must succeed and
      if receive on transfer_from msg succeeds then requirements must hold *)
  Lemma try_transfer_from_is_some : forall state chain ctx from to amount,
    let get_allowance_ account := FMap.find account (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances state))) in
    (ctx_amount ctx >? 0)%Z = false ->
    isSome (FMap.find from (allowances state)) = true
    /\ isSome (get_allowance_ (ctx_from ctx)) = true
    /\ amount <= with_default 0 (FMap.find from (balances state))
    /\ amount <= with_default 0 (get_allowance_ (ctx_from ctx))
      <-> isOk (receive chain ctx state (Some (transfer_from from to amount))) = true.
  Proof.
    intros * sender_amount_zero.
    split; contract_simpl; rewrite sender_amount_zero in *;
      unfold get_allowance_; clear get_allowance_; cbn.
    - intros (from_allowances_some &
              sender_allowance &
              from_enough_balance%N.ltb_ge &
              sender_enough_allowance%N.ltb_ge).
      destruct_match eqn:receive_some; cbn in *; auto.
      destruct_match eqn:allowances_ctx in receive_some;
        try (apply result_of_option_eq_none in allowances_ctx; now rewrite allowances_ctx in from_allowances_some).
      rewrite result_of_option_eq_some in allowances_ctx.
      rewrite allowances_ctx in *.
      clear from_allowances_some allowances_ctx.
      cbn in *.
      destruct_match eqn:allowance_ctx in receive_some;
        try (apply result_of_option_eq_none in allowance_ctx; now rewrite allowance_ctx in sender_allowance).
      rewrite result_of_option_eq_some in allowance_ctx.
      rewrite allowance_ctx in *.
      clear allowance_ctx sender_allowance.
      destruct_match eqn:amount_from in receive_some; try discriminate.
      rewrite from_enough_balance in amount_from.
      now rewrite sender_enough_allowance in amount_from.
    - intros receive_some.
      destruct_match eqn:H in receive_some; try discriminate.
      destruct_match eqn:allowances_ctx in H; try discriminate.
      destruct_match eqn:allowance_ctx in H; try discriminate.
      destruct_match eqn:amount_from in H; try discriminate.
      cbn in *.
      propify.
      rewrite result_of_option_eq_some in allowances_ctx.
      rewrite result_of_option_eq_some in allowance_ctx.
      now rewrite allowances_ctx, allowance_ctx.
  Qed.



  (** ** Approve correct *)

  (** [try_approve] correctly replaces allowance *)
  Lemma try_approve_allowance_correct : forall prev_state new_state chain ctx delegate amount new_acts,
    receive chain ctx prev_state (Some (approve delegate amount)) = Ok (new_state, new_acts) ->
    approve_allowance_update_correct new_state ctx.(ctx_from) delegate amount = true.
  Proof.
    intros * receive_some.
    unfold approve_allowance_update_correct, get_allowance.
    contract_simpl.
    destruct_match eqn:from_allowance in H;
      inversion H; cbn;
      FMap_simpl; apply N.eqb_refl.
  Qed.

  (** [try_approve] does not change total supply of tokens *)
  Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx delegate amount new_acts,
    receive chain ctx prev_state (Some (approve delegate amount)) = Ok (new_state, new_acts) ->
      (total_supply prev_state) = (total_supply new_state).
  Proof.
    intros * receive_some.
    contract_simpl.
    destruct_match in H;
      now inversion H.
  Qed.

  (** [try_approve] does not change balances *)
  Lemma try_approve_preserves_balances : forall prev_state new_state chain ctx delegate amount new_acts,
    receive chain ctx prev_state (Some (approve delegate amount)) = Ok (new_state, new_acts) ->
      (balances prev_state) = (balances new_state).
  Proof.
    intros * receive_some.
    contract_simpl.
    destruct_match in H;
      now inversion H.
  Qed.

  (** [try_approve] does not change allowances map of other addresses *)
  Lemma try_approve_preserves_other_allowances : forall prev_state new_state chain ctx delegate amount new_acts,
    receive chain ctx prev_state (Some (approve delegate amount)) = Ok (new_state, new_acts) ->
      forall account, account <> (ctx_from ctx) ->
        FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
  Proof.
    intros * receive_some account account_not_sender.
    contract_simpl.
    destruct_match in H;
      inversion H;
      cbn; FMap_simpl.
  Qed.

  (** [try_approve] does not change allowance of other addresses *)
  Lemma try_approve_preserves_other_allowance : forall prev_state new_state chain ctx delegate amount new_acts,
    receive chain ctx prev_state (Some (approve delegate amount)) = Ok (new_state, new_acts) ->
      forall account, account <> delegate ->
        get_allowance prev_state (ctx_from ctx) account = get_allowance new_state (ctx_from ctx) account.
  Proof.
    intros * receive_some account account_not_delegate.
    contract_simpl.
    unfold get_allowance.
    destruct_match eqn:allowances_from in H;
      inversion H;
      cbn; FMap_simpl.
  Qed.

  (** If the requirements are met then receive on approve msg must succeed and
      if receive on approve msg succeeds then requirements must hold *)
  Lemma try_approve_is_some : forall state chain ctx delegate amount,
    (ctx_amount ctx >? 0)%Z = false <-> isOk (receive chain ctx state (Some (approve delegate amount))) = true.
  Proof.
    split; contract_simpl.
    - intros sender_amount_zero.
      rewrite sender_amount_zero.
      destruct_match eqn:H; auto.
      destruct_match in H; discriminate.
    - intros receive_some.
      now destruct_match in receive_some.
  Qed.



  (** ** EIP20 functions preserve sum of balances *)

  (** Sum of all balances remain the same after processing transfer msg *)
  Lemma try_transfer_preserves_balances_sum : forall prev_state new_state chain ctx to amount new_acts,
    receive chain ctx prev_state (Some (transfer to amount)) = Ok (new_state, new_acts) ->
      (sum_balances prev_state) = (sum_balances new_state).
  Proof.
    intros * receive_some.
    contract_simpl.
    propify.
    unfold sum_balances. cbn.
    now apply sumN_FMap_add_sub.
  Qed.

  (** Sum of all balances remain the same after processing transfer_from msg *)
  Lemma try_transfer_from_preserves_balances_sum : forall prev_state new_state chain ctx from to amount new_acts,
    receive chain ctx prev_state (Some (transfer_from from to amount)) = Ok (new_state, new_acts) ->
      (sum_balances prev_state) = (sum_balances new_state).
  Proof.
    intros * receive_some.
    contract_simpl.
    propify.
    unfold sum_balances. cbn.
    now apply sumN_FMap_add_sub.
  Qed.

  (** Sum of all balances remain the same after approve transfer msg *)
  Lemma try_approve_preserves_balances_sum : forall prev_state new_state chain ctx delegate amount new_acts,
    receive chain ctx prev_state (Some (approve delegate amount)) = Ok (new_state, new_acts) ->
      (sum_balances prev_state) = (sum_balances new_state).
  Proof.
    intros * receive_some.
    contract_simpl.
    destruct_match in H;
      now inversion H.
  Qed.



  (** ** Contract never produces any actions *)
  Lemma outgoing_acts_nil : forall (bstate : ChainState) (caddr : Address),
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    outgoing_acts bstate caddr = [].
  Proof.
    intros * reach deployed.
    apply (lift_outgoing_acts_nil contract); eauto.
    intros.
    unfold Blockchain.receive in *.
    now eapply EIP20_no_acts.
  Qed.



  (** ** Total supply always equals initial supply *)
  Lemma total_supply_eq_init_supply bstate caddr (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists deploy_info cstate,
      deployment_info _ trace caddr = Some deploy_info
      /\ contract_state bstate caddr = Some cstate
      /\ let init_supply := init_amount deploy_info.(deployment_setup) in
        init_supply = total_supply cstate.
  Proof.
    apply (lift_dep_info_contract_state_prop contract); intros *.
    - intros init_some.
      now inversion init_some.
    - intros IH receive_some.
      destruct_message.
      + now apply try_transfer_preserves_total_supply in receive_some.
      + now apply try_transfer_from_preserves_total_supply in receive_some.
      + now apply try_approve_preserves_total_supply in receive_some.
  Qed.



  (** ** Sum of balances always equals total supply *)
  Lemma sum_balances_eq_total_supply bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate
      /\ (total_supply cstate) = (sum_balances cstate).
  Proof.
    intros.
    apply (lift_contract_state_prop contract); eauto; intros *.
    - intros init_some.
      inversion_clear init_some.
      unfold sum_balances.
      setoid_rewrite FMap.elements_add; auto.
      setoid_rewrite FMap.elements_empty. cbn. lia.
    - intros IH receive_some.
      unfold Blockchain.receive in *.
      cbn in *.
      destruct_message.
      + now erewrite try_transfer_preserves_balances_sum,
          try_transfer_preserves_total_supply in IH.
      + now erewrite try_transfer_from_preserves_balances_sum,
          try_transfer_from_preserves_total_supply in IH.
      + now erewrite try_approve_preserves_balances_sum,
          try_approve_preserves_total_supply in IH.
  Qed.

End Theories.
