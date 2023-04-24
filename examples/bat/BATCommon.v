(** * Basic Attention Token *)
(** This file contains type definitions, utility functions and lemmas for the Basic Attention Token contract.

    The implementation of the Basic Attention Token is a ported of
    https://github.com/brave-intl/basic-attention-token-crowdsale/blob/66c886cc4bfb0493d9e7980f392ca7921ef1e7fc/contracts/BAToken.sol

    Definitions and lemmas defined in this file are used in three different implementations of the Basic Attention Token contract.
    - [ConCert.Execution.Examples.BAT] Classical implementation
    - [ConCert.Execution.Examples.BATFixed] An implementation of the Basic Attention Token contract that fixes some bugs in the original implementation
    - [ConCert.Execution.Examples.BATAltFix] An alternative implementation of the Basic Attention Token contract that fixes some bugs in the original implementation

    The BAT contract is a combination of a EIP20 token contract and a crowdsale contract.
    The types and definitions in this file extends the EIP20 contract implemented in [ConCert.Execution.Examples.EIP20Token].
*)
From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import ZArith.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Examples.EIP20 Require EIP20Token.
Import ListNotations.



Section BATCommon.
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  Definition TokenValue := EIP20Token.TokenValue.

  Inductive Msg :=
    (** Message types from the EIP20/ERC20 Standard Token: *)
    | tokenMsg : EIP20Token.Msg -> Msg
    (** Message types specific for BAT: *)
    (** create_tokens accepts the currency of the chain and converts
        it to BAT according to the pre-specified exchange rate *)
    | create_tokens : Msg
    (** finalize ends the funding period and sends the chain currency to
        the pre-specified fund deposit address. Only callable by this address *)
    | finalize : Msg
    (** Allows contributors to recover their ether in the case of a failed funding campaign. *)
    | refund : Msg.

  Record State :=
    build_state {
      (** State from EIP20Token: *)
      token_state       : EIP20Token.State;
      (** State for BAT: *)
      initSupply        : N;
      fundDeposit    		: Address;
      batFundDeposit 		: Address;
      isFinalized    		: bool;
      fundingStart   		: nat;
      fundingEnd	 	 		: nat;
      tokenExchangeRate : N;
      tokenCreationCap 	: N;
      tokenCreationMin 	: N;
    }.

  Record Setup :=
    build_setup {
      _batFund						: N;
      _fundDeposit 				: Address;
      _batFundDeposit 		: Address;
      _fundingStart	  		: nat;
      _fundingEnd					: nat;
      (** In the reference implementation, the fields below are constants,
          but we allow setting them at initialization, in order to test out different values. *)
      _tokenExchangeRate  : N;
      _tokenCreationCap 	: N;
      _tokenCreationMin 	: N;
    }.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (* begin hide *)
  MetaCoq Run (make_setters State).
  MetaCoq Run (make_setters Setup).

  Section Serialization.

  Global Instance setup_serializable : Serializable Setup :=
    Derive Serializable Setup_rect <build_setup>.

  Global Instance msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect <tokenMsg, create_tokens, finalize, refund>.

  Global Instance state_serializable : Serializable State :=
    Derive Serializable State_rect <build_state>.

  End Serialization.
  (* end hide *)

  Definition total_supply (state : State) := state.(token_state).(EIP20Token.total_supply).
  Definition balances (state : State) := state.(token_state).(EIP20Token.balances).
  Definition allowances (state : State) := state.(token_state).(EIP20Token.allowances).
  Definition transfer t a := tokenMsg (EIP20Token.transfer t a).
  Definition transfer_from f t a := tokenMsg (EIP20Token.transfer_from f t a).
  Definition approve d a := tokenMsg (EIP20Token.approve d a).

  Definition serializeMsg msg := (@serialize Msg _) msg.
  Definition serializeState state := (@serialize State _) state.
  Definition serializeSetup setup := (@serialize Setup _) setup.

  Global Coercion serializeMsg : Msg >-> SerializedValue.
  Global Coercion serializeState : State >-> SerializedValue.
  Global Coercion serializeSetup : Setup >-> SerializedValue.

  Definition finalize_act cstate caddr : Action :=
    build_act (fundDeposit cstate) (fundDeposit cstate) (act_call caddr 0 finalize).

  Definition deploy_act setup contract from : Action :=
    build_act from from (act_deploy 0 contract setup).

  (** Utility definitions and lemmas *)
  Open Scope N_scope.
  (** Stronger version of N.mod_le.
      N.mod_le requires that b <> 0, however
      it is possible to prove the same without
      that assumption *)
  Lemma N_mod_le : forall n m,
    n mod m <= n.
  Proof.
    intros.
    edestruct N.le_gt_cases.
    - unfold N.modulo, N.div_eucl.
      destruct_match.
      + apply N.le_0_l.
      + destruct_match.
        * apply N.le_refl.
        * eapply N.le_trans.
          now apply N.lt_le_incl, N.pos_div_eucl_remainder.
          apply H.
    - rewrite N.lt_eq_cases.
      right.
      now apply N.mod_small.
  Qed.

  Lemma N_sub_add_mod : forall n m p,
    n <= p -> p - n + n mod m <= p.
  Proof.
    intros.
    specialize (N_mod_le n m) as mod_le.
    apply N.le_trans with (m := p - n + n).
    - lia.
    - now rewrite N.sub_add.
  Qed.

  Lemma N_div_mod : forall n m,
    n / m * m = n - n mod m.
  Proof.
    intros.
    symmetry.
    apply N.add_sub_eq_r.
    symmetry.
    rewrite N.mul_comm.
    apply N.div_mod'.
  Qed.

  Lemma N_add_le : forall n m p,
    n <= m -> n <= p + m.
  Proof.
  lia.
  Qed.

  Lemma N_le_add_distr : forall n m p,
  n + m <= p -> n <= p.
  Proof.
    lia.
  Qed.

  Lemma N_le_sub : forall n m p,
    p <= m ->
    n <= m - p ->
    n + p <= m.
  Proof.
    lia.
  Qed.

  Lemma N_div_mul_le : forall n m,
    (n / m) * m <= n.
  Proof.
    intros.
    erewrite N.div_mod', N.mul_comm.
    apply N.le_add_r.
  Qed.

  Lemma N_sub_mod_le : forall n m,
    n - n mod m <= n.
  Proof.
    intros.
    rewrite <- N_div_mod.
    apply N_div_mul_le.
  Qed.

  Lemma N_le_div_mul : forall n m,
    m <> 0 ->
    n - m <= (n / m) * m.
  Proof.
    intros.
    eapply N.add_le_mono_r.
    rewrite N.mul_comm, <- N.div_mod'.
    apply N_le_sub.
    - now apply N.mod_le.
    - now apply N.sub_le_mono_l,
                N.lt_le_incl,
                N.mod_lt.
  Qed.

  (** The balance of a single account is always less than
      or equal to the sum of all balances *)
  Lemma balance_le_sum_balances : forall addr state,
    with_default 0 (FMap.find addr (balances state)) <= EIP20Token.sum_balances (token_state state).
  Proof.
    intros.
    destruct FMap.find eqn:balance.
    - eapply FMap.In_elements, sumN_in_le in balance.
      eapply N.le_trans; cycle 1; eauto.
    - apply N.le_0_l.
  Qed.

  Lemma balance_le_sum_balances_ne : forall addr1 addr2 state,
    addr1 <> addr2 ->
    with_default 0 (FMap.find addr1 (balances state)) <=
    EIP20Token.sum_balances (token_state state) - with_default 0 (FMap.find addr2 (balances state)).
  Proof.
    intros * addr_ne.
    destruct (FMap.find addr2) eqn:balance_addr1.
    - unfold EIP20Token.sum_balances.
      erewrite sumN_permutation by
      now eapply Permutation_sym, (fin_maps.map_to_list_delete _ _ n).
      cbn.
      rewrite N.add_comm, <- N.add_sub_assoc, N.sub_diag, N.add_0_r by auto.
      destruct (FMap.find addr1 (FMap.remove addr2 (balances state))) eqn:balance_addr2.
      + cbn.
        erewrite sumN_permutation by
          now eapply Permutation_sym, (fin_maps.map_to_list_delete _ _ t).
        setoid_rewrite FMap.find_remove_ne in balance_addr2; auto.
        setoid_rewrite balance_addr2. cbn.
        lia.
      + setoid_rewrite FMap.find_remove_ne in balance_addr2; auto.
        setoid_rewrite balance_addr2. cbn.
        apply N.le_0_l.
    - rewrite N.sub_0_r. cbn.
      apply balance_le_sum_balances.
  Qed.

  Local Open Scope Z_scope.
  Lemma Z_div_mult : forall n m p,
    p <> 0 ->
    n * p = m ->
    n = m / p.
  Proof.
    intros.
    subst.
    now rewrite Z_div_mult_full.
  Qed.

  (** [sumZ] over balances is always positive *)
  Lemma sum_balances_positive : forall bstate accounts,
    reachable bstate ->
    0 <= sumZ (fun acc : Address => env_account_balances bstate acc) accounts.
  Proof.
    intros * reach.
    apply sumZ_nonnegative.
    intros account _.
    now apply Z.ge_le, account_balance_nonnegative.
  Qed.

  (** Sums balances of a list of accounts *)
  Definition total_balance bstate accounts : Amount :=
    let account_balance := env_account_balances bstate in
      sumZ (fun acc => account_balance acc) accounts.

  (** Sum of balances is always positive *)
  Lemma total_balance_positive : forall bstate accounts,
    reachable bstate ->
    0 <= total_balance bstate accounts.
  Proof.
    intros * reach.
    now apply sum_balances_positive.
  Qed.
  Local Close Scope Z_scope.

  Lemma total_balance_distr : forall state h t x,
    reachable state ->
    Z.to_N (total_balance state (h :: t)) * x =
      Z.to_N (env_account_balances state h) * x +
      Z.to_N (total_balance state t) * x.
  Proof.
    intros * reach.
    cbn.
    rewrite Z2N.inj_add.
    - now rewrite N.mul_add_distr_r.
    - now apply Z.ge_le, account_balance_nonnegative.
    - now apply sum_balances_positive.
  Qed.

  (** Total balance equality if all accounts have equal balance *)
  Lemma total_balance_eq : forall env1 env2 accounts,
    (forall a, In a accounts -> env_account_balances env1 a = env_account_balances env2 a) ->
      total_balance env1 accounts = total_balance env2 accounts.
  Proof.
    intros.
    now apply sumZ_eq.
  Qed.

  Local Open Scope Z_scope.
  Lemma total_balance_le : forall env1 env2 accounts,
    (forall a, In a accounts -> env_account_balances env1 a <= env_account_balances env2 a) ->
      total_balance env1 accounts <= total_balance env2 accounts.
  Proof.
    intros.
    now apply sumZ_le.
  Qed.

  (** Pending usage is the total balance that an account has allocated
      in the pending actions.
      Does not count actions with negative amount and caps the usage
      at the balance limit of the account. *)
  Definition pending_usage bstate account : Amount :=
    Z.min (sumZ (fun act => if address_eqb act.(act_from) account
                          then Z.max 0 (act_amount act)
                          else 0) bstate.(chain_state_queue))
          (env_account_balances bstate account).

  (** Spendable balance is the balance of an account minus their pending
      usage, i.e. the minimum amount that the account is guaranteed to have
      available for usage next block. *)
  Definition spendable_balance (bstate : ChainState) accounts : Amount :=
    let account_balance := env_account_balances bstate in
      sumZ (fun acc => account_balance acc - pending_usage bstate acc) accounts.

  (** Spendable balance is equal to total balance if there is no
      pending actions left in the current block. *)
  Lemma spendable_eq_total_balance : forall bstate accounts,
    reachable bstate ->
    chain_state_queue bstate = [] ->
    spendable_balance bstate accounts = total_balance bstate accounts.
  Proof.
    intros * reach queue.
    unfold spendable_balance, total_balance, pending_usage.
    rewrite queue. cbn.
    erewrite sumZ_eq. eauto.
    intros.
    rewrite Z.min_l, Z.sub_0_r; auto.
    now apply Z.ge_le, account_balance_nonnegative.
  Qed.

  (** Spendable balance cannot decrease when consuming or discarding
      actions from the queue. *)
  Lemma spendable_consume_act : forall (bstate1 bstate2 : ChainState) accounts act acts,
    env_account_balances bstate1 act.(act_from) <= env_account_balances bstate2 act.(act_from) + (Z.max 0 (act_amount act)) ->
    (forall a, In a accounts -> a <> act.(act_from) -> env_account_balances bstate1 a <= env_account_balances bstate2 a) ->
    chain_state_queue bstate1 = act :: acts ->
    chain_state_queue bstate2 = acts ->
    spendable_balance bstate1 accounts <= spendable_balance bstate2 accounts.
  Proof.
    intros * act_balance other_balances queue_from queue_to.
    induction accounts.
    - apply Z.le_refl.
    - cbn.
      apply Z.add_le_mono.
      + edestruct address_eqdec as [from_eq | from_neq];
          unfold pending_usage;
          rewrite queue_from, queue_to; cbn.
        * rewrite from_eq.
          rewrite address_eq_refl.
          lia.
        * rewrite address_eq_ne by auto.
          apply other_balances in from_neq; try apply in_eq.
          lia.
      + apply IHaccounts.
        intros.
        apply other_balances; eauto.
        now apply in_cons.
  Qed.

  (** Spendable balance is always positive *)
  Lemma spendable_balance_positive : forall bstate accounts,
    0 <= spendable_balance bstate accounts.
  Proof.
    intros.
    apply sumZ_nonnegative.
    intros.
    unfold pending_usage.
    rewrite <- Z.sub_max_distr_l, Z.sub_diag.
    apply Z.le_max_r.
  Qed.
  Local Close Scope Z_scope.

  (** Function that generated create_token actions.
      Will keep generating action until all accounts given have been emptied of balance
      or the token goal is hit. Also ensures that we do not hit the token creation cap
      by only creation just enough to go over the token goal. *)
  Fixpoint create_token_acts (env : Environment) caddr accounts tokens_left exchange_rate :=
    let create_tokens_act sender amount := build_act sender sender (act_call caddr amount create_tokens) in
      match accounts with
      | [] => []
      | acc :: accounts' =>
        (** Dont produce any action for this account if tokens_left = 0 *)
        if 0 <? tokens_left
        then
          let amount := 1 + ((tokens_left / exchange_rate)) in
          (** Choose the minimum amount of balance needed to hit tokens_left = 0 or all balance
              if the account does not have enough balance to hit goal *)
          let amount := N.min amount (Z.to_N (env_account_balances env acc)) in
            (create_tokens_act acc (Z.of_N amount)) ::
            create_token_acts env caddr accounts' (N.sub tokens_left (amount * exchange_rate)) exchange_rate
        else
          create_token_acts env caddr accounts' tokens_left exchange_rate
      end.

  Lemma create_token_acts_cons : forall caddr env acc accounts tokens_left exchange_rate,
    let create_tokens_act sender amount := build_act sender sender (act_call caddr amount create_tokens) in
    let amount' := 1 + ((tokens_left / exchange_rate)) in
    let amount := N.min amount' (Z.to_N (env_account_balances env acc)) in
    let act := create_tokens_act acc (Z.of_N amount) in
    0 < tokens_left->
    create_token_acts env caddr (acc :: accounts) tokens_left exchange_rate =
    act :: (create_token_acts env caddr accounts (tokens_left - (amount * exchange_rate))) exchange_rate.
  Proof.
    intros.
    cbn.
    destruct_match eqn:Htokens_left; eauto.
    now apply N.ltb_nlt in Htokens_left.
  Qed.

  Lemma create_token_acts_eq : forall caddr env1 env2 accounts tokens_left exchange_rate,
    (forall a, In a accounts -> env_account_balances env1 a = env_account_balances env2 a) ->
      create_token_acts env1 caddr accounts tokens_left exchange_rate =
      create_token_acts env2 caddr accounts tokens_left exchange_rate.
  Proof.
    induction accounts; intros * env_eq.
    - reflexivity.
    - cbn.
      rewrite env_eq by apply in_eq.
      now do 2 rewrite <- IHaccounts by (intros; now apply env_eq, in_cons).
  Qed.

  (** All actions produced by create_token_acts are from accounts *)
  Lemma create_token_acts_is_account : forall caddr env accounts tokens_left exchange_rate,
    Forall (fun acc : Address => address_is_contract acc = false) accounts ->
      (forall x : Action, In x (create_token_acts env caddr accounts tokens_left exchange_rate) -> act_is_from_account x).
  Proof.
    induction accounts; intros * is_address act HIn.
    - inversion HIn.
    - cbn in HIn.
      apply list.Forall_cons in is_address as [is_address is_address'].
      destruct_match in HIn.
      destruct HIn; subst.
      all: eauto.
  Qed.

  (** All actions produced by create_token_acts have same sender and origin *)
  Lemma create_token_acts_origin_correct: forall accounts (env : Environment) caddr tokens_left exchange_rate,
    Forall act_origin_is_eq_from (create_token_acts env caddr accounts tokens_left exchange_rate).
  Proof.
    induction accounts; intros *.
    - now cbn.
    - cbn.
      destruct_match; auto.
      apply list.Forall_cons.
      destruct_and_split; auto.
      apply address_eq_refl.
  Qed.
  Close Scope N_scope.

End BATCommon.

(** Definitions from EIP20Token *)
Notation "'sum_balances' s" := (EIP20Token.sum_balances (token_state s)) (at level 60).
Notation get_allowance := EIP20Token.get_allowance.
