From Coq Require Import List
                        ZArith_base
                        Lia.
Import ListNotations.
From ConCert Require Import RecordUpdate
                            Extras
                            Containers
                            Automation
                            Serializable
                            Blockchain.
Import RecordSetNotations.
Require EIP20Token.


Section BATCommon.

Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Definition TokenValue := EIP20Token.TokenValue.

Inductive Msg :=
  (* Message types from the EIP20/ERC20 Standard Token: *)
  | tokenMsg : EIP20Token.Msg -> Msg
  (* Message types specific for BAT: *)
  (* create_tokens acceps the currency of the chain and converts it to BAT according to the pre-specified exchange rate *)
  | create_tokens : Msg
  (* finalize ends the funding period and sends the chain currency home to the pre-specified fund deposit address. Only callable by this address *)
  | finalize : Msg
  (* Allows contributors to recover their ether in the case of a failed funding campaign. *)
  | refund : Msg.

Record State :=
  build_state {
    (* State from EIP20Token: *)
    token_state       : EIP20Token.State;
    (* State for BAT: *)
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
    (* In the reference implementation, the fields below are constants, but we allow setting them at initialisation, in order to test out different values. *)
    _tokenExchangeRate  : N;
    _tokenCreationCap 	: N;
    _tokenCreationMin 	: N;
  }.

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

Definition returnIf (cond : bool) := if cond then None else Some tt.
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
  build_act (fundDeposit cstate) (act_call caddr 0%Z finalize).

Definition deploy_act setup contract from : Action :=
  build_act from (act_deploy 0%Z contract setup).

(* Utility definitions and lemmas *)
Open Scope N_scope.
(* Stronger version of N.mod_le.
   N.mod_le requires that b <> 0, however
   it is possible to prove the same without
   that assumption *)
Lemma N_mod_le : forall a b, a mod b <= a.
Proof.
  intros a b. destruct (N.le_gt_cases b a).
  - unfold N.modulo. unfold N.div_eucl.
    destruct a.
    + apply N.le_0_l.
    + destruct b.
      * apply N.le_refl.
      * apply N.le_trans with (N.pos p0); auto.
        apply N.lt_le_incl.
        apply N.pos_div_eucl_remainder. lia.
  - rewrite N.lt_eq_cases; right.
    apply N.mod_small; auto.
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
  rewrite N.div_mod' with (b:= m).
  rewrite N.mul_comm.
  apply N.le_add_r.
Qed.

Lemma N_le_div_mul : forall n m,
  m <> 0 ->
  n - m <= (n / m) * m.
Proof.
  intros.
  eapply N.add_le_mono_r.
  rewrite N.mul_comm.
  rewrite <- N.div_mod' with (b:= m).
  apply N_le_sub.
  - apply N.mod_le; auto.
  - apply N.sub_le_mono_l.
    apply N.lt_le_incl.
    apply N.mod_lt; auto.
Qed.

Lemma sumN_in_le : forall {A} x (f : A -> N) l,
  In x l -> f x <= EIP20Token.sumN f l.
Proof.
  intros.
  induction l.
  - inversion H.
  - apply in_inv in H as [H | H].
    + cbn. subst.
      rewrite N.add_comm.
      apply N_add_le, N.le_refl.
    + cbn.
      now apply N_add_le, IHl.
Qed.

(* The balance of a single account is always less than
   or equal to the sum of all balances *)
Lemma balance_le_sum_balances : forall addr state,
  with_default 0 (FMap.find addr (balances state)) <= EIP20Token.sum_balances (token_state state).
Proof.
  intros.
  unfold EIP20Token.sum_balances.
  destruct (FMap.find addr (balances state)) eqn:balance.
  - cbn. apply FMap.In_elements in balance.
    apply sumN_in_le with (f:= fun '(_, v) => v) in balance.
    now eapply N.le_trans.
  - apply N.le_0_l.
Qed.

(* sumZ over balances is always positive *)
Lemma sum_balances_positive : forall bstate accounts,
  reachable bstate ->
  (0 <= sumZ (fun acc : Address => env_account_balances bstate acc) accounts)%Z.
Proof.
  intros.
  induction accounts; cbn.
  - lia.
  - apply Z.add_nonneg_nonneg; auto.
    apply Z.ge_le.
    now apply account_balance_nonnegative.
Qed.

Lemma sumZ_le : forall {A} l (f g : A -> Z),
  (forall a, In a l -> f a <= g a)%Z ->
  (sumZ f l <= sumZ g l)%Z.
Proof.
  intros.
  induction l.
  - apply Z.le_refl.
  - cbn.
    apply Z.add_le_mono.
    + apply H, in_eq.
    + apply IHl.
      intros.
      now apply H, in_cons.
Qed.

(* Sums balances of a list of accounts *)
Definition total_balance bstate accounts : Amount :=
  let account_balance := env_account_balances bstate in
    sumZ (fun acc => account_balance acc) accounts.

(* Sum of balances is always positive *)
Lemma total_balance_positive : forall bstate accounts,
  reachable bstate -> 
  (0 <= total_balance bstate accounts)%Z.
Proof.
  intros.
  unfold total_balance.
  now apply sum_balances_positive.
Qed.

Lemma total_balance_distr : forall state h t x,
  reachable state ->
  Z.to_N (total_balance state (h :: t)) * x =
    Z.to_N (env_account_balances state h) * x +
    Z.to_N (total_balance state t) * x.
Proof.
  intros.
  cbn.
  rewrite Z2N.inj_add.
  - now rewrite N.mul_add_distr_r.
  - apply Z.ge_le.
    now apply account_balance_nonnegative.
  - now apply sum_balances_positive.
Qed.

(* total balance equality if all accounts have equal balance *)
Lemma total_balance_eq : forall env1 env2 accounts,
  (forall a, In a accounts -> env_account_balances env1 a = env_account_balances env2 a) ->
    total_balance env1 accounts = total_balance env2 accounts.
Proof.
  intros.
  unfold total_balance.
  rewrite sumZ_map_id.
  setoid_rewrite sumZ_map_id at 2.
  f_equal.
  now apply map_ext_in.
Qed.

Lemma total_balance_le : forall env1 env2 accounts,
  (forall a, In a accounts -> env_account_balances env1 a <= env_account_balances env2 a)%Z ->
    (total_balance env1 accounts <= total_balance env2 accounts)%Z.
Proof.
  intros.
  now apply sumZ_le.
Qed.

(* pending usage is the total balance that an account has allocated
   in the pending actions.
   Does not count actions with negative amount and caps the usage
   at the balance limit of the account. *)
Definition pending_usage bstate account : Amount :=
  Z.min (sumZ (fun act => if address_eqb act.(act_from) account
                         then Z.max 0 (act_amount act) 
                         else 0%Z) bstate.(chain_state_queue))
        (env_account_balances bstate account).

(* Spendable blance is the balance of an account minus their pending
   usage, i.e. the minimum amount that the account is guaranteed to have
   available for usage next block. *)
Definition spendable_balance (bstate : ChainState) accounts : Amount :=
  let account_balance := env_account_balances bstate in
    sumZ (fun acc => account_balance acc - pending_usage bstate acc)%Z accounts.

(* Spendable balance is equal to total balance if there is no
   pending actions left in the current block. *)
Lemma spendable_eq_total_balance : forall bstate accounts,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  spendable_balance bstate accounts = total_balance bstate accounts.
Proof.
  intros bstate accounts reach queue.
  unfold spendable_balance, total_balance, pending_usage.
  rewrite queue. cbn.
  rewrite sumZ_map_id.
  setoid_rewrite sumZ_map_id at 2.
  f_equal.
  apply map_ext_in.
  intros.
  rewrite Z.min_l, Z.sub_0_r; auto.
  apply Z.ge_le.
  now apply account_balance_nonnegative.
Qed.

(* Spendable balance cannot decrease when consuming or discarding
   actions from the queue. *)
Lemma spendable_consume_act : forall (bstate1 bstate2 : ChainState) accounts act acts,
  (env_account_balances bstate1 act.(act_from) <= env_account_balances bstate2 act.(act_from) + (Z.max 0 (act_amount act)))%Z ->
  (forall a, In a accounts -> a <> act.(act_from) -> env_account_balances bstate1 a <= env_account_balances bstate2 a)%Z ->
  chain_state_queue bstate1 = act :: acts ->
  chain_state_queue bstate2 = acts ->
  (spendable_balance bstate1 accounts <= spendable_balance bstate2 accounts)%Z.
Proof.
  intros bstate_from bstate_to accounts act acts
         act_balance other_balances queue_from queue_to.
  induction accounts.
  - apply Z.le_refl.
  - cbn.
    apply Z.add_le_mono.
    + destruct (address_eqdec a (act_from act));
        unfold pending_usage; rewrite queue_from, queue_to; cbn.
      * subst.
        rewrite address_eq_refl.
        lia.
      * rewrite address_eq_ne; auto.
        apply other_balances in n; try apply in_eq.
        lia.
    + apply IHaccounts.
      intros.
      apply other_balances; eauto.
      now apply in_cons.
Qed.

(* Spendable balance is always positive *)
Lemma spendable_balance_positive : forall bstate accounts,
  reachable bstate ->
  (0 <= spendable_balance bstate accounts)%Z.
Proof.
  intros.
  unfold spendable_balance.
  induction accounts.
  - apply Z.le_refl.
  - cbn.
    apply Ztac.add_le;
    unfold pending_usage in *;
    lia.
Qed.

(* Function that generated create_token actions.
   Will keep generating action untill all accounts given have been emptied of balance
   or the token goal is hit. Also ensures that we do not hit the token creation cap
   by only creation just enough to go over the token goal. *)
Fixpoint create_token_acts (env : Environment) caddr accounts tokens_left exchange_rate:=
  let create_tokens_act sender amount := build_act sender (act_call caddr amount create_tokens) in
    match accounts with
    | [] => []
    | acc :: accounts' =>
      (* Dont produce any action for this account if tokens_left = 0 *)
      if 0 <? tokens_left
      then
        let amount := 1 + ((tokens_left / exchange_rate)) in
        (* Choose the minimum amount of balance needed to hit tokens_left = 0 or all balance
            if the account does not have enough balance to hit goal *)
        let amount := N.min amount (Z.to_N (env_account_balances env acc)) in
          (create_tokens_act acc (Z.of_N amount)) ::
          create_token_acts env caddr accounts' (N.sub tokens_left (amount * exchange_rate)) exchange_rate
      else
        create_token_acts env caddr accounts' tokens_left exchange_rate
    end.

Lemma create_token_acts_cons : forall caddr env acc accounts tokens_left exchange_rate,
  let create_tokens_act sender amount := build_act sender (act_call caddr amount create_tokens) in
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
  induction accounts; intros.
  - reflexivity.
  - cbn.
    rewrite H by apply in_eq.
    now do 2 rewrite <- IHaccounts by (intros; now apply H, in_cons).
Qed.

(* All actions produced by create_token_acts are from accounts *)
Lemma create_token_acts_is_account : forall caddr env accounts tokens_left exchange_rate,
  Forall (fun acc : Address => address_is_contract acc = false) accounts ->
    (forall x : Action, In x (create_token_acts env caddr accounts tokens_left exchange_rate) -> act_is_from_account x).
Proof.
  induction accounts; intros ? ? is_address act HIn.
  - inversion HIn.
  - cbn in HIn.
    apply list.Forall_cons in is_address as [is_address is_address'].
    destruct_match in HIn. destruct HIn; subst.
    all: eauto.
Qed.
Close Scope N_scope.

End BATCommon.

(* ------------------- Definitions from EIP20Token ------------------- *)
Notation isSome := EIP20Token.isSome.
Notation sumN := EIP20Token.sumN.
Notation "'sum_balances' s" := (EIP20Token.sum_balances (token_state s)) (at level 60).
Notation get_allowance := EIP20Token.get_allowance.
Notation transfer_balance_update_correct := EIP20Token.transfer_balance_update_correct.
Notation transfer_from_allowances_update_correct := EIP20Token.transfer_from_allowances_update_correct.
Notation approve_allowance_update_correct := EIP20Token.approve_allowance_update_correct.

Existing Instance EIP20Token.sumN_perm_proper.

Ltac returnIf H :=
  let G := fresh "G" in
    unfold returnIf in H;
    destruct_match eqn:G in H; try congruence;
    clear H;
    rename G into H.
