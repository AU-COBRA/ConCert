(*
  Implementation of the Basic Attention Token.
  Ported from https://github.com/brave-intl/basic-attention-token-crowdsale/blob/66c886cc4bfb0493d9e7980f392ca7921ef1e7fc/contracts/BAToken.sol
*)
From Coq Require Import ZArith
                        Morphisms
                        List
                        Lia.
Import ListNotations.
From ConCert Require Import Monads
                            Extras
                            Containers
                            Automation
                            RecordUpdate
                            Serializable
                            Blockchain
                            BATCommon
                            BuildUtils.
Import RecordSetNotations.
Require EIP20Token.


Section BATAltFix.
Context {BaseTypes : ChainBase}.

Open Scope N_scope.
Definition init (chain : Chain)
                (ctx : ContractCallContext)
                (setup : Setup) : option State :=
  (* BAToken should not be deployable if one of the following conditions does not hold on "setup"
     1. funding period is non empty
     2. funding period does not start before the slot where the contract is deployed
     3. minimum tokens to fund should not be less than the maximum tokens allowed
     4. the initial supply of tokens should be less than the maximum tokens allowed
     5. token exchange rate must be larger than 0
     6. it must be possible to get over minimum token bound without going over maximum
     For the last condition we check that "exchange rate <= token cap - token min", however this does exclude
     a few possible configurations where the contract still works as intended, however these are not likely to
     come up in real usecases.
  *)
  do _ <- returnIf ((setup.(_fundingEnd) <=? setup.(_fundingStart))%nat
          || (setup.(_fundingStart) <? chain.(current_slot))%nat
          || (setup.(_tokenCreationCap) <? setup.(_tokenCreationMin))
          || (setup.(_tokenExchangeRate) =? 0)
          || ((setup.(_tokenCreationCap) - setup.(_tokenCreationMin)) <? setup.(_tokenExchangeRate))
          || address_eqb setup.(_batFundDeposit) ctx.(ctx_contract_address)
          || address_eqb setup.(_fundDeposit) ctx.(ctx_contract_address)) ;
  let token_state := {|
      EIP20Token.balances := FMap.empty;
      EIP20Token.total_supply := 0;
      EIP20Token.allowances := FMap.empty;
    |} in
  Some {|
    (* EIP20Token initialisation: *)
    token_state := token_state;
    (* BAT initialisation: *)
    initSupply := setup.(_batFund);
    isFinalized := false;
    fundDeposit := setup.(_fundDeposit);
    batFundDeposit := setup.(_batFundDeposit);
    fundingStart := setup.(_fundingStart);
    fundingEnd := setup.(_fundingEnd);
    tokenExchangeRate := setup.(_tokenExchangeRate);
    tokenCreationCap := setup.(_tokenCreationCap);
    tokenCreationMin := setup.(_tokenCreationMin);
  |}.

Definition try_create_tokens sender (sender_payload : Amount) current_slot state :=
 (* early return if funding is finalized, funding period hasn't started yet, or funding period is over *)
  do _ <- returnIf (state.(isFinalized)
          || (Nat.ltb current_slot state.(fundingStart))
          || (Nat.ltb state.(fundingEnd) current_slot)) ;
  (* here we deviate slightly from the reference implementation. They only check for = 0,
     but since ConCert's payloads may be negative numbers, we must extend this check to <= 0 *)
  do _ <- returnIf (Z.leb sender_payload 0) ;
  (* Note: this conversion from Z to N is safe because by assumption sender_payload > 0 *)
  let tokens := (Z.to_N sender_payload) * state.(tokenExchangeRate) in
  let checkedSupply := (total_supply state) + tokens in
  do _ <- returnIf (state.(tokenCreationCap) <? checkedSupply) ;
  let new_token_state : EIP20Token.State := {|
    EIP20Token.total_supply := checkedSupply;
    EIP20Token.balances := FMap.partial_alter (fun balance => Some (with_default 0 balance + tokens)) sender (balances state);
    EIP20Token.allowances := allowances state;
  |} in
  Some (state<|token_state := new_token_state|>).

Definition try_refund sender current_slot state :=
  (* early return if funding is finalized, or funding period is NOT over, or if total supply exceeds or is equal to the minimum fund tokens. *)
  do _ <- returnIf (state.(isFinalized)
          || (Nat.leb current_slot state.(fundingEnd))
          || (state.(tokenCreationMin) <=? (total_supply state))) ;
  do sender_bats <- FMap.find sender (balances state) ;
  do _ <- returnIf (sender_bats =? 0) ;
  (* convert tokens back to the currency of the blockchain, to be sent back to the sender address *)
  let amount_to_send := Z.of_N (sender_bats / state.(tokenExchangeRate)) in
  let new_total_supply := (total_supply) state - sender_bats + (N.modulo sender_bats state.(tokenExchangeRate)) in
  let new_token_state : EIP20Token.State := {|
    EIP20Token.total_supply := new_total_supply;
    EIP20Token.balances := FMap.add sender (N.modulo sender_bats state.(tokenExchangeRate)) (balances state);
    EIP20Token.allowances := allowances state;
  |} in
  let new_state := state<|token_state := new_token_state|> in
  let send_act := act_transfer sender amount_to_send in
    Some (new_state, [send_act]).

Definition try_finalize sender current_slot contract_balance state :=
  (* early return if funding is finalized, or if sender is NOT the fund deposit address,
     or if the total token supply is less than the minimum required amount,
     or if it is too early to end funding and the total token supply has not reached the cap.
    Note: the last requirement makes it possible to end a funding early if the cap has been reached.
  *)
  do _ <- returnIf (state.(isFinalized) ||
                   (negb (address_eqb sender state.(fundDeposit))) ||
                   ((total_supply state) <? state.(tokenCreationMin))) ;
  do _ <- returnIf ((Nat.leb current_slot state.(fundingEnd)) && negb ((total_supply state) =? state.(tokenCreationCap))) ;
  (* Send the currency of the contract back to the fund *)
  let send_act := act_transfer state.(fundDeposit) contract_balance in
  let new_token_state : EIP20Token.State := {|
    EIP20Token.total_supply := (total_supply state) + state.(initSupply);
    EIP20Token.balances := FMap.partial_alter
      (fun balance => Some (with_default 0 balance + state.(initSupply))) state.(batFundDeposit) (balances state);
    EIP20Token.allowances := allowances state;
  |} in
  let new_state := state<|isFinalized := true|><|token_state := new_token_state|> in
  Some (new_state, [send_act]).

Open Scope Z_scope.
Definition receive_bat (chain : Chain)
                    (ctx : ContractCallContext)
                   (state : State)
                   (maybe_msg : option Msg)
                   : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let sender_payload := ctx.(ctx_amount) in
  let slot := chain.(current_slot) in
  let contract_balance := ctx.(ctx_contract_balance) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
  match maybe_msg with
  | Some create_tokens => without_actions (try_create_tokens sender sender_payload slot state)
  | Some refund =>
        do _ <- returnIf (sender_payload >? 0) ;
        try_refund sender slot state
  | Some finalize =>
      do _ <- returnIf (sender_payload >? 0) ;
      try_finalize sender slot contract_balance state
  | _ => None
  end.
Close Scope Z_scope.

(* Composes EIP20Token.receive and receive_bat by first executing EIP20Token.receive (if the message is an EIP20 message),
   and otherwise executes receive_bat *)
Definition receive (chain : Chain)
                    (ctx : ContractCallContext)
                   (state : State)
                   (maybe_msg : option Msg)
                   : option (State * list ActionBody) :=
  match maybe_msg with
  | Some (tokenMsg msg) =>
                     do res <- EIP20Token.receive chain ctx state.(token_state) (Some msg) ;
                     let new_state := state<|token_state := fst res|> in
                         Some (new_state, snd res)
  | _ => receive_bat chain ctx state maybe_msg
  end.

Definition contract : Contract Setup Msg State :=
  build_contract init receive.



Section Theories.
(* ------------------- Tactics to simplify proof steps ------------------- *)

Ltac receive_simpl_step :=
  match goal with
  | H : context[receive] |- _ => unfold receive in H; cbn in H
  | |- context[receive] => unfold receive
  | H : context[receive_bat] |- _ => unfold receive_bat in H
  | |- context[receive_bat] => unfold receive_bat
  | H : context[Blockchain.receive] |- _ => unfold Blockchain.receive in H; cbn in H
  | |- context[Blockchain.receive] => unfold Blockchain.receive; cbn
  | H : context[try_finalize] |- _ => unfold try_finalize in H; cbn in H
  | |- context[try_finalize] => unfold try_finalize; cbn
  | H : context[try_refund] |- _ => unfold try_refund in H; cbn in H
  | |- context[try_refund] => unfold try_refund; cbn
  | H : context[try_create_tokens] |- _ => unfold try_create_tokens in H; cbn in H
  | |- context[try_create_tokens] => unfold try_create_tokens; cbn
  | H : returnIf _ = _ |- _ => returnIf H
  | H : option_map (fun s : State => (s, _)) match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
  | H : match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
  | H : isSome (match ?m with | Some _ => _ | None => None end) = _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
  | H : option_map (fun s : State => (s, _)) (if ?m then ?a else ?b) = Some _ |- _ =>
    match a with
    | None =>
      let a := fresh "H" in
      destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
    | _ => match b with
           | None =>
             let a := fresh "H" in
             destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
           | _ => idtac
    end end
  | H : (if ?m then ?a else ?b) = Some _ |- _ =>
    match a with
    | None =>
      let a := fresh "H" in
      destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
    | _ => match b with
           | None =>
             let a := fresh "H" in
             destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
           | _ => idtac
    end end
  end.

Tactic Notation "receive_simpl" := repeat receive_simpl_step.



(* ------------------- Transfer correct ------------------- *)

Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct (token_state prev_state) (token_state new_state) ctx.(ctx_from) to amount = true.
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_balance_correct; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_preserves_total_supply; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_preserves_allowances : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_preserves_allowances; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_preserves_other_balances : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) -> account <> to ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_preserves_other_balances; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_is_some : forall state chain ctx to amount,
  (ctx_amount ctx >? 0)%Z = false ->
  (amount = 0 /\ isSome (FMap.find (ctx_from ctx) (balances state)) = false)
  \/ amount <= with_default 0 (FMap.find (ctx_from ctx) (balances state))
    <-> isSome (receive chain ctx state (Some (transfer to amount))) = true.
Proof.
  intros * sender_amount_zero.
  unfold balances. cbn.
  destruct_match eqn:receive;
    now erewrite EIP20Token.try_transfer_is_some, receive.
Qed.



(* ------------------- Transfer_from correct ------------------- *)

Lemma try_transfer_from_balance_correct : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct (token_state prev_state) (token_state new_state) from to amount = true /\
  transfer_from_allowances_update_correct (token_state prev_state) (token_state new_state) from ctx.(ctx_from) amount = true.
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_from_balance_correct; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_from_preserves_total_supply : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_from_preserves_total_supply; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_from_preserves_other_balances : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> from -> account <> to ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_from_preserves_other_balances.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_from_preserves_other_allowances : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> from ->
      FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_from_preserves_other_allowances; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_from_preserves_other_allowance : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      get_allowance (token_state prev_state) from account = get_allowance (token_state new_state) from account.
Proof.
  intros * receive_some account account_not_sender.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_from_preserves_other_allowance; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_from_is_some : forall state chain ctx from to amount,
  let get_allowance_ account := FMap.find account (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances state))) in
  (ctx_amount ctx >? 0)%Z = false ->
  isSome (FMap.find from (allowances state)) = true
  /\ isSome (get_allowance_ (ctx_from ctx)) = true
  /\ amount <= with_default 0 (FMap.find from (balances state))
  /\ amount <= with_default 0 (get_allowance_ (ctx_from ctx))
    <-> isSome (receive chain ctx state (Some (transfer_from from to amount))) = true.
Proof.
  intros * sender_amount_zero.
  unfold balances, allowances, get_allowance_. cbn.
  destruct_match eqn:receive;
    now erewrite EIP20Token.try_transfer_from_is_some, receive.
Qed.



(* ------------------- Approve correct ------------------- *)

Lemma try_approve_allowance_correct : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
  approve_allowance_update_correct (token_state new_state) ctx.(ctx_from) delegate amount = true.
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_approve_allowance_correct; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_approve_preserves_total_supply; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_approve_preserves_balances : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (balances prev_state) = (balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_approve_preserves_balances; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_approve_preserves_other_allowances : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
Proof.
  intros * receive_some account account_not_sender.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_approve_preserves_other_allowances; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_approve_preserves_other_allowance : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    forall account, account <> delegate ->
      get_allowance (token_state prev_state) (ctx_from ctx) account = get_allowance (token_state new_state) (ctx_from ctx) account.
Proof.
  intros * receive_some account account_not_delegate.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_approve_preserves_other_allowance; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_approve_is_some : forall state chain ctx delegate amount,
  (ctx_amount ctx >? 0)%Z = false <-> isSome (receive chain ctx state (Some (approve delegate amount))) = true.
Proof.
  intros.
  cbn.
  destruct_match eqn:receive;
    now erewrite EIP20Token.try_approve_is_some, receive.
Qed.



(* ------------------- EIP20 functions only changes token_state ------------------- *)

Lemma eip_only_changes_token_state : forall prev_state new_state chain ctx m new_acts,
  receive chain ctx prev_state (Some (tokenMsg m)) = Some (new_state, new_acts) ->
    prev_state<|token_state := (token_state new_state)|> = new_state.
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.



(* ------------------- EIP20 functions not payable ------------------- *)

Lemma eip20_not_payable : forall prev_state new_state chain ctx m new_acts,
  receive chain ctx prev_state (Some (tokenMsg m)) = Some (new_state, new_acts) ->
    (ctx_amount ctx <= 0)%Z.
Proof.
  intros * receive_some.
  receive_simpl.
  destruct p.
  now eapply EIP20Token.EIP20_not_payable.
Qed.



(* ------------------- EIP20 functions produces no acts ------------------- *)

Lemma eip20_new_acts_correct : forall prev_state new_state chain ctx m new_acts,
  receive chain ctx prev_state (Some (tokenMsg m)) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  receive_simpl.
  destruct p.
  eapply EIP20Token.EIP20_no_acts.
  inversion receive_some.
  now subst.
Qed.



(* ------------------- Create_tokens correct ------------------- *)

Lemma try_create_tokens_balance_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    with_default 0 (FMap.find (ctx_from ctx) (balances prev_state)) =
    with_default 0 (FMap.find (ctx_from ctx) (balances new_state)) - ((Z.to_N (ctx_amount ctx)) * (tokenExchangeRate prev_state)).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  setoid_rewrite EIP20Token.add_is_partial_alter_plus; auto.
  destruct (FMap.find (ctx_from ctx) (balances prev_state)) eqn:from_balance;
    setoid_rewrite from_balance;
    setoid_rewrite FMap.find_add; cbn;
    now rewrite N.add_sub.
Qed.

Lemma try_create_tokens_total_supply_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    (total_supply prev_state) + ((Z.to_N (ctx_amount ctx)) * (tokenExchangeRate prev_state)) =
    (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

Lemma try_create_tokens_preserves_other_balances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros * receive_some account account_not_sender.
  receive_simpl.
  inversion receive_some.
  setoid_rewrite EIP20Token.add_is_partial_alter_plus; auto.
  now setoid_rewrite FMap.find_add_ne.
Qed.

Lemma try_create_tokens_preserves_allowances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

Lemma try_create_tokens_only_change_token_state : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    prev_state<|token_state := (token_state new_state)|> = new_state.
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

Lemma try_create_tokens_is_some : forall state chain ctx,
  Z.lt 0 (ctx_amount ctx)
  /\ (isFinalized state) = false
  /\ ((fundingStart state) <= (current_slot chain))%nat
  /\ ((current_slot chain) <= (fundingEnd state))%nat
  /\ (total_supply state) + ((Z.to_N (ctx_amount ctx)) * (tokenExchangeRate state)) <= (tokenCreationCap state)
    <-> exists x y, receive chain ctx state (Some create_tokens) = Some (x, y).
Proof.
  split.
  - intros (amount_positive & not_finalized &
      funding_started & funding_not_over & cap_not_hit).
    receive_simpl.
    destruct_match eqn:match_requirements; returnIf match_requirements.
    destruct_match eqn:sender_amount; returnIf sender_amount.
    destruct_match eqn:cap_hit; returnIf cap_hit.
    + eauto.
    + rewrite N.ltb_lt in cap_hit.
      lia.
    + rewrite Z.leb_le in sender_amount.
      lia.
    + rewrite !Bool.orb_true_iff in match_requirements.
      destruct match_requirements as
        [[finalized | funding_not_started%Nat.ltb_lt] | funding_over%Nat.ltb_lt]; try easy.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    rename H into match_requirements.
    rename H0 into sender_amount.
    rename H1 into cap_hit.
    rewrite Z.leb_gt in sender_amount.
    apply N.ltb_ge in cap_hit.
    rewrite !Bool.orb_false_iff in match_requirements.
    destruct match_requirements as
      ((not_finalized & funding_started%Nat.ltb_ge) & funding_not_over%Nat.ltb_ge).
    intuition.
Qed.

Lemma try_create_tokens_acts_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros.
  receive_simpl.
Qed.

Lemma try_create_tokens_amount_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    Z.lt 0 ctx.(ctx_amount).
Proof.
  intros.
  receive_simpl.
  rename H1 into sender_amount_positive.
  now apply Z.leb_gt in sender_amount_positive.
Qed.



(* ------------------- Finalize correct ------------------- *)

Lemma try_finalize_isFinalized_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    (isFinalized prev_state) = false /\ (isFinalized new_state) = true.
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  split.
  - rename H0 into requirements_check.
    now do 2 apply Bool.orb_false_iff in requirements_check as [requirements_check _].
  - reflexivity.
Qed.

Lemma try_finalize_balance_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    with_default 0 (FMap.find prev_state.(batFundDeposit) (balances prev_state)) =
    with_default 0 (FMap.find new_state.(batFundDeposit) (balances new_state)) - new_state.(initSupply).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  setoid_rewrite EIP20Token.add_is_partial_alter_plus; auto. cbn.
  destruct (FMap.find (batFundDeposit prev_state) (balances prev_state)) eqn:from_balance;
    setoid_rewrite from_balance;
    setoid_rewrite FMap.find_add; cbn;
    now rewrite N.add_sub.
Qed.

Lemma try_finalize_total_supply_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    (total_supply prev_state) + prev_state.(initSupply) =
    (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

Lemma try_finalize_preserves_other_balances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    forall account, account <> prev_state.(batFundDeposit) ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros * receive_some account account_not_batfund.
  receive_simpl.
  inversion receive_some.
  setoid_rewrite EIP20Token.add_is_partial_alter_plus; auto.
  now setoid_rewrite FMap.find_add_ne.
Qed.

Lemma try_finalize_preserves_allowances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

Lemma try_finalize_is_some : forall state chain ctx,
  (ctx_amount ctx >? 0)%Z = false
  /\ (isFinalized state) = false
  /\ (ctx_from ctx) = (fundDeposit state)
  /\ (tokenCreationMin state) <= (total_supply state)
  /\ ((fundingEnd state) < (current_slot chain) \/ (tokenCreationCap state) = (total_supply state))%nat
    <-> exists x y, receive chain ctx state (Some finalize) = Some (x, y).
Proof.
  split.
  - intros * (amount_zero & not_finalized & sender_funddeposit & min_hit & funding_over).
    receive_simpl.
    destruct_match eqn:amount_check; returnIf amount_check.
    destruct_match eqn:requirements_check; returnIf requirements_check.
    destruct_match eqn:funding_over_check; returnIf funding_over_check.
    + easy.
    + apply Bool.andb_true_iff in funding_over_check as
        (funding_not_over%Nat.leb_le & cap_not_hit%Bool.negb_true_iff%N.eqb_neq).
      now destruct funding_over.
    + rewrite !Bool.orb_true_iff in requirements_check.
      destruct requirements_check as
        [[finalized | sender_not_funddeposit%Bool.negb_true_iff] | min_not_hit%N.ltb_lt]; try easy.
      * now destruct_address_eq.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    rename H into amount_check.
    rename H0 into requirements_check.
    rename H1 into funding_over_check.
    rewrite !Bool.orb_false_iff in requirements_check.
    destruct requirements_check as
      ((not_finalized & sender_funddeposit) & min_hit%N.ltb_ge).
    repeat split; eauto.
    + now destruct_address_eq.
    + now apply Bool.andb_false_iff in funding_over_check as
        [H4%Nat.leb_gt | H5%Bool.negb_false_iff%N.eqb_eq].
Qed.

Lemma try_finalize_acts_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    new_acts =
    [act_transfer
      (fundDeposit prev_state)
      (ctx_contract_balance ctx)
    ].
Proof.
  intros.
  receive_simpl.
Qed.



(* ------------------- Refund correct ------------------- *)

Lemma try_refund_balance_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    with_default 0 (FMap.find (ctx_from ctx) (balances new_state)) =
    N.modulo (with_default 0 (FMap.find (ctx_from ctx) (balances prev_state))) prev_state.(tokenExchangeRate).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  now setoid_rewrite FMap.find_add.
Qed.

Lemma try_refund_total_supply_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    (total_supply prev_state) - (with_default 0 (FMap.find (ctx_from ctx) (balances prev_state))) +
    N.modulo (with_default 0 (FMap.find (ctx_from ctx) (balances prev_state))) prev_state.(tokenExchangeRate) =
    (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

Lemma try_refund_preserves_other_balances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros * receive_some account account_not_sender.
  receive_simpl.
  inversion receive_some.
  now setoid_rewrite FMap.find_add_ne.
Qed.

Lemma try_refund_preserves_allowances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

Lemma try_refund_only_change_token_state : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    prev_state<|token_state := (token_state new_state)|> = new_state.
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

Lemma try_refund_is_some : forall state chain ctx,
  (ctx_amount ctx >? 0)%Z = false
  /\ (isFinalized state) = false
  /\ ((fundingEnd state) < (current_slot chain))%nat
  /\ (total_supply state) < (tokenCreationMin state)
  /\ 0 < with_default 0 (FMap.find (ctx_from ctx) (balances state))
    <-> exists x y, receive chain ctx state (Some refund) = Some (x, y).
Proof.
  split.
  - intros (amount_zero & not_finalized & funding_over & min_not_hit & balance_not_zero).
    receive_simpl.
    destruct_match eqn:amount_check; returnIf amount_check.
    destruct_match eqn:requirements_check; returnIf requirements_check.
    destruct_match eqn:from_balance.
    destruct_match eqn:from_balance_check; returnIf from_balance_check.
    + easy.
    + rewrite N.eqb_eq in from_balance_check.
      now rewrite from_balance_check in balance_not_zero.
    + easy.
    + rewrite !Bool.orb_true_iff in requirements_check.
      now destruct requirements_check as
        [[finalized | funding_active%Nat.leb_le] | min_hit%N.leb_le].
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    rename H into amount_check.
    rename H0 into requirements_check.
    rename H1 into from_balance.
    rename H2 into from_balance_check.
    rewrite N.eqb_neq in from_balance_check.
    rewrite !Bool.orb_false_iff in requirements_check.
    destruct requirements_check as
      ((not_finalized & funding_over%Nat.leb_gt) & min_not_hit%N.leb_gt).
    now repeat split.
Qed.

Lemma try_refund_acts_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    new_acts =
    [act_transfer
      (ctx_from ctx)
      (Z.of_N (with_default 0 (FMap.find (ctx_from ctx) (balances prev_state)) / (tokenExchangeRate prev_state)))
    ].
Proof.
  intros.
  receive_simpl.
Qed.



(* ------------------- Init correct ------------------- *)

Lemma init_bat_balances_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    (balances state) = FMap.empty.
Proof.
  intros * init_some.
  cbn in init_some.
  destruct_match in init_some; try congruence.
  now inversion init_some.
Qed.

Lemma init_allowances_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    (allowances state) = FMap.empty.
Proof.
  intros * init_some.
  cbn in init_some.
  destruct_match in init_some; try congruence.
  now inversion init_some.
Qed.

Lemma init_isFinalized_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    state.(isFinalized) = false.
Proof.
  intros * init_some.
  cbn in init_some.
  destruct_match in init_some; try congruence.
  now inversion init_some.
Qed.

Lemma init_total_supply_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    (total_supply state) = 0.
Proof.
  intros * init_some.
  cbn in init_some.
  destruct_match in init_some; try congruence.
  now inversion init_some.
Qed.

Lemma init_constants_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    state.(fundDeposit) = setup.(_fundDeposit)
    /\ state.(batFundDeposit) = setup.(_batFundDeposit)
    /\ state.(fundingStart) = setup.(_fundingStart)
    /\ state.(fundingEnd) = setup.(_fundingEnd)
    /\ state.(tokenExchangeRate) = setup.(_tokenExchangeRate)
    /\ state.(tokenCreationCap) = setup.(_tokenCreationCap)
    /\ state.(tokenCreationMin) = setup.(_tokenCreationMin)
    /\ state.(initSupply) = setup.(_batFund).
Proof.
  intros * init_some.
  cbn in init_some.
  destruct_match in init_some; try congruence.
  now inversion init_some.
Qed.



(* ------------------- EIP20 functions preserve sum of balances ------------------- *)

Lemma try_transfer_preserves_balances_sum : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_preserves_balances_sum; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_transfer_from_preserves_balances_sum : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_transfer_from_preserves_balances_sum; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_approve_preserves_balances_sum : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  eapply EIP20Token.try_approve_preserves_balances_sum; eauto.
  destruct p.
  subst. now cbn.
Qed.

Lemma try_create_tokens_update_balances_sum : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    (sum_balances prev_state) + ((Z.to_N (ctx_amount ctx)) * (tokenExchangeRate prev_state)) = (sum_balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  unfold EIP20Token.sum_balances.
  cbn in *. clear H H3 H4.
  setoid_rewrite EIP20Token.add_is_partial_alter_plus; auto.
  destruct (FMap.find (ctx_from ctx) (balances prev_state)) eqn:from_balance.
  - setoid_rewrite from_balance.
    setoid_rewrite FMap.elements_add_existing; eauto.
    erewrite sumN_split with (x := (ctx_from ctx, _)) (y:= (ctx_from ctx, _)) by eauto.
    now rewrite sumN_swap, fin_maps.map_to_list_delete, N.add_comm.
  - setoid_rewrite from_balance.
    setoid_rewrite FMap.elements_add; auto.
    now rewrite N.add_comm.
Qed.

Lemma try_finalize_preserves_balances_sum : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    (sum_balances prev_state) + prev_state.(initSupply) = (sum_balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some.
  unfold EIP20Token.sum_balances. cbn.
  setoid_rewrite EIP20Token.add_is_partial_alter_plus; auto.
  destruct (FMap.find (batFundDeposit prev_state) (balances prev_state)) eqn:from_balance.
  - setoid_rewrite from_balance.
    setoid_rewrite FMap.elements_add_existing; eauto.
    erewrite sumN_split with (x := ((batFundDeposit prev_state), _)) (y:= ((batFundDeposit prev_state), _)) by eauto.
    now rewrite sumN_swap, fin_maps.map_to_list_delete, N.add_comm.
  - setoid_rewrite from_balance.
    setoid_rewrite FMap.elements_add; auto.
    now rewrite N.add_comm.
Qed.

Lemma try_refund_update_balances_sum : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state) + (with_default 0 (FMap.find (ctx_from ctx) (balances prev_state))) -
    N.modulo (with_default 0 (FMap.find (ctx_from ctx) (balances prev_state))) prev_state.(tokenExchangeRate).
Proof.
  intros * receive_some.
  receive_simpl.
  inversion receive_some. 
  unfold EIP20Token.sum_balances. clear H H4 H5.
  setoid_rewrite FMap.elements_add_existing; eauto.
  change n with ((fun '(_, v) => v) (ctx_from ctx, n)).
  rewrite sumN_inv, sumN_swap, fin_maps.map_to_list_delete by auto. cbn.
  now rewrite N.add_comm, N.add_sub.
Qed.

Lemma init_preserves_balances_sum : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    (sum_balances state) = (total_supply state).
Proof.
  intros * init_some.
  cbn in init_some.
  destruct_match in init_some; try congruence.
  inversion init_some.
  unfold EIP20Token.sum_balances. subst. cbn.
  reflexivity.
Qed.



(* ------------------- init validation ------------------- *)

Lemma deployed_implies_constants_valid bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ (cstate.(fundingStart) < cstate.(fundingEnd))%nat
    /\ cstate.(tokenCreationMin) <= cstate.(tokenCreationCap)
    /\ cstate.(tokenExchangeRate) <> 0
    /\ cstate.(tokenExchangeRate) <= cstate.(tokenCreationCap) - cstate.(tokenCreationMin)
    /\ cstate.(batFundDeposit) <> caddr
    /\ cstate.(fundDeposit) <> caddr.
Proof.
  contract_induction; intros; auto.
  - unfold Blockchain.init in init_some. cbn in *.
    destruct_match eqn:setup_check in init_some; try congruence.
    returnIf setup_check.
    rewrite !Bool.orb_false_iff in setup_check.
    destruct setup_check as
      ((((((funding_period_nonempty & funding_not_started) & funding_goal) &
      exchange_rate_nonzero) & can_hit_min) & contract_ne_batfund) & contract_ne_ethfund).
    inversion init_some. cbn.
    repeat split.
    + now apply leb_complete_conv in funding_period_nonempty.
    + now apply N.ltb_ge in funding_goal.
    + now apply N.eqb_neq in exchange_rate_nonzero.
    + now apply N.ltb_ge in can_hit_min.
    + now destruct_address_eq.
    + now destruct_address_eq.
  - destruct msg. destruct m. destruct m.
    all: receive_simpl; now inversion receive_some.
  - destruct msg. destruct m. destruct m.
    all: receive_simpl; now inversion receive_some.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ _ => True).
    unset_all; subst; cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.



(* ------------------- Sum of balances always equals total supply ------------------- *)

(* In any reachable state the sum of token balance
    will be equal to the total supply of tokens *)
Lemma sum_balances_eq_total_supply bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ (total_supply cstate) = (sum_balances cstate).
Proof.
  assert (receive_sum_balances_eq_total_supply :
          forall prev_state new_state chain ctx msg new_acts,
            total_supply prev_state = sum_balances prev_state ->
            receive chain ctx prev_state msg = Some (new_state, new_acts) ->
            prev_state.(tokenExchangeRate) <> 0 ->
            total_supply new_state = sum_balances new_state).
  - intros prev_state new_state chain ctx msg new_acts IH receive_some exchange_rate_nonzero.
    destruct msg. destruct m. destruct m.
    + now erewrite <- try_transfer_preserves_balances_sum,
                   <- try_transfer_preserves_total_supply.
    + now erewrite <- try_transfer_from_preserves_balances_sum,
                   <- try_transfer_from_preserves_total_supply.
    + now erewrite <- try_approve_preserves_balances_sum,
                   <- try_approve_preserves_total_supply.
    + now erewrite <- try_create_tokens_update_balances_sum,
                   <- try_create_tokens_total_supply_correct; eauto.
    + erewrite <- try_finalize_preserves_balances_sum,
               <- try_finalize_total_supply_correct; eauto. lia.
    + apply try_refund_update_balances_sum in receive_some as balance_sum.
      apply try_refund_total_supply_correct in receive_some.
      rewrite IH in receive_some. rewrite <- receive_some.
      rewrite <- N.add_sub_swap, balance_sum, N.sub_add.
      now rewrite N.add_sub.
      apply N_add_le.
      now apply N.mod_le.
      apply balance_le_sum_balances.
    + now receive_simpl.
  - contract_induction; intros;
      only 1: instantiate (CallFacts := fun _ _ cstate _ => cstate.(tokenExchangeRate) <> 0); eauto.
    + now apply init_preserves_balances_sum in init_some.
    + instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      unset_all; subst.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      intros ? contract_deployed ?.
      now apply deployed_implies_constants_valid in contract_deployed as [].
Qed.



(* ------------------- total supply can only grow before funding fails ------------------- *)

(* If funding period is active or funding goal was hit then the
    total supply of tokens cannot decrease *)
Lemma receive_total_supply_increasing : forall prev_state new_state chain ctx msg new_acts,
  ((current_slot chain) <= (fundingEnd prev_state))%nat \/ tokenCreationMin prev_state <= total_supply prev_state->
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
       (total_supply prev_state) <= (total_supply new_state).
Proof.
  intros * funding_active receive_some.
  destruct msg. destruct m. destruct m.
  - apply try_transfer_preserves_total_supply in receive_some. lia.
  - apply try_transfer_from_preserves_total_supply in receive_some. lia.
  - apply try_approve_preserves_total_supply in receive_some. lia.
  - apply try_create_tokens_total_supply_correct in receive_some.
    rewrite <- receive_some. apply N.le_add_r.
  - apply try_finalize_total_supply_correct in receive_some. lia.
  - specialize try_refund_is_some as [_ refund_implications].
    rewrite receive_some in refund_implications.
    now destruct refund_implications; eauto.
  - now receive_simpl.
Qed.



(* ------------------- Constants are constant ------------------- *)

(* Constants should never change after after receiving msg *)
Lemma receive_preserves_constants : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
       prev_state.(fundDeposit) = new_state.(fundDeposit)
    /\ prev_state.(batFundDeposit) = new_state.(batFundDeposit)
    /\ prev_state.(fundingStart) = new_state.(fundingStart)
    /\ prev_state.(fundingEnd) = new_state.(fundingEnd)
    /\ prev_state.(tokenExchangeRate) = new_state.(tokenExchangeRate)
    /\ prev_state.(tokenCreationCap) = new_state.(tokenCreationCap)
    /\ prev_state.(tokenCreationMin) = new_state.(tokenCreationMin)
    /\ prev_state.(initSupply) = new_state.(initSupply).
Proof.
  intros * receive_some.
  destruct msg. destruct m. destruct m.
  all: receive_simpl; now inversion receive_some.
Qed.

(* Constants are always equal to the initial assignment *)
Lemma constants_are_constant bstate caddr (trace : ChainTrace empty_state bstate) :
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists deploy_info cstate,
    deployment_info _ trace caddr = Some deploy_info
    /\ contract_state bstate caddr = Some cstate
    /\ let setup := deploy_info.(deployment_setup) in
         cstate.(fundDeposit) = setup.(_fundDeposit)
      /\ cstate.(batFundDeposit) = setup.(_batFundDeposit)
      /\ cstate.(fundingStart) = setup.(_fundingStart)
      /\ cstate.(fundingEnd) = setup.(_fundingEnd)
      /\ cstate.(tokenExchangeRate) = setup.(_tokenExchangeRate)
      /\ cstate.(tokenCreationCap) = setup.(_tokenCreationCap)
      /\ cstate.(tokenCreationMin) = setup.(_tokenCreationMin)
      /\ cstate.(initSupply) = setup.(_batFund).
Proof.
  apply (lift_dep_info_contract_state_prop contract);
    intros *; clear trace bstate caddr.
  - intros init_some.
    now apply init_constants_correct in init_some.
  - intros IH receive_some.
    now apply receive_preserves_constants in receive_some.
Qed.



(* ------------------- Finalize cannot be undone ------------------- *)

(* Once the contract is in the finalized state it cannot leave it *)
Lemma final_is_final : forall prev_state new_state chain ctx msg new_acts,
  (isFinalized prev_state) = true /\
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
    (isFinalized new_state) = true.
Proof.
  intros * (finalized & receive_some).
  destruct msg. destruct m.
  - now rewrite <- (eip_only_changes_token_state _ _ _ _ _ _ receive_some).
  - now rewrite <- (try_create_tokens_only_change_token_state _ _ _ _ _ receive_some).
  - now apply try_finalize_isFinalized_correct in receive_some.
  - now rewrite <- (try_refund_only_change_token_state _ _ _ _ _ receive_some).
  - now receive_simpl.
Qed.



(* ------------------- Cannot finalize if goal not hit ------------------- *)

Lemma no_finalization_before_goal bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ (total_supply cstate < tokenCreationMin cstate -> isFinalized cstate = false).
Proof.
  apply (lift_contract_state_prop contract);
    intros *; clear bstate caddr.
  - intros init_some ?.
    now eapply init_isFinalized_correct.
  - intros IH receive_some ?.
    destruct msg. destruct m.
    + apply eip_only_changes_token_state in receive_some as finalized_unchanged.
      destruct m.
      * apply try_transfer_preserves_total_supply in receive_some as supply_unchanged.
        now rewrite supply_unchanged, <- finalized_unchanged in *.
      * apply try_transfer_from_preserves_total_supply in receive_some as supply_unchanged.
        now rewrite supply_unchanged, <- finalized_unchanged in *.
      * apply try_approve_preserves_total_supply in receive_some as supply_unchanged.
        now rewrite supply_unchanged, <- finalized_unchanged in *.
    + apply try_create_tokens_only_change_token_state in receive_some as finalized_unchanged.
      rewrite <- finalized_unchanged in *.
      receive_simpl.
      rename H0 into requirements_check.
      now rewrite !Bool.orb_false_iff in requirements_check.
    + receive_simpl.
      inversion receive_some as [supply_unchanged].
      rewrite <- supply_unchanged in *.
      rename H1 into requirements_check.
      rewrite !Bool.orb_false_iff in requirements_check.
      cbn in *.
      now destruct requirements_check as (_ & goal_hit%N.ltb_nlt).
    + apply try_refund_only_change_token_state in receive_some as finalized_unchanged.
      rewrite <- finalized_unchanged in *.
      receive_simpl.
      rename H1 into requirements_check.
      now rewrite !Bool.orb_false_iff in requirements_check.
    + now receive_simpl.
Qed.



(* ------------------- It is always possible to finalize ------------------- *)

(* Prove that it is always possible to reach a state where the token is finalized if the funding
   goal was reached *)
Lemma can_finalize_if_creation_min : forall bstate (reward : Amount) (caddr creator : Address),
  address_is_contract creator = false ->
  (reward >= 0)%Z ->
  reachable bstate ->
  emptyable (chain_state_queue bstate) ->
  (exists cstate,
    env_contracts bstate caddr = Some (BATAltFix.contract : WeakContract)
    /\ env_contract_states bstate caddr = Some (serializeState cstate)
    /\ (tokenCreationMin cstate) <= (total_supply cstate)
    /\ address_is_contract (fundDeposit cstate) = false)
      ->
      exists bstate', reachable_through bstate bstate'
        /\ emptyable (chain_state_queue bstate')
        /\ exists cstate',
        env_contracts bstate' caddr = Some (BATAltFix.contract : WeakContract)
        /\ env_contract_states bstate' caddr = Some (serializeState cstate')
        /\ (isFinalized cstate') = true.
Proof.
  intros * Hcreator Hreward bstate_reachable bstate_queue H.
  (* Empty the action queue so that we can add new blocks *)
  empty_queue H; destruct H as (cstate & contract_deployed & contract_state & creation_min & fund_deposit_not_contract);
    (* Prove that H is preserved after transfers, discarding invalid actions, calling other contracts and deploying contracts *)
    only 3: destruct (address_eqdec caddr to_addr);
    try (now eexists; rewrite_environment_equiv; repeat split; eauto;
         cbn; destruct_address_eq; try easy).
  - (* Prove that H is preserved after calls to the contract *)
    clear amount_nonnegative enough_balance reward Hreward creator Hcreator
      bstate_queue bstate_reachable bstate new_acts_eq act_eq.
    subst.
    rewrite contract_deployed in deployed.
    inversion deployed. subst.
    rewrite contract_state in deployed_state.
    inversion deployed_state. subst.
    clear deployed_state deployed.
    apply wc_receive_strong in receive_some as
      (prev_state' & msg' & new_state' & serialize_prev_state & _ & serialize_new_state & receive_some).
    setoid_rewrite deserialize_serialize in serialize_prev_state.
    inversion serialize_prev_state. subst.
    apply receive_total_supply_increasing in receive_some as total_supply_increasing; try (cbn; lia).
    apply receive_preserves_constants in receive_some as (? & ? & ? & ? & ? & ? & ? & ?).
    repeat match goal with
    | H : _ prev_state' =  _ new_state' |- _=> rewrite H in *; clear H
    end.
    exists new_state'.
    rewrite_environment_equiv; cbn; repeat split; eauto;
    cbn; destruct_address_eq; try easy.
    eapply N.le_trans; eauto.
  - update_all.
    (* First check if contract is already finalized, if it is we just use the current state to finish proof *)
    destruct (isFinalized cstate) eqn:finalized;
      [eexists; rewrite queue; split; eauto; split; eauto; eapply empty_queue_is_emptyable |].
    (* Fast forward time/slot to "fundingEnd" so that we know for sure that the funding period is not active
        in the next block *)
    forward_time (cstate.(fundingEnd)); eauto.
    (* forward_time gives us a new ChainState so we no longer need the old one therefore
        we call update_all to replace all occurrences of the old ChainState with the new one *)
    update_all.
    (* Now we know that the funding period is over or on its last slot and the funding minimum has been hit.
       So now we can add a new block containing a finalize call *)
    add_block [(finalize_act cstate caddr)] 1%nat; eauto.
    (* The hypothesis "slot_hit" no longer holds so we have to update it manually before calling update_all *)
    update (S (fundingEnd cstate) <= current_slot bstate0)%nat in slot_hit by
      (rewrite_environment_equiv; cbn; easy).
    update_all.
    clear reward Hreward creator Hcreator.

    (* We can now evaluate the action we added giving us a ChainState where
        the token is in its finalized state *)
    evaluate_action BATAltFix.contract; try easy.
    + (* Prove that there is enough balance to evaluate action *)
      now apply account_balance_nonnegative.
    + (* Prove that receive action returns Some *)
      specialize (try_finalize_is_some cstate bstate0) as ((new_cstate & new_act & receive_some) & _); cycle 1.
      * rewrite receive_some.
        now receive_simpl.
      * easy.
    + cbn in *.
      clear contract_state slot_hit creation_min.
      update_all;
        [rewrite queue0; do 3 f_equal;repeat (rewrite_environment_equiv; cbn; destruct_address_eq; try easy)|].
      (* Finally we need to evaluate the new transfer action that finalize produced *)
      evaluate_transfer; try easy.
      * (* Prove that the transfer is nonnegative *)
        destruct_address_eq;
        try rewrite Z.add_0_r;
        now apply account_balance_nonnegative.
      * (* Prove that there is enough balance to evaluate the transfer *)
        destruct_address_eq;
        try rewrite Z.add_0_r;
        apply Z.le_ge, Z.le_refl.
      * exists bstate0.
        split; eauto.
        rewrite queue.
        split; try apply empty_queue_is_emptyable.
        eexists.
        now repeat split; try (rewrite_environment_equiv; cbn; eauto).
Qed.

(* Prove that it is always possible to reach a state where the token is finalized if there
   is enough money in the blockchain and the contract constants have valid values *)
Lemma can_finalize_if_deployed : forall deployed_bstate (reward : Amount) (caddr creator : Address) accounts,
  address_is_contract creator = false ->
  (reward >= 0)%Z ->
  reachable deployed_bstate ->
  emptyable (chain_state_queue deployed_bstate) ->
  NoDup accounts ->
  Forall (fun acc => address_is_contract acc = false) accounts ->
  (exists deployed_cstate,
    env_contracts deployed_bstate caddr = Some (BATAltFix.contract : WeakContract)
    /\ env_contract_states deployed_bstate caddr = Some (serializeState deployed_cstate)
    /\ (((tokenCreationMin deployed_cstate) - (total_supply deployed_cstate))) <=
            ((Z.to_N (spendable_balance deployed_bstate accounts)) * (tokenExchangeRate deployed_cstate))
    /\ ((fundingStart deployed_cstate) <= (current_slot (env_chain deployed_bstate)))%nat
    /\ ((current_slot (env_chain deployed_bstate)) < (fundingEnd deployed_cstate))%nat
    /\ address_is_contract (fundDeposit deployed_cstate) = false)
      ->
      exists bstate, reachable_through deployed_bstate bstate
        /\ emptyable (chain_state_queue bstate)
        /\ exists cstate,
        env_contracts bstate caddr = Some (BATAltFix.contract : WeakContract)
        /\ env_contract_states bstate caddr = Some (serializeState cstate)
        /\ (isFinalized cstate) = true.
Proof.
  intros * Hcreator Hreward reach' empty accounts_unique accounts_not_contracts H.
  (* Empty the action queue so that we can add new blocks *)
  empty_queue H; destruct H as
    (cstate & contract_deployed & contract_state & enough_balance_to_fund &
     funding_period_started & funding_period_not_over & fund_deposit_not_contract);
    (* Prove that H is preserved after transfers, discarding invalid actions, calling other contracts and deploying contracts *)
    only 3: destruct (address_eqdec caddr to_addr);
    try now exists cstate;
        repeat split; eauto;
          try (rewrite_environment_equiv; cbn; (easy || now destruct_address_eq));
        eapply N.le_trans; [apply enough_balance_to_fund | apply N.mul_le_mono_r, Z2N.inj_le; try now apply spendable_balance_positive];
        eapply spendable_consume_act; eauto;
          intros; rewrite_environment_equiv; subst; (try destruct msg);
          cbn; destruct_address_eq; try easy; lia.
  - (* Prove that H is preserved after calls to the contract *)
    clear enough_balance reward Hreward creator Hcreator empty reach'
      deployed_bstate new_acts_eq accounts_unique accounts_not_contracts.
    subst.
    rewrite contract_deployed in deployed.
    inversion deployed.
    rewrite contract_state in deployed_state.
    inversion deployed_state.
    subst.
    clear deployed_state deployed.
    apply wc_receive_strong in receive_some as
      (prev_state' & msg' & new_state' & serialize_prev_state & serialize_msg & serialize_new_state & receive_some).
    setoid_rewrite deserialize_serialize in serialize_prev_state. inversion serialize_prev_state. subst.
    apply receive_total_supply_increasing in receive_some as total_supply_increasing; try (cbn; lia).
    apply receive_preserves_constants in receive_some as (? & ? & ? & ? & ? & ? & ? & ?).
    repeat match goal with
    | H : _ prev_state' =  _ new_state' |- _=> rewrite H in *; clear H
    end.
    eexists new_state'.
    repeat split; eauto;
      try (rewrite_environment_equiv; cbn; (easy || now destruct_address_eq)).
    eapply N.le_trans in enough_balance_to_fund; [| apply N.sub_le_mono_l, total_supply_increasing].
    eapply N.le_trans.
    apply enough_balance_to_fund.
    apply N.mul_le_mono_r, Z2N.inj_le; try now apply spendable_balance_positive.
    eapply spendable_consume_act; eauto;
      intros; rewrite_environment_equiv; subst; destruct msg;
      cbn; destruct_address_eq; try easy; lia.
  - (* Update goal and eleminate all occurrences of old ChainState *)
    update_all.
    (* Now that the queue is empty we can switch from using spendable_balance
       to total_balance to simplify the proof *)
    rewrite spendable_eq_total_balance in enough_balance_to_fund; eauto.

    (* First check if contract is already finalized, if it is we just use the current state to finish proof *)
    destruct (isFinalized cstate) eqn:finalized;
      [eexists; split; eauto; rewrite queue; split; eauto; apply empty_queue_is_emptyable |].

    (* Next add a new block containing enough create_tokens actions to reach funding goal *)
    add_block (create_token_acts (bstate<|env_account_balances := add_balance creator reward bstate.(env_account_balances)|>) caddr accounts
            ((tokenCreationMin cstate) - (total_supply cstate)) cstate.(tokenExchangeRate)) 1%nat;
      only 1: apply Hcreator; eauto; [now apply All_Forall.In_Forall, create_token_acts_is_account | ].
    (* Prove that the funding period is still not over *)
    update ((current_slot bstate0) <= (fundingEnd cstate))%nat in funding_period_not_over by
      (rewrite_environment_equiv; cbn; lia).
    (* Prove that the environment in the new ChainState is correct *)
    update (setter_from_getter_Environment_env_account_balances
               (fun _ : Address -> Amount => add_balance creator reward (env_account_balances bstate)) bstate)
      with bstate0.(chain_state_env) in queue0 by
      (rewrite queue0; apply create_token_acts_eq; intros; now rewrite_environment_equiv).
    (* Prove that there is still enough balance in accounts to hit funding goal *)
    update bstate with bstate0 in enough_balance_to_fund.
    { eapply N.le_trans; eauto.
      apply N.mul_le_mono_r, Z2N.inj_le;
        try now apply total_balance_positive.
      apply (total_balance_le bstate).
      intros. rewrite_environment_equiv. cbn.
      destruct_address_eq; lia.
    }
    update_all.
    generalize dependent bstate0.
    generalize dependent cstate.

    (* Next we do induction on account to evaluate all the actions added to the queue *)
    induction accounts; intros.
    + (* If the queue is empty then we know that the funding goal was hit
          and can then apply can_finalize_if_creation_min *)
      clear accounts_unique accounts_not_contracts finalized
            funding_period_not_over funding_period_started.
      apply N.le_0_r, N.sub_0_le in enough_balance_to_fund.
      specialize (can_finalize_if_creation_min bstate0 reward caddr creator).
      intros []; eauto.
      rewrite queue0.
      apply empty_queue_is_emptyable.
    + clear reward Hreward creator Hcreator.
      apply NoDup_cons_iff in accounts_unique as [accounts_unique accounts_unique'].
      apply list.Forall_cons in accounts_not_contracts as [accounts_not_contracts accounts_not_contracts'].

      (* Check if funding goal was alredy hit *)
      destruct (tokenCreationMin cstate - total_supply cstate) eqn:tokens_left_to_fund.
      * (* If funding goal is reached then we know that create_token_acts will not
            produce any more actions so the queue is actually empty.
           Therefore we can directly apply the induction hypothesis *)
        eapply IHaccounts; eauto.
       -- now rewrite tokens_left_to_fund.
       -- rewrite tokens_left_to_fund.
          apply N.le_0_l.
      * rewrite <- tokens_left_to_fund in *.
        (* We check if the account balance is 0 *)
        destruct (0 <? env_account_balances bstate0 a)%Z eqn:balance_positive; cycle 1;
          [apply Z.ltb_ge in balance_positive | apply Z.ltb_lt in balance_positive].
        { (* If account balance is 0 then we need to discard the action as it
              cannot be evaluated *)
          assert (amount_zero : (forall x, x <= 0 -> Z.to_N x = 0%N)%Z) by lia.
          rewrite create_token_acts_cons, amount_zero, N.min_0_r, N.mul_0_l, N.sub_0_r in queue0 by lia.
          discard_invalid_action; eauto.
          - (* Prove that the action cannot be evaluated since create_tokens
                requires to be called with amount > 0 *)
            clear dependent accounts.
            clear dependent cstate.
            clear p reach0 accounts_not_contracts balance_positive.
            intros * eval.
            destruct eval as
            [?from_addr ?to_addr ?amount ?amount_nonnegative ?enough_balance
              ?to_addr_not_contract ?act_eq ?env_eq ?new_acts_eq |
              ?from_addr ?to_addr ?amount ?wc ?setup ?state ?amount_nonnegative
              ?enough_balance ?to_addr_contract ?not_deployed ?act_eq ?init_some ?env_eq ?new_acts_eq |
              ?from_addr ?to_addr ?amount ?wc ?msg ?prev_state ?new_state ?resp_acts
              ?amount_nonnegative ?enough_balance ?deployed ?deployed_state ?act_eq ?receive_some ?new_acts_eq ?env_eq ];
            try destruct msg; inversion act_eq; subst.
            rewrite contract_deployed in deployed.
            inversion deployed. subst.
            clear deployed.
            apply wc_receive_strong in receive_some as
              (prev_state' & msg' & new_state' & serialize_prev_state & serialize_msg & serialize_new_state & receive_some).
            destruct_match in serialize_msg; try congruence.
            cbn in serialize_msg.
            setoid_rewrite deserialize_serialize in serialize_msg.
            inversion serialize_msg. subst.
            now apply try_create_tokens_amount_correct in receive_some.
          - (* Apply induction hypothesis *)
            edestruct IHaccounts with (bstate0 := bstate) (cstate := cstate) as
              (bstate_new & reach_new & emptyable_new & H); eauto; try (rewrite_environment_equiv; eauto).
            + rewrite queue.
              apply create_token_acts_eq.
              intros. now rewrite_environment_equiv.
            + rewrite total_balance_distr, N.add_comm in enough_balance_to_fund; eauto.
              erewrite (total_balance_eq _ bstate0) by (intros; now rewrite_environment_equiv).
              lia.
        }

        specialize deployed_implies_constants_valid as
            (cstate' & contract_state' & _ & _ & echange_rate_nonzero & can_hit_fund_min); eauto.
        cbn in contract_state'.
        rewrite contract_state in contract_state'.
        setoid_rewrite deserialize_serialize in contract_state'.
        inversion contract_state'. subst cstate'.
        clear contract_state'.

        (* Now we know that the action is valid we need to evaluate it *)
        evaluate_action BATAltFix.contract; try easy;
          only 1-4: clear fund_deposit_not_contract accounts_not_contracts IHaccounts.
        -- (* Prove that there is an action in the queue *)
           now rewrite create_token_acts_cons by lia.
        -- (* Prove that amount is nonnegative *)
           apply Z.le_ge, N2Z.is_nonneg.
        -- (* Prove that amount <= account balance *)
           nia.
        -- (* Prove that receive returns Some *)
           clear dependent accounts.
           clear contract_state.
           apply Nat.ltb_ge in funding_period_started.
           apply Nat.ltb_ge in funding_period_not_over.
           cbn.
           rewrite finalized, funding_period_started, funding_period_not_over, N2Z.inj_min, Z2N.id;
             try (apply Z.ge_le, account_balance_nonnegative; eauto).
           clear finalized funding_period_started funding_period_not_over.
           cbn.
           destruct_match eqn:match_amount; returnIf match_amount.
           destruct_match eqn:match_cap; returnIf match_cap; eauto.
        --- (* Prove contradiction between match_amount, match_cap and can_hit_fund_min *)
            apply N.ltb_lt in match_cap.
            apply Z.leb_gt, Z.min_glb_lt_iff in match_amount as [min_left min_right].
            rewrite Z2N.inj_min, N2Z.id, <- N.mul_min_distr_r, <- N.add_min_distr_l, N.min_glb_lt_iff in match_cap.
            destruct match_cap as [match_cap_left match_cap_right].
            apply N.lt_le_trans with (p := (tokenCreationMin cstate) + tokenExchangeRate cstate) in match_cap_left.
            nia.
            rewrite N.mul_add_distr_r, N.mul_1_l.
            rewrite N.add_assoc, N.add_comm, N.add_assoc.
            rewrite <- N.add_le_mono_r.
            apply N_le_sub. lia.
            now apply N_div_mul_le.
        --- (* Prove contradiction between match_amount, balance_positive *)
            apply Zle_bool_imp_le, Z.min_le in match_amount as [min_left | min_right].
         ---- rewrite <- N2Z.inj_0 in min_left.
              now apply N2Z.inj_le, N_le_add_distr in min_left.
         ---- lia.
        -- assert (caddr_not_in_accounts : ~ In caddr accounts) by
             (intro; rewrite Forall_forall in accounts_not_contracts'; apply accounts_not_contracts' in H; now apply contract_addr_format in contract_deployed).
           (* Apply induction hypothesis *)
           edestruct IHaccounts as (bstate_new & reach_new & emptyable_new & H);
             clear IHaccounts accounts_not_contracts balance_positive queue0 tokens_left_to_fund p can_hit_fund_min;
             only 10: (rewrite deployed_state; eauto);
             try (rewrite_environment_equiv; eauto);
             cbn; try rewrite Z2N.inj_min, N2Z.id;
             clear deployed_state contract_deployed funding_period_started funding_period_not_over
                   fund_deposit_not_contract finalized contract_state.
         --- (* Prove that the queues of the two ChainStates are equivalent *)
             rewrite queue, N.sub_add_distr.
             apply create_token_acts_eq.
             intros. rewrite_environment_equiv. cbn. now destruct_address_eq.
         --- (* Prove that there still is enough balance to hit funding goal *)
             clear queue accounts_not_contracts'.
             edestruct N.min_dec.
          ---- cbn. rewrite e.
               eapply N.le_trans; [| apply N.le_0_l].
               rewrite N.mul_add_distr_r, N.mul_1_l.
               apply N.le_0_r.
               rewrite N.sub_add_distr.
               rewrite N.sub_add_distr.
               apply N.sub_0_le.
               now apply N_le_div_mul.
          ---- rewrite total_balance_distr, N.add_comm in enough_balance_to_fund; eauto.
               erewrite (total_balance_eq _ bstate0) by
                (intros; rewrite_environment_equiv; cbn; now destruct_address_eq).
               apply N.le_sub_le_add_r in enough_balance_to_fund.
               rewrite <- N.sub_add_distr in enough_balance_to_fund.
               eapply N.le_trans; [| apply enough_balance_to_fund].
               apply N.sub_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r.
               lia.
Qed.

Lemma can_deploy_and_finalize : forall bstate (reward : Amount) (caddr creator : Address) accounts setup,
  address_is_contract creator = false ->
  (reward >= 0)%Z ->
  reachable bstate ->
  chain_state_queue bstate = [] ->
  NoDup accounts ->
  Forall (fun acc => address_is_contract acc = false) accounts ->
  address_is_contract caddr = true ->
  env_contracts bstate caddr = None ->
  (((_tokenCreationMin setup))) <=
            ((Z.to_N (spendable_balance bstate accounts)) * (_tokenExchangeRate setup)) ->
  setup.(_tokenExchangeRate) <= setup.(_tokenCreationCap) - setup.(_tokenCreationMin) ->
  ((_fundingStart setup) < (_fundingEnd setup))%nat ->
  (S (current_slot (env_chain bstate)) < (_fundingStart setup))%nat ->
  address_is_contract (_fundDeposit setup) = false ->
  setup.(_tokenExchangeRate) <> 0 ->
  setup.(_batFundDeposit) <> caddr ->
  setup.(_fundDeposit) <> caddr ->
  exists bstate',
    reachable_through bstate bstate'
    /\ emptyable (chain_state_queue bstate')
    /\ exists cstate,
    env_contracts bstate' caddr = Some (BATAltFix.contract : WeakContract)
    /\ env_contract_states bstate' caddr = Some (serializeState cstate)
    /\ (isFinalized cstate) = true.
Proof.
  intros * Hcreator Hreward
        bstate_reachable
        bstate_queue
        accounts_unique
        accounts_not_contracts
        caddr_is_contract
        contract_not_deployed
        enough_balance_to_fund
        can_hit_fund_min
        funding_period_nonempty
        funding_period_not_started
        fund_deposit_not_contract
        echange_rate_nonzero
        batfund_not_caddr
        ethfund_not_caddr.

  add_block [(deploy_act setup BATAltFix.contract creator)] 1%nat; eauto.
  update ((current_slot bstate0) < _fundingStart setup)%nat in funding_period_not_started by
    (rewrite_environment_equiv; cbn; lia).
  update bstate with bstate0 in enough_balance_to_fund by
    (eapply N.le_trans; [apply enough_balance_to_fund | apply N.mul_le_mono_r, Z2N.inj_le; try now apply spendable_balance_positive];
     unfold spendable_balance, pending_usage; rewrite queue, bstate_queue; apply sumZ_le;
     intros; rewrite_environment_equiv; cbn; destruct_address_eq; try lia).
  update_all.

  deploy_contract BATAltFix.contract; eauto; try lia;
    try now apply account_balance_nonnegative.
  { (* Prove that init returns some *)
    cbn.
    destruct_match eqn:requirements; eauto.
    returnIf requirements.
    repeat apply Bool.orb_prop in requirements as [requirements | requirements].
    - now apply Nat.leb_le in requirements.
    - now apply Nat.ltb_lt in requirements.
    - now apply N.ltb_lt in requirements.
    - now apply N.eqb_eq in requirements.
    - now apply N.ltb_lt in requirements.
    - now destruct_address_eq.
    - now destruct_address_eq.
  }
  specialize constants_are_constant as
    (dep_info & cstate' & deploy_info' & deployed_state' & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
  unfold contract_state in deployed_state'. cbn in deployed_state'.
  rewrite deployed_state, deserialize_serialize in deployed_state'.
  inversion deployed_state'. subst cstate'. clear deployed_state'.
  rewrite deploy_info in deploy_info'.
  inversion deploy_info'. subst dep_info. clear deploy_info'.
  cbn in *.
  repeat match goal with
  | H : _ cstate =  _ setup |- _=> rewrite <- H in *; clear H
  end.
  update bstate0 with bstate in enough_balance_to_fund by
    (eapply N.le_trans; [apply enough_balance_to_fund | apply N.mul_le_mono_r, Z2N.inj_le; try now apply spendable_balance_positive];
     eapply spendable_consume_act; eauto; intros; rewrite_environment_equiv; subst; cbn; destruct_address_eq; try easy; lia).
  clear dependent trace.
  update_all.

  forward_time_exact (cstate.(fundingStart)); eauto.
  update bstate with bstate0 in enough_balance_to_fund by
    (inversion header_valid;
     eapply N.le_trans; [apply enough_balance_to_fund | apply N.mul_le_mono_r, Z2N.inj_le; try now apply spendable_balance_positive];
     unfold spendable_balance, pending_usage; rewrite queue, queue0; apply sumZ_le;
     intros; rewrite_environment_equiv; cbn; destruct_address_eq; try lia).
  clear funding_period_not_started.
  update_all.

  eapply can_finalize_if_deployed; eauto.
  - rewrite queue. apply empty_queue_is_emptyable.
  - eexists.
    intuition.
Qed.



(* ------------------- BAToken outgoing acts facts ------------------- *)

(* BAToken never calls itself *)
Lemma bat_no_self_calls bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  Forall (fun act_body =>
    match act_body with
    | act_transfer to _ => (to =? caddr)%address = false
    | _ => False
    end) (outgoing_acts bstate caddr).
Proof.
  contract_induction; intros; auto.
  - now inversion IH.
  - apply Forall_app; split; auto.
    clear IH.
    instantiate (CallFacts := fun _ ctx state _ => fundDeposit state <> ctx_contract_address ctx).
    destruct msg. destruct m.
    + now erewrite eip20_new_acts_correct by eauto.
    + receive_simpl.
      now inversion receive_some.
    + receive_simpl.
      inversion_clear receive_some.
      constructor; auto.
      now destruct_address_eq.
    + receive_simpl.
      inversion_clear receive_some.
      constructor; auto.
      now destruct_address_eq.
    + now receive_simpl.
  - inversion_clear IH as [|? ? head_not_me tail_not_me].
    apply Forall_app; split; auto.
    clear tail_not_me.
    destruct head; try contradiction.
    destruct action_facts as [? _].
    now destruct_address_eq.
  - now rewrite <- perm.
  - instantiate (DeployFacts := fun _ _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros ? contract_deployed ?.
    cbn.
    now apply deployed_implies_constants_valid in contract_deployed as
      (cstate' & deployed_cstate' & _ & _ & _ & _ & _ & ethfund_not_caddr).
Qed.

Lemma bat_no_self_calls' : forall bstate from_addr to_addr amount msg acts,
  reachable bstate ->
  env_contracts bstate to_addr = Some (contract : WeakContract) ->
  chain_state_queue bstate = {| act_from := from_addr; act_body :=
    match msg with
    | Some msg => act_call to_addr amount msg
    | None => act_transfer to_addr amount
    end |} :: acts ->
  from_addr <> to_addr.
Proof.
  intros * reach deployed queue.
  apply bat_no_self_calls in deployed as no_self_calls; auto.
  unfold outgoing_acts in no_self_calls.
  rewrite queue in no_self_calls.
  cbn in no_self_calls.
  destruct_address_eq; auto.
  inversion_clear no_self_calls as [|? ? hd _].
  destruct msg.
  * congruence.
  * now rewrite address_eq_refl in hd.
Qed.

(* BAToken only produces transfer acts *)
Lemma outgoing_acts_are_transfers : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  Forall (fun act_body =>
    match act_body with
    | act_transfer _ _ => True
    | _ => False
    end) (outgoing_acts bstate caddr).
Proof.
  intros * reach deployed.
  apply (lift_outgoing_acts_prop contract); auto.
  intros * receive_some.
  destruct msg; try discriminate.
  destruct m.
  - (* m = EIP msg *)
    now erewrite eip20_new_acts_correct.
  - (* m = create_tokens *)
    now erewrite try_create_tokens_acts_correct.
  - (* m = finalize *)
    now erewrite try_finalize_acts_correct.
  - (* m = refund *)
    now erewrite try_refund_acts_correct.
Qed.

(* BAToken only produces transfer acts *)
Lemma outgoing_acts_positive_amount : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  Forall (fun act_body => 0 <= act_body_amount act_body)%Z (outgoing_acts bstate caddr).
Proof.
  contract_induction; intros; auto.
  - now inversion IH.
  - instantiate (CallFacts := fun _ ctx _ _ =>
      (0 <= (ctx_contract_balance ctx))%Z /\
      ctx_from ctx <> ctx_contract_address ctx).
    destruct facts as (contract_balance_positive & _).
    destruct msg; try discriminate.
    destruct m.
    + (* m = EIP msg *)
      apply eip20_new_acts_correct in receive_some.
      now subst.
    + (* m = create_tokens *)
      apply try_create_tokens_acts_correct in receive_some.
      now subst.
    + (* m = finalize *)
      apply try_finalize_acts_correct in receive_some.
      subst.
      now constructor.
    + (* m = refund *)
      apply try_refund_acts_correct in receive_some.
      subst.
      constructor; auto.
      apply N2Z.is_nonneg.
  - now destruct facts.
  - eapply forall_respects_permutation; eauto.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros cstate contract_deployed _. cbn.
    subst. cbn.
    split.
    + (* Prove call fact: 0 <= ctx_contract_balance ctx *)
      destruct_address_eq; subst; try easy.
      * lia.
      * apply Z.add_nonneg_nonneg; try lia.
        now apply Z.ge_le, account_balance_nonnegative.
    + (* Prove call fact: ctx_from ctx <> ctx_contract_address ctx *)
      now eapply bat_no_self_calls'.
Qed.



(* ------------------- No outgoing acts produces while funding ------------------- *)

Lemma funding_period_no_acts : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ (isFinalized cstate = false /\
        ((current_slot bstate <= fundingEnd cstate)%nat \/ tokenCreationMin cstate <= total_supply cstate) ->
        outgoing_acts bstate caddr = []).
Proof.
  contract_induction; intros; auto; try rename H into not_finalized.
  - specialize (IH not_finalized).
    discriminate.
  - instantiate (CallFacts := fun _ ctx state _ =>
        ctx_from ctx <> ctx_contract_address ctx /\
        total_supply state = sum_balances state).
    destruct facts as (_ & supply_eq_sum_balances).
    destruct msg. destruct m.
    + apply eip_only_changes_token_state in receive_some as finalized_unchanged.
      apply eip20_new_acts_correct in receive_some as no_new_acts.
      destruct m.
      * apply try_transfer_preserves_total_supply in receive_some as supply_unchanged.
        rewrite <- supply_unchanged, <- finalized_unchanged in not_finalized.
        now rewrite IH, no_new_acts.
      * apply try_transfer_from_preserves_total_supply in receive_some as supply_unchanged.
        rewrite <- supply_unchanged, <- finalized_unchanged in not_finalized.
        now rewrite IH, no_new_acts.
      * apply try_approve_preserves_total_supply in receive_some as supply_unchanged.
        rewrite <- supply_unchanged, <- finalized_unchanged in not_finalized.
        now rewrite IH, no_new_acts.
    + apply try_create_tokens_only_change_token_state in receive_some as finalized_unchanged.
      apply try_create_tokens_acts_correct in receive_some as no_new_acts.
      specialize try_create_tokens_is_some as (_ & (_ & _ & _ & funding_active & _)); eauto.
      rewrite  <- finalized_unchanged in not_finalized.
      destruct not_finalized as [not_finalized _].
      rewrite no_new_acts, IH; auto.
    + apply try_finalize_isFinalized_correct in receive_some as finalized.
      now destruct not_finalized as [not_finalized _].
    + apply try_refund_only_change_token_state in receive_some as finalized_unchanged.
      apply try_refund_total_supply_correct in receive_some as new_supply.
      specialize try_refund_is_some as
        (_ & (_ & _ & funding_over%lt_not_le & goal_not_hit & _)); eauto.
      destruct not_finalized as [_ [funding_not_over | goal_hit]].
      * now rewrite <- finalized_unchanged in funding_not_over.
      * rewrite <- new_supply, <- finalized_unchanged in goal_hit.
        cbn in goal_hit.
        eapply N.le_trans with (n := tokenCreationMin prev_state) (p := total_supply prev_state) in goal_hit; try lia.
        apply N_sub_add_mod.
        rewrite supply_eq_sum_balances.
        apply balance_le_sum_balances.
    + now receive_simpl.
  - now destruct facts.
  - apply IH in not_finalized. subst.
    now apply Permutation.Permutation_nil in perm.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros ? contract_deployed ?.
    subst. cbn.
    split.
    + now eapply bat_no_self_calls'.
    + now specialize sum_balances_eq_total_supply as
        (? & ? & ?).
Qed.



(* ------------------- Contract balance bound ------------------- *)

Lemma contract_balance_bound : forall bstate caddr (trace : ChainTrace empty_state bstate),
  let effective_balance := (env_account_balances bstate caddr - (sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr)))%Z in
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate deploy_info,
    contract_state bstate caddr = Some cstate
    /\ deployment_info Setup trace caddr = Some deploy_info
    /\ (isFinalized cstate = true -> effective_balance = 0)%Z
    /\ (isFinalized cstate = false ->
      (effective_balance - deploy_info.(deployment_amount)) * (Z.of_N cstate.(tokenExchangeRate)) =
      (Z.of_N (total_supply cstate)))%Z.
Proof.
  intros *.
  unfold effective_balance.
  contract_induction; intros; auto; try destruct IH as [IH_finalized IH_funding].
  - cbn in *.
    destruct_match in init_some; try congruence.
    inversion init_some. cbn.
    split; intros.
    + discriminate.
    + lia.
  - cbn in *.
    split; intros.
    + now rewrite <- IH_finalized by assumption.
    + now rewrite <- IH_funding by assumption.
  - instantiate (CallFacts := fun chain ctx state out_acts =>
      (0 <= ctx_amount ctx)%Z /\
      tokenExchangeRate state <> 0 /\
      total_supply state = sum_balances state /\
      (isFinalized state = false /\
              ((current_slot chain <= fundingEnd state)%nat \/
              tokenCreationMin state <= total_supply state) -> out_acts = []) /\
      ctx_from ctx <> ctx_contract_address ctx).
    destruct facts as (ctx_amount_positive &
                       exchange_rate_nonzero &
                       supply_eq_sum_balances &
                       funding_no_outgoing_acts & _).
    clear CallFacts AddBlockFacts DeployFacts effective_balance tag prev_inc_calls prev_out_txs.
    destruct msg. destruct m.
    + apply eip_only_changes_token_state in receive_some as finalized_unchanged.
      apply eip20_new_acts_correct in receive_some as no_new_acts.
      apply eip20_not_payable in receive_some as not_payable.
      apply Z.le_antisymm in ctx_amount_positive; auto.
      rewrite ctx_amount_positive, Z.sub_0_r in IH_finalized, IH_funding.
      destruct m.
      * apply try_transfer_preserves_total_supply in receive_some as supply_unchanged.
        now rewrite no_new_acts, <- supply_unchanged, <- finalized_unchanged.
      * apply try_transfer_from_preserves_total_supply in receive_some as supply_unchanged.
        now rewrite no_new_acts, <- supply_unchanged, <- finalized_unchanged.
      * apply try_approve_preserves_total_supply in receive_some as supply_unchanged.
        now rewrite no_new_acts, <- supply_unchanged, <- finalized_unchanged.
    + apply try_create_tokens_amount_correct in receive_some as payable.
      receive_simpl.
      inversion receive_some.
      subst. cbn in *.
      clear receive_some.
      rename H into requirements_check.
      rewrite !Bool.orb_false_iff in requirements_check.
      destruct requirements_check as ((not_finalized & _) & _).
      split; intros finalized_state.
      * congruence.
      * now apply IH_funding in finalized_state.
    + receive_simpl.
      inversion receive_some.
      subst. cbn in *.
      clear receive_some.
      rename H into not_payable.
      rewrite Z.gtb_ltb, Z.ltb_ge in not_payable.
      apply Z.le_antisymm in ctx_amount_positive; auto.
      rewrite ctx_amount_positive, Z.sub_0_r in IH_finalized, IH_funding.
      split; intros finalized_state.
      * rewrite Z.sub_add_distr, Z.sub_diag, Z.sub_0_l, <- Z.opp_0, Z.opp_inj_wd.
        rename H0 into requirements_check.
        rewrite !Bool.orb_false_iff in requirements_check.
        destruct requirements_check as ((not_finalized & _) & funding_hit%N.ltb_ge).
        now rewrite funding_no_outgoing_acts.
      * congruence.
    + receive_simpl.
      inversion receive_some.
      subst. cbn in *.
      clear receive_some.
      rename H into not_payable.
      rewrite Z.gtb_ltb, Z.ltb_ge in not_payable.
      apply Z.le_antisymm in ctx_amount_positive; auto.
      rewrite ctx_amount_positive, Z.sub_0_r in IH_finalized, IH_funding.
      rename H0 into requirements_check.
      rename H1 into from_balance.
      rewrite !Bool.orb_false_iff in requirements_check.
      destruct requirements_check as ((finalized_sate & _) & _).
      split; intros finalized_state.
      * congruence.
      * apply IH_funding in finalized_state.
        rewrite <- Z.sub_add_distr, <- Z.add_assoc, Z.add_comm, !Z.sub_add_distr, Z.mul_sub_distr_r, <- N2Z.inj_mul.
        setoid_rewrite finalized_state.
        rewrite supply_eq_sum_balances in *.
        specialize N_div_mod as ?.
        specialize N_mod_le as ?.
        specialize (balance_le_sum_balances (ctx_from ctx) prev_state) as ?.
        rewrite from_balance in *.
        specialize N_sub_mod_le as ?.
        rewrite H, <- N2Z.inj_sub, N2Z.inj_add, (N2Z.inj_sub _ n); auto.
        rewrite <- Z.sub_sub_distr, <- N2Z.inj_sub, <- N2Z.inj_sub; auto.
        all:  now eapply N.le_trans.
    + now receive_simpl.
  - now destruct facts.
  - now erewrite sumZ_permutation in IH_finalized, IH_funding by eauto.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros ? contract_deployed ?.
    subst. cbn.
    repeat split.
    + now apply Z.ge_le.
    + now specialize deployed_implies_constants_valid as
        (cstate' & deployed_state' & _ & _ & exchange_rate_nonzero & _ & _).
    + now specialize sum_balances_eq_total_supply as
        (cstate' & deployed_state' & ?).
    + intros.
      specialize funding_period_no_acts as (cstate' & deployed_state' & no_acts); eauto.
      now apply no_acts.
    + now eapply bat_no_self_calls'.
Qed.



(* ------------------- outgoing acts are valid ------------------- *)

(* Prove that all outgoing acts produced by the contract can be evaluated *)
Lemma outgoing_acts_evaluable : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  Forall (fun act_body => receiver_can_receive_transfer bstate act_body) (outgoing_acts bstate caddr) ->
  Forall (fun act_body => exists bstate_new, inhabited (ActionEvaluation bstate (build_act caddr act_body) bstate_new [])) (outgoing_acts bstate caddr).
Proof.
  intros * reach deployed can_receive_funds.
  assert (trace := reach).
  destruct trace as [trace].
  specialize contract_balance_bound as
    (cstate & dep_info & deployed_state & deployed_info &
    contract_balance_bound_finalized & contract_balance_bound); eauto.
  apply deployment_amount_nonnegative in deployed_info as dep_amount_nonnegative.
  specialize deployed_implies_constants_valid as
    (cstate' & deployed_state' & _ & _ & exchange_rate_nonzero & _); eauto.
  rewrite deployed_state in deployed_state'.
  inversion deployed_state'.
  subst cstate'. clear deployed_state'.
  eapply outgoing_acts_are_transfers in reach as acts_are_transfers; eauto.
  eapply outgoing_acts_positive_amount in reach as acts_amount_positive; eauto.
  apply Forall_forall.
  intros act HIn.
  eapply Forall_forall in acts_are_transfers; eauto.
  eapply Forall_forall in acts_amount_positive as act_amount_positive; eauto.
  eapply Forall_forall in can_receive_funds; eauto.
  destruct act; try now exfalso.
  clear acts_are_transfers.
  assert (enough_balance : (act_body_amount (act_transfer to amount) <= env_account_balances bstate caddr)%Z).
  { destruct (isFinalized cstate).
    - apply Zminus_eq in contract_balance_bound_finalized; auto.
      rewrite contract_balance_bound_finalized.
      apply sumZ_in_le; eauto.
      now apply Forall_forall.
    - apply Z_div_mult in contract_balance_bound; auto; try lia.
      eapply Z.add_cancel_r in contract_balance_bound.
      rewrite Z.sub_add, <- N2Z.inj_div in contract_balance_bound.
      assert (H : (forall n m p, 0 <= p -> n - m = p -> m <= n)%Z).
      { intros. subst p. now apply Z.le_0_sub. }
      apply H in contract_balance_bound.
      -- eapply Z.le_trans; try apply contract_balance_bound.
         apply sumZ_in_le; eauto.
         now apply Forall_forall.
      -- apply Z.add_nonneg_nonneg; auto.
         apply N2Z.is_nonneg.
  }
  destruct can_receive_funds as [receive_not_contract | (wc & cstate' & deployed' & deployed_state' & new_state & receive_some )].
  - eexists.
    constructor.
    eapply eval_transfer; auto.
    + now apply Z.le_ge.
    + now replace amount with (act_body_amount (act_transfer to amount)); auto.
    + assumption.
    + now constructor.
  - eexists.
    constructor.
    eapply eval_call with (msg := None); eauto; cycle -1.
    + now constructor.
    + apply Z.le_ge.
      apply act_amount_positive.
    + cbn.
      replace (env_account_balances (set_contract_state to new_state (transfer_balance caddr to amount bstate)) to)
        with (((env_account_balances bstate to) + amount)%Z).
      * apply receive_some.
      * apply bat_no_self_calls in deployed; auto.
        eapply Forall_forall in deployed; eauto.
        cbn in *.
        destruct_address_eq; easy.
    + eauto.
  Unshelve. auto.
Qed.

End Theories.
End BATAltFix.
