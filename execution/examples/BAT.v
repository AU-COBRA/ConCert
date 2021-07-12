(*
  Implementation of the Basic Attention Token.
  Ported from https://github.com/brave-intl/basic-attention-token-crowdsale/blob/66c886cc4bfb0493d9e7980f392ca7921ef1e7fc/contracts/BAToken.sol
*)
From Coq Require Import ZArith.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Require EIP20Token.

Import ListNotations.
Import RecordSetNotations.

Section BAT.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Definition TokenValue := EIP20Token.TokenValue.
Open Scope N_scope.

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

Definition init (chain : Chain)
                (ctx : ContractCallContext)
                (setup : Setup) : option State :=
  let token_state := {|
      EIP20Token.balances := FMap.add setup.(_batFundDeposit) setup.(_batFund) FMap.empty;
      EIP20Token.total_supply := setup.(_batFund);
      EIP20Token.allowances := FMap.empty;
    |} in
  Some {|
    (* EIP20Token initialisation: *)
    token_state := token_state;
    (* BAT initialisation: *)
    isFinalized := false;
    fundDeposit := setup.(_fundDeposit);
    batFundDeposit := setup.(_batFundDeposit);
    fundingStart := setup.(_fundingStart);
    fundingEnd := setup.(_fundingEnd);
    tokenExchangeRate := setup.(_tokenExchangeRate);
    tokenCreationCap := setup.(_tokenCreationCap);
    tokenCreationMin := setup.(_tokenCreationMin);
  |}.

Definition returnIf (cond : bool) := if cond then None else Some tt.
Definition total_supply (state : State) := state.(token_state).(EIP20Token.total_supply).
Definition balances (state : State) := state.(token_state).(EIP20Token.balances).
Definition allowances (state : State) := state.(token_state).(EIP20Token.allowances).

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
  (* Don't allow the the batFundDeposit account to refund *)
  do _ <- returnIf (address_eqb sender state.(batFundDeposit)) ;
  do sender_bats <- FMap.find sender (balances state) ;
  do _ <- returnIf (sender_bats =? 0) ;
  let new_total_supply := (total_supply) state - sender_bats in
  (* convert tokens back to the currency of the blockchain, to be sent back to the sender address *)
  let amount_to_send := Z.of_N (sender_bats / state.(tokenExchangeRate)) in
  let new_token_state : EIP20Token.State := {|
    EIP20Token.total_supply := new_total_supply;
    EIP20Token.balances := FMap.add sender 0 (balances state);
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
  let new_state := state<|isFinalized := true|> in
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
  | Some refund => try_refund sender slot state
  | Some finalize => try_finalize sender slot contract_balance state
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
  | Some (tokenMsg msg) => do res <- EIP20Token.receive chain ctx state.(token_state) (Some msg) ;
                     let new_state := state<|token_state := fst res|> in
                         Some (new_state, snd res)
  | _ => receive_bat chain ctx state maybe_msg
  end.

Definition contract : Contract Setup Msg State :=
  build_contract init receive.

Section Theories.

Import Lia.

(* ------------------- Definitions from EIP20Token ------------------- *)

Notation isSome := EIP20Token.isSome.
Notation sumN := EIP20Token.sumN.
Notation "'sum_balances' s" := (EIP20Token.sum_balances (token_state s)) (at level 60).
Notation get_allowance := EIP20Token.get_allowance.
Notation transfer_balance_update_correct := EIP20Token.transfer_balance_update_correct.
Notation transfer_from_allowances_update_correct := EIP20Token.transfer_from_allowances_update_correct.
Notation approve_allowance_update_correct := EIP20Token.approve_allowance_update_correct.

Definition transfer t a := tokenMsg (EIP20Token.transfer t a).
Definition transfer_from f t a := tokenMsg (EIP20Token.transfer_from f t a).
Definition approve d a := tokenMsg (EIP20Token.approve d a).

Existing Instance EIP20Token.sumN_perm_proper.



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
  | H : option_map (fun s : State => (s, _)) match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
  | H : match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
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

Ltac returnIf H :=
  let G := fresh "G" in
    unfold returnIf in H;
    destruct_match eqn:G in H; try congruence;
    clear H;
    rename G into H.



(* ------------------- Transfer correct ------------------- *)

Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct (token_state prev_state) (token_state new_state) ctx.(ctx_from) to amount = true.
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_balance_correct; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_preserves_total_supply; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_transfer_preserves_allowances : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_preserves_allowances; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_transfer_preserves_other_balances : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) -> account <> to ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_preserves_other_balances; eauto.
  destruct p. subst. cbn. erewrite H2. f_equal.
Qed.

Lemma try_transfer_is_some : forall state chain ctx to amount,
  (ctx_amount ctx >? 0)%Z = false ->
  (amount = 0 /\ isSome (FMap.find (ctx_from ctx) (balances state)) = false)
  \/ amount <= with_default 0 (FMap.find (ctx_from ctx) (balances state))
    <-> isSome (receive chain ctx state (Some (transfer to amount))) = true.
Proof.
  intros.
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
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_from_balance_correct; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_transfer_from_preserves_total_supply : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_from_preserves_total_supply; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_transfer_from_preserves_other_balances : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> from -> account <> to ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_from_preserves_other_balances.
  destruct p. subst. cbn. erewrite H2. f_equal.
  all: auto.
Qed.

Lemma try_transfer_from_preserves_other_allowances : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> from ->
      FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_from_preserves_other_allowances; eauto.
  destruct p. subst. cbn. erewrite H1. f_equal.
Qed.

Lemma try_transfer_from_preserves_other_allowance : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      get_allowance (token_state prev_state) from account = get_allowance (token_state new_state) from account.
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_from_preserves_other_allowance; eauto.
  destruct p. subst. cbn. erewrite H1. f_equal.
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
  intros.
  unfold balances, allowances, get_allowance_. cbn.
  destruct_match eqn:receive;
    now erewrite EIP20Token.try_transfer_from_is_some, receive.
Qed.



(* ------------------- Approve correct ------------------- *)

Lemma try_approve_allowance_correct : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
  approve_allowance_update_correct (token_state new_state) ctx.(ctx_from) delegate amount = true.
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_approve_allowance_correct; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_approve_preserves_total_supply; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_approve_preserves_balances : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (balances prev_state) = (balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_approve_preserves_balances; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_approve_preserves_other_allowances : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_approve_preserves_other_allowances; eauto.
  destruct p. subst. cbn. erewrite H1. f_equal.
Qed.

Lemma try_approve_preserves_other_allowance : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    forall account, account <> delegate ->
      get_allowance (token_state prev_state) (ctx_from ctx) account = get_allowance (token_state new_state) (ctx_from ctx) account.
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_approve_preserves_other_allowance; eauto.
  destruct p. subst. cbn. erewrite H1. f_equal.
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
  intros.
  receive_simpl.
  now inversion H.
Qed.



(* ------------------- EIP20 functions produces no acts ------------------- *)

Lemma eip20_new_acts_correct : forall prev_state new_state chain ctx m new_acts,
  receive chain ctx prev_state (Some (tokenMsg m)) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros.
  receive_simpl.
  destruct p.
  apply EIP20Token.EIP20_no_acts in H0.
  now inversion H.
Qed.



(* ------------------- Create_tokens correct ------------------- *)

Lemma try_create_tokens_balance_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    with_default 0 (FMap.find (ctx_from ctx) (balances prev_state)) =
    with_default 0 (FMap.find (ctx_from ctx) (balances new_state)) - ((Z.to_N (ctx_amount ctx)) * (tokenExchangeRate prev_state)).
Proof.
  intros.
  receive_simpl.
  inversion H.
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
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_create_tokens_preserves_other_balances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  setoid_rewrite EIP20Token.add_is_partial_alter_plus; auto.
  now setoid_rewrite FMap.find_add_ne.
Qed.

Lemma try_create_tokens_preserves_allowances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_create_tokens_only_change_token_state : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    prev_state<|token_state := (token_state new_state)|> = new_state.
Proof.
  intros.
  receive_simpl.
  now inversion H.
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
  - intros. receive_simpl.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    destruct_match eqn:match1. destruct_match eqn:match2. destruct_match eqn:match3.
    + easy.
    + returnIf match3.
      rewrite N.ltb_lt in match3. lia.
    + returnIf match2.
      rewrite Z.leb_le in match2. lia.
    + returnIf match1.
      do 2 rewrite Bool.orb_true_iff in match1.
      destruct match1 as [[H2' | H3'] | H4'].
      * easy.
      * rewrite Nat.ltb_lt in H3'. easy.
      * rewrite Nat.ltb_lt in H4'. easy.
  - intros.
    destruct H as [x [y H]].
    receive_simpl.
    returnIf H0; returnIf H1; returnIf H2.
    apply Bool.orb_false_iff in H0 as [H0 H4];
    apply Bool.orb_false_iff in H0 as [H0 H3].
    repeat split.
    + now rewrite Z.leb_gt in H1.
    + assumption.
    + now apply Nat.ltb_ge in H3.
    + now apply Nat.ltb_ge in H4.
    + now apply N.ltb_ge in H2.
Qed.

Lemma try_create_tokens_acts_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros.
  receive_simpl.
Qed.



(* ------------------- Finalize correct ------------------- *)

Lemma try_finalize_isFinalized_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    (isFinalized prev_state) = false /\ (isFinalized new_state) = true.
Proof.
  intros.
  receive_simpl.
  inversion H.
  split.
  - returnIf H0.
    now do 2 apply Bool.orb_false_iff in H0 as [H0 _].
  - reflexivity.
Qed.

Lemma try_finalize_only_change_isFinalized : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    prev_state<|isFinalized := (isFinalized new_state)|> = new_state.
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_finalize_preserves_total_supply : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros.
  apply try_finalize_only_change_isFinalized in H.
  now rewrite <- H.
Qed.

Lemma try_finalize_is_some : forall state chain ctx,
  (isFinalized state) = false
  /\ (ctx_from ctx) = (fundDeposit state)
  /\ (tokenCreationMin state) <= (total_supply state)
  /\ ((fundingEnd state) < (current_slot chain) \/ (tokenCreationCap state) = (total_supply state))%nat
    <-> exists x y, receive chain ctx state (Some finalize) = Some (x, y).
Proof.
  split.
  - intros. receive_simpl.
    destruct H as [H1 [H2 [H3 H4]]].
    destruct_match eqn:match1. destruct_match eqn:match2.
    + easy.
    + returnIf match2.
      apply Bool.andb_true_iff in match2 as [H4' H5'].
      destruct H4 as [H4 | H5].
      * now rewrite Nat.leb_le in H4'.
      * now rewrite Bool.negb_true_iff, N.eqb_neq in H5'.
    + returnIf match1.
      do 2 rewrite Bool.orb_true_iff in match1.
      destruct match1 as [[H1' | H2'] | H3'].
      * easy.
      * rewrite Bool.negb_true_iff in H2'. now destruct_address_eq.
      * now rewrite N.ltb_lt in H3'.
  - intros.
    destruct H as [x [y H]].
    receive_simpl.
    returnIf H0.
    returnIf H1.
    apply Bool.orb_false_iff in H0 as [H0 H3].
    apply Bool.orb_false_iff in H0 as [H0 H2].
    repeat split.
    + assumption.
    + now destruct_address_eq.
    + now rewrite N.ltb_ge in H3.
    + apply Bool.andb_false_iff in H1 as [H4 | H5].
      * left. now rewrite Nat.leb_gt in H4.
      * right. now rewrite Bool.negb_false_iff, N.eqb_eq in H5.
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
    with_default 0 (FMap.find (ctx_from ctx) (balances new_state)) = 0.
Proof.
  intros.
  receive_simpl.
  inversion H.
  now setoid_rewrite FMap.find_add.
Qed.

Lemma try_refund_total_supply_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    (total_supply prev_state) - (with_default 0 (FMap.find (ctx_from ctx) (balances prev_state))) =
    (total_supply new_state).
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_refund_preserves_other_balances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  now setoid_rewrite FMap.find_add_ne.
Qed.

Lemma try_refund_preserves_allowances : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_refund_only_change_token_state : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    prev_state<|token_state := (token_state new_state)|> = new_state.
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_refund_is_some : forall state chain ctx,
  (isFinalized state) = false
  /\ ((fundingEnd state) < (current_slot chain))%nat
  /\ (total_supply state) < (tokenCreationMin state)
  /\ (ctx_from ctx) <> (batFundDeposit state)
  /\ 0 < with_default 0 (FMap.find (ctx_from ctx) (balances state))
    <-> isSome (receive chain ctx state (Some refund)) = true.
Proof.
  split.
  - intros. receive_simpl.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    destruct_match eqn:match1. destruct_match eqn:match2. destruct_match eqn:from_balance. destruct_match eqn:match3.
    + easy.
    + returnIf match3.
      rewrite N.eqb_eq in match3.
      now rewrite match3 in H5.
    + easy.
    + returnIf match2. now destruct_address_eq.
    + returnIf match1.
      do 2 rewrite Bool.orb_true_iff in match1.
      destruct match1 as [[H1' | H2'] | H3'].
      * congruence.
      * now rewrite Nat.leb_le in H2'.
      * now rewrite N.leb_le in H3'.
  - intros. receive_simpl.
    do 5 try split;
      destruct_match eqn:H1 in H; cbn in H; try discriminate;
      destruct_match eqn:H4 in H; cbn in H; try discriminate;
      destruct_match eqn:from_balance in H; cbn in H; try discriminate;
      destruct_match eqn:H5 in H; cbn in H; try discriminate;
      returnIf H1; returnIf H4; returnIf H5;
      apply Bool.orb_false_iff in H1 as [H1 H3];
      apply Bool.orb_false_iff in H1 as [H1 H2].
    + assumption.
    + now apply Nat.leb_gt in H2.
    + now apply N.leb_gt in H3.
    + now destruct_address_eq.
    + cbn. now rewrite N.eqb_neq in H5.
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

Lemma init_bat_balance_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    with_default 0 (FMap.find state.(batFundDeposit) (balances state)) = setup.(_batFund).
Proof.
  intros.
  inversion H.
  now setoid_rewrite FMap.find_add.
Qed.

Lemma init_other_balances_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    forall account, account <> state.(batFundDeposit) ->
    with_default 0 (FMap.find account (balances state)) = 0.
Proof.
  intros.
  inversion H.
  cbn.
  setoid_rewrite FMap.find_add_ne.
  - now setoid_rewrite FMap.find_empty.
  - subst. auto.
Qed.

Lemma init_allowances_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    (allowances state) = FMap.empty.
Proof.
  intros.
  now inversion H.
Qed.

Lemma init_isFinalized_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    state.(isFinalized) = false.
Proof.
  intros.
  now inversion H.
Qed.

Lemma init_total_supply_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    (total_supply state) = setup.(_batFund).
Proof.
  intros.
  now inversion H.
Qed.

Lemma init_constants_correct : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    state.(fundDeposit) = setup.(_fundDeposit)
    /\ state.(batFundDeposit) = setup.(_batFundDeposit)
    /\ state.(fundingStart) = setup.(_fundingStart)
    /\ state.(fundingEnd) = setup.(_fundingEnd)
    /\ state.(tokenExchangeRate) = setup.(_tokenExchangeRate)
    /\ state.(tokenCreationCap) = setup.(_tokenCreationCap)
    /\ state.(tokenCreationMin) = setup.(_tokenCreationMin).
Proof.
  intros.
  now inversion H.
Qed.



(* ------------------- Functions preserve sum of balances ------------------- *)

Lemma try_transfer_preserves_balances_sum : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_preserves_balances_sum; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_transfer_from_preserves_balances_sum : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_transfer_from_preserves_balances_sum; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_approve_preserves_balances_sum : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  eapply EIP20Token.try_approve_preserves_balances_sum; eauto.
  destruct p. subst. cbn. erewrite H0. f_equal.
Qed.

Lemma try_create_tokens_update_balances_sum : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some create_tokens) = Some (new_state, new_acts) ->
    (sum_balances prev_state) + ((Z.to_N (ctx_amount ctx)) * (tokenExchangeRate prev_state)) = (sum_balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H.
  unfold EIP20Token.sum_balances. cbn in *. clear H H4 H5.
  setoid_rewrite EIP20Token.add_is_partial_alter_plus; auto.
  destruct (FMap.find (ctx_from ctx) (balances prev_state)) eqn:from_balance.
  - setoid_rewrite from_balance.
    setoid_rewrite FMap.elements_add_existing; eauto.
    rewrite EIP20Token.sumN_split with (x:=ctx_from ctx), EIP20Token.sumN_swap.
    rewrite fin_maps.map_to_list_delete; auto.
    now rewrite N.add_comm.
  - setoid_rewrite from_balance.
    setoid_rewrite FMap.elements_add; auto.
    now rewrite N.add_comm.
Qed.

Lemma try_finalize_preserves_balances_sum : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some finalize) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_refund_update_balances_sum : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state (Some refund) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state) + (with_default 0 (FMap.find (ctx_from ctx) (balances prev_state))).
Proof.
  intros.
  receive_simpl.
  inversion H. unfold EIP20Token.sum_balances. clear H H5 H6.
  setoid_rewrite FMap.elements_add_existing; eauto.
  rewrite EIP20Token.sumN_add with (x:=ctx_from ctx), EIP20Token.sumN_swap.
  rewrite fin_maps.map_to_list_delete; eauto.
Qed.

Lemma init_update_balances_sum : forall state chain ctx setup,
  init chain ctx setup = Some (state) ->
    (sum_balances state) = (total_supply state).
Proof.
  intros.
  inversion H. unfold EIP20Token.sum_balances. subst. cbn.
  setoid_rewrite FMap.elements_add; auto.
  rewrite fin_maps.map_to_list_empty.
  now apply N.add_0_r.
Qed.



(* ------------------- Sum of balances always equals total supply ------------------- *)

Lemma sum_balances_eq_total_supply block_state contract_addr :
  reachable block_state ->
  env_contracts block_state contract_addr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state block_state contract_addr = Some cstate
    /\ (total_supply cstate) = (sum_balances cstate).
Proof.
  contract_induction; intros; try auto.
  - now apply init_update_balances_sum in init_some.
  - destruct msg. destruct m. destruct m.
    + apply try_transfer_preserves_balances_sum in receive_some as balance_sum.
      apply try_transfer_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_transfer_from_preserves_balances_sum in receive_some as balance_sum.
      apply try_transfer_from_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_approve_preserves_balances_sum in receive_some as balance_sum.
      apply try_approve_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_create_tokens_update_balances_sum in receive_some as balance_sum.
      apply try_create_tokens_total_supply_correct in receive_some.
      now rewrite <- balance_sum, <- receive_some, N.add_cancel_r.
    + apply try_finalize_preserves_balances_sum in receive_some as balance_sum.
      apply try_finalize_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_refund_update_balances_sum in receive_some as balance_sum.
      apply try_refund_total_supply_correct in receive_some.
      rewrite IH in receive_some. rewrite <- receive_some, balance_sum.
      now rewrite N.add_sub.
    + cbn in receive_some. congruence.
  - destruct msg. destruct m. destruct m.
    + apply try_transfer_preserves_balances_sum in receive_some as balance_sum.
      apply try_transfer_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_transfer_from_preserves_balances_sum in receive_some as balance_sum.
      apply try_transfer_from_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_approve_preserves_balances_sum in receive_some as balance_sum.
      apply try_approve_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_create_tokens_update_balances_sum in receive_some as balance_sum.
      apply try_create_tokens_total_supply_correct in receive_some.
      now rewrite <- balance_sum, <- receive_some, N.add_cancel_r.
    + apply try_finalize_preserves_balances_sum in receive_some as balance_sum.
      apply try_finalize_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_refund_update_balances_sum in receive_some as balance_sum.
      apply try_refund_total_supply_correct in receive_some.
      rewrite IH in receive_some. rewrite <- receive_some, balance_sum.
      now rewrite N.add_sub.
    + cbn in receive_some. congruence.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ => True).
    unset_all; subst;cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.



(* ------------------- Constants are constant ------------------- *)

Lemma receive_preserves_constants : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
       prev_state.(fundDeposit) = new_state.(fundDeposit)
    /\ prev_state.(batFundDeposit) = new_state.(batFundDeposit)
    /\ prev_state.(fundingStart) = new_state.(fundingStart)
    /\ prev_state.(fundingEnd) = new_state.(fundingEnd)
    /\ prev_state.(tokenExchangeRate) = new_state.(tokenExchangeRate)
    /\ prev_state.(tokenCreationCap) = new_state.(tokenCreationCap)
    /\ prev_state.(tokenCreationMin) = new_state.(tokenCreationMin).
Proof.
  intros.
  destruct msg. destruct m. destruct m.
  all: receive_simpl; now inversion H.
Qed.

Lemma constants_are_constant block_state contract_addr (trace : ChainTrace empty_state block_state) :
  env_contracts block_state contract_addr = Some (contract : WeakContract) ->
  exists cstate deploy_info,
    contract_state block_state contract_addr = Some cstate
    /\ deployment_info _ trace contract_addr = Some deploy_info
    /\ let setup := deploy_info.(deployment_setup) in
         cstate.(fundDeposit) = setup.(_fundDeposit)
      /\ cstate.(batFundDeposit) = setup.(_batFundDeposit)
      /\ cstate.(fundingStart) = setup.(_fundingStart)
      /\ cstate.(fundingEnd) = setup.(_fundingEnd)
      /\ cstate.(tokenExchangeRate) = setup.(_tokenExchangeRate)
      /\ cstate.(tokenCreationCap) = setup.(_tokenCreationCap)
      /\ cstate.(tokenCreationMin) = setup.(_tokenCreationMin).
Proof.
  contract_induction; intros; auto.
  - now apply init_constants_correct in init_some.
  - now apply receive_preserves_constants in receive_some.
  - now apply receive_preserves_constants in receive_some.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ => True).
    unset_all; subst;cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.



(* ------------------- Finalize cannot be undone ------------------- *)

Lemma final_is_final : forall prev_state new_state chain ctx msg new_acts,
  (isFinalized prev_state) = true /\
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
    (isFinalized new_state) = true.
Proof.
  intros.
  destruct H as [H receive].
  destruct msg. destruct m.
  - apply eip_only_changes_token_state in receive.
    now rewrite <- receive.
  - apply try_create_tokens_only_change_token_state in receive.
    now rewrite <- receive.
  - now apply try_finalize_isFinalized_correct in receive as [_ receive].
  - apply try_refund_only_change_token_state in receive.
    now rewrite <- receive.
  - cbn in receive. congruence.
Qed.



Require Import ZArith_base.
Import ResultMonad.
Context  {ChainBuilder : ChainBuilderType}.
Notation serializeMsg := (@serialize BAT.Msg _).
Notation serializeState := (@serialize BAT.State _).
From ConCert.Execution.Examples Require Import BuildUtils.

Definition total_balance bstate accounts : Amount :=
  let account_balance := env_account_balances bstate in
    sumZ (fun acc => account_balance acc) accounts.

Lemma sum_balances_positive : forall bstate accounts,
  reachable bstate ->
  (0 <= sumZ (fun acc : Address => env_account_balances bstate acc) accounts)%Z.
Proof.
  intros.
  induction accounts; cbn.
  - lia.
  - apply Z.add_nonneg_nonneg; auto.
    eapply account_balance_nonnegative in H.
    now apply Z.ge_le.
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
  - eapply account_balance_nonnegative in H. now apply Z.ge_le.
  - now apply sum_balances_positive.
Qed.

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

Lemma forall_account_balances_eq : forall P accounts env1 env2,
  (forall a, In a accounts -> env_account_balances env1 a = env_account_balances env2 a) ->
  Forall (fun acc => P (env_account_balances env1 acc)) accounts <->
  Forall (fun acc => P (env_account_balances env2 acc)) accounts.
Proof.
  intros.
  assert (map_eq : map (env_account_balances env1) accounts = map (env_account_balances env2) accounts)
    by now apply map_ext_in.
  split;
    intro;
    apply All_Forall.Forall_map in H0;
    apply All_Forall.Forall_map_inv;
    now rewrite ? map_eq.
Qed.

Definition block_header bstate slot creator reward : BlockHeader :=
  {| block_height := S (chain_height bstate);
      block_slot := slot;
      block_finalized_height := finalized_height bstate;
      block_creator := creator;
      block_reward := reward; |}.

Definition finalize_act cstate caddr : Action :=
  build_act (fundDeposit cstate) (act_call caddr 0%Z (serializeMsg finalize)).

Definition finalize_transfer_act cstate env caddr : Action :=
  build_act caddr (act_transfer (fundDeposit cstate) (env_account_balances env caddr)).

Definition create_tokens_act env caddr sender : Action :=
  build_act sender (act_call caddr (env_account_balances env sender) (serializeMsg create_tokens)).

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

Hint Resolve N_le_add_distr N_le_sub N_div_mul_le N_le_div_mul : core.

Lemma can_finalize_if_creation_min : forall bstate (reward : Amount) (caddr creator : Address),
  address_is_contract creator = false ->
  (reward >= 0)%Z ->
  reachable bstate ->
  (chain_state_queue bstate) = [] ->
  (exists cstate,
    env_contracts bstate caddr = Some (BAT.contract : WeakContract)
    /\ env_contract_states bstate caddr = Some (serializeState cstate)
    /\ (tokenCreationMin cstate) <= (total_supply cstate)
    /\ address_is_contract (fundDeposit cstate) = false)
      ->
      exists bstate', reachable_through bstate bstate'
        /\ (chain_state_queue bstate') = []
        /\ exists cstate',
        env_contracts bstate' caddr = Some (BAT.contract : WeakContract)
        /\ env_contract_states bstate' caddr = Some (serializeState cstate')
        /\ (isFinalized cstate') = true.
Proof.
  intros bstate reward caddr creator Hcreator Hreward bstate_reachable bstate_queue
    [cstate [contract_deployed [deployed_state [creation_min fund_deposit_not_contract]]]].
  (* First check if contract is already finalized, if it is we just use the current state to finish proof *)
  destruct (isFinalized cstate) eqn:finalized; [eexists; split; eauto|].
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
  update (S (fundingEnd cstate) <= current_slot bstate)%nat in slot_hit by
    (rewrite_environment_equiv; cbn; easy).
  update_all.
  (* We can now evaluate the action we added giving us a ChainState where
      the token is in its finalized state *)
  evaluate_action BAT.contract; try easy.
  - now apply account_balance_nonnegative.
  - specialize (try_finalize_is_some cstate bstate) as [[x [y H]] _]; cycle 1.
    + specialize try_finalize_isFinalized_correct as [_ H1]; eauto.
      now erewrite <- (try_finalize_only_change_isFinalized _ _ _ _ _ H),
                   H1, (try_finalize_acts_correct _ _ _ _ _ H) in H.
    + eauto.
  - cbn in *.
    clear deployed_state.
    update_all;
      [rewrite queue; do 3 f_equal;repeat (rewrite_environment_equiv; cbn; destruct_address_eq; try easy)|].
    (* Finally we need to evaluate the new transfer action that finalize produced *)
    evaluate_transfer; try easy.
    + destruct_address_eq;
      try rewrite Z.add_0_r;
      now apply account_balance_nonnegative.
    + destruct_address_eq;
      try rewrite Z.add_0_r;
      apply Z.le_ge, Z.le_refl.
    + exists bstate.
      split; eauto.
      split; eauto.
      eexists.
      now repeat split; try (rewrite_environment_equiv; cbn; eauto).
Qed.

Fixpoint create_token_acts (env : Environment) caddr accounts tokens_left exchange_rate:=
  let create_tokens_act sender amount := build_act sender (act_call caddr amount (serializeMsg create_tokens)) in
    match accounts with
    | [] => []
    | acc :: accounts' =>
      if 0 <? tokens_left
      then
        let amount := 1 + ((tokens_left / exchange_rate)) in
        let amount := N.min amount (Z.to_N (env_account_balances env acc)) in
          (create_tokens_act acc (Z.of_N amount)) ::
          create_token_acts env caddr accounts' (N.sub tokens_left (amount * exchange_rate)) exchange_rate
      else
        create_token_acts env caddr accounts' tokens_left exchange_rate
    end.

Lemma create_token_acts_cons : forall caddr env acc accounts tokens_left exchange_rate,
  let create_tokens_act sender amount := build_act sender (act_call caddr amount (serializeMsg create_tokens)) in
  let amount' := 1 + ((tokens_left / exchange_rate)) in
  let amount := N.min amount' (Z.to_N (env_account_balances env acc)) in
  let act := create_tokens_act acc (Z.of_N amount) in
  0 < tokens_left->
  create_token_acts env caddr (acc :: accounts) tokens_left exchange_rate =
  act :: (create_token_acts env caddr accounts (tokens_left - (amount * exchange_rate))) exchange_rate.
Proof.
  intros.
  cbn.
  apply N.ltb_lt in H.
  rewrite H.
  f_equal.
Qed.

Lemma create_token_acts_eq : forall caddr env1 env2 accounts tokens_left exchange_rate,
  (forall a, In a accounts -> env_account_balances env1 a = env_account_balances env2 a) ->
    create_token_acts env1 caddr accounts tokens_left exchange_rate =
    create_token_acts env2 caddr accounts tokens_left exchange_rate.
Proof.
  induction accounts; intros.
  - reflexivity.
  - cbn.
    rewrite H; [| apply in_eq].
    now do 2 (rewrite <- IHaccounts; [| intros; now apply H, in_cons]).
Qed.

Lemma create_token_acts_is_account : forall caddr env accounts tokens_left exchange_rate,
  Forall (fun acc : Address => address_is_contract acc = false) accounts ->
    (forall x : Action, In x (create_token_acts env caddr accounts tokens_left exchange_rate) -> act_is_from_account x).
Proof.
  induction accounts; intros.
  - inversion H0.
  - cbn in H0.
    apply list.Forall_cons in H as [H H'].
    destruct_match in H0.
    + destruct H0 as [].
      * now subst.
      * now eapply IHaccounts.
    + now eapply IHaccounts.
Qed.

Lemma can_finalize_if_deployed : forall deployed_bstate accounts (reward : Amount) (caddr creator : Address),
  address_is_contract creator = false ->
  (reward >= 0)%Z ->
  (exists deployed_cstate,
    reachable deployed_bstate
    /\ (chain_state_queue deployed_bstate) = []
    /\ env_contracts deployed_bstate caddr = Some (BAT.contract : WeakContract)
    /\ env_contract_states deployed_bstate caddr = Some (serializeState deployed_cstate)
    /\ (((tokenCreationMin deployed_cstate) - (total_supply deployed_cstate))) <=
            ((Z.to_N (total_balance deployed_bstate accounts)) * (tokenExchangeRate deployed_cstate))
    /\ deployed_cstate.(tokenExchangeRate) <= deployed_cstate.(tokenCreationCap) - deployed_cstate.(tokenCreationMin)
    /\ ((fundingStart deployed_cstate) <= (current_slot (env_chain deployed_bstate)))%nat
    /\ ((current_slot (env_chain deployed_bstate)) < (fundingEnd deployed_cstate))%nat
    /\ address_is_contract (fundDeposit deployed_cstate) = false
    /\ Forall (fun acc => Z.lt 0 (env_account_balances deployed_bstate acc)) accounts
    /\ NoDup accounts
    /\ ~ In caddr accounts
    /\ Forall (fun acc => address_is_contract acc = false) accounts
    /\ ~ In creator accounts
    /\ deployed_cstate.(tokenExchangeRate) <> 0)
      ->
      exists bstate, reachable_through deployed_bstate bstate
        /\ (chain_state_queue bstate) = []
        /\ exists cstate,
        env_contracts bstate caddr = Some (BAT.contract : WeakContract)
        /\ env_contract_states bstate caddr = Some (serializeState cstate)
        /\ (isFinalized cstate) = true.
Proof.
  intros deployed_bstate accounts reward caddr creator Hcreator Hreward
    [deployed_cstate [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]]].
  destruct (isFinalized deployed_cstate) eqn:finalized;[eexists; split; eauto|].

  add_block (create_token_acts deployed_bstate caddr accounts
          ((tokenCreationMin deployed_cstate) - (total_supply deployed_cstate)) deployed_cstate.(tokenExchangeRate)) 1%nat;
    only 1: apply Hcreator; eauto; [now apply All_Forall.In_Forall, create_token_acts_is_account | ].
  update ((current_slot bstate) <= (fundingEnd deployed_cstate))%nat in H8 by
    (rewrite_environment_equiv; cbn; lia).
  update_all.
  { rewrite queue. apply create_token_acts_eq. intros.
    rewrite_environment_equiv. cbn. now destruct_address_eq.
  }
  { setoid_rewrite env_eq.
    now erewrite forall_account_balances_eq by (intros; cbn; now destruct_address_eq). 
  }
  { now erewrite total_balance_eq by (intros; rewrite_environment_equiv; cbn; now destruct_address_eq). }
  generalize dependent bstate.
  generalize dependent deployed_cstate.

  induction accounts; intros.
  - apply N.le_0_r, N.sub_0_le in H5.
    specialize (can_finalize_if_creation_min bstate reward caddr creator).
    intros []; eauto.
  - apply list.Forall_cons in H10 as [H10 H10'].
    apply NoDup_cons_iff in H11 as [H11 H11'].
    apply not_in_cons in H12 as [H12 H12'].
    apply list.Forall_cons in H13 as [H13 H13'].
    apply not_in_cons in H14 as [H14 H14'].
    destruct (tokenCreationMin deployed_cstate - total_supply deployed_cstate) eqn:tokens_left_to_fund.
    + eapply IHaccounts; eauto.
      * now rewrite tokens_left_to_fund.
      * rewrite tokens_left_to_fund.
        apply N.le_0_l.
    + pose (created_amount := N.min (1 + (((tokenCreationMin deployed_cstate - total_supply deployed_cstate) / (tokenExchangeRate deployed_cstate))))
                                      (Z.to_N (env_account_balances bstate a))).
      pose (token_state_tmp := (token_state deployed_cstate)
            <|EIP20Token.total_supply := (total_supply deployed_cstate) + (created_amount * tokenExchangeRate deployed_cstate)|>
            <|EIP20Token.balances := FMap.partial_alter
                                       (fun balance : option N =>
                                        Some
                                          (with_default 0 balance + (created_amount * tokenExchangeRate deployed_cstate))) a
                                       (balances deployed_cstate)|>).
      pose (cstate_tmp := deployed_cstate<|token_state := token_state_tmp|>).
      rewrite <- tokens_left_to_fund in *.
      clear Hreward.
      evaluate_action BAT.contract; try easy.
      * now rewrite create_token_acts_cons by lia.
      * apply Z.le_ge, N2Z.is_nonneg.
      * nia.
      * apply Nat.ltb_ge in H7.
        apply Nat.ltb_ge in H8.
        cbn.
        rewrite finalized, H7, H8, N2Z.inj_min, Z2N.id;
        try (apply Z.ge_le, account_balance_nonnegative; eauto).
        cbn.
        destruct_match eqn:match_amount; returnIf match_amount.
        destruct_match eqn:match_cap; returnIf match_cap.
        -- eauto.
        -- apply N.ltb_lt in match_cap.
           apply Z.leb_gt, Z.min_glb_lt_iff in match_amount as [].
           rewrite Z2N.inj_min, N2Z.id, <- N.mul_min_distr_r, <- N.add_min_distr_l, N.min_glb_lt_iff in match_cap.
           destruct match_cap.
           apply N.lt_le_trans with (p := (tokenCreationMin deployed_cstate) + tokenExchangeRate deployed_cstate) in H1.
           nia.
           rewrite N.mul_add_distr_r, N.mul_1_l.
           rewrite N.add_assoc, N.add_comm, N.add_assoc.
           rewrite <- N.add_le_mono_r.
           apply N_le_sub. lia.
           now apply N_div_mul_le.
        -- apply Zle_bool_imp_le, Z.min_le in match_amount as [].
         --- rewrite <- N2Z.inj_0 in H.
             now apply N2Z.inj_le, N_le_add_distr in H.
         --- lia.
      * assert (env_balances_eq : forall a, In a accounts -> env_account_balances bstate0 a = env_account_balances bstate a)
          by (intros; rewrite_environment_equiv; cbn; now destruct_address_eq).
        edestruct IHaccounts with (bstate := bstate0) (deployed_cstate := cstate_tmp); eauto; try (rewrite_environment_equiv; eauto).
        -- now rewrite deployed_state, Z2N.inj_min, N2Z.id.
        -- rewrite queue0. unfold cstate_tmp, token_state_tmp. cbn. fold created_amount.
           rewrite N.sub_add_distr.
           apply create_token_acts_eq.
           intros. rewrite_environment_equiv. cbn. now destruct_address_eq.
        -- now erewrite forall_account_balances_eq.
        -- edestruct N.min_dec in created_amount.
          --- cbn. rewrite e.
             eapply N.le_trans; [| apply N.le_0_l].
             rewrite N.mul_add_distr_r, N.mul_1_l.
             apply N.le_0_r.
             rewrite N.sub_add_distr.
             rewrite N.sub_add_distr.
             apply N.sub_0_le.
             now apply N_le_div_mul.
          --- rewrite total_balance_distr, N.add_comm in H5; eauto.
             erewrite total_balance_eq by auto.
             apply N.le_sub_le_add_r in H5.
             rewrite <- N.sub_add_distr in H5.
             eapply N.le_trans; [| apply H5].
             apply N.sub_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r.
             lia.
        -- destruct H as [H H'].
           now exists x.
Qed.

End Theories.
End BAT.
