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
    EIP20Token.balances := FMap.add sender tokens (balances state);
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

(* ------------------- Definitions from EIP20Token ------------------- *)

Notation isSome := EIP20Token.isSome.
Notation sumN := EIP20Token.sumN.
Notation get_allowance := EIP20Token.get_allowance.
Notation transfer_balance_update_correct := EIP20Token.transfer_balance_update_correct.
Notation transfer_from_allowances_update_correct := EIP20Token.transfer_from_allowances_update_correct.
Notation approve_allowance_update_correct := EIP20Token.approve_allowance_update_correct.
Definition transfer t a := tokenMsg (EIP20Token.transfer t a).
Definition transfer_from f t a := tokenMsg (EIP20Token.transfer_from f t a).
Definition approve d a := tokenMsg (EIP20Token.approve d a).

Local Open Scope nat.

Definition total_balance bstate accounts : Amount :=
  let account_balance := env_account_balances bstate in
    fold_left (fun a b => Z.add a (account_balance b)) accounts 0%Z.

Lemma can_finalize : forall bstate caddr cstate accounts,
  reachable bstate ->
  env_contracts bstate caddr = Some (BAT.contract : WeakContract) ->
  contract_state bstate caddr = Some cstate ->
  cstate.(fundingStart) < cstate.(fundingEnd)
    /\ current_slot (env_chain bstate) < fundingEnd cstate
    /\ N.ge (Z.to_N (total_balance bstate accounts)) ((tokenCreationMin cstate) - (total_supply cstate)) ->
      exists bstate_new cstate_new, reachable bstate_new /\ contract_state bstate_new caddr = Some cstate_new /\ isFinalized cstate_new = true.
Proof.
Admitted.
(*  intros. simpl in *. destruct H2 as [H2 [H3 H4]].
  induction accounts.
  - simpl in *. destruct cstate. simpl in *. *)
    

End Theories.
End BAT.
