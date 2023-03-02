(** * Basic Attention Token contract *)
(** This implementation of the Basic Attention Token is a based on
    https://github.com/brave-intl/basic-attention-token-crowdsale/blob/66c886cc4bfb0493d9e7980f392ca7921ef1e7fc/contracts/BAToken.sol
    The implementation includes some minor changes that fixes bugs present in the original Solidity implementation.

    This file contains contract function definitions.
    All contract types and utility functions are defined in [ConCert.Examples.BAT.BATCommon].
    Proofs for this contract can be found in [ConCert.Examples.BAT.BATAltFixCorrect].

    The BAT contract is a combination of a EIP20 token contract and a crowdsale contract.
    This implementation extends the EIP20 contract implemented in [ConCert.Execution.Examples.EIP20Token].
*)
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith_base.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Examples.BAT Require Import BATCommon.
From ConCert.Examples.EIP20 Require EIP20Token.



(** * Contract functions *)
Section BATAltFix.
  Context {BaseTypes : ChainBase}.

  Open Scope N_scope.
  (** ** Init *)
  (** This function only gets called once when contract is deployed.
      Will set up the initial storage state of the contract.
  *)
  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : Setup)
                  : result State Error :=
    (** BAToken should not be deployable if one of the following conditions does not hold on "setup"
      - funding period is non-empty
      - funding period does not start before the slot where the contract is deployed
      - minimum tokens to fund should not be less than the maximum tokens allowed
      - the initial supply of tokens should be less than the maximum tokens allowed
      - token exchange rate must be larger than 0
      - it must be possible to get over minimum token bound without going over maximum
      For the last condition we check that "exchange rate <= token cap - token min", however this does exclude
      a few possible configurations where the contract still works as intended, however these are not likely to
      come up in real use cases.
    *)
    do _ <- throwIf ((setup.(_fundingEnd) <=? setup.(_fundingStart))%nat
            || (setup.(_fundingStart) <? chain.(current_slot))%nat
            || (setup.(_tokenCreationCap) <? setup.(_tokenCreationMin))
            || (setup.(_tokenExchangeRate) =? 0)
            || ((setup.(_tokenCreationCap) - setup.(_tokenCreationMin)) <? setup.(_tokenExchangeRate))
            || address_eqb setup.(_batFundDeposit) ctx.(ctx_contract_address)
            || address_eqb setup.(_fundDeposit) ctx.(ctx_contract_address)) default_error;
    let token_state := {|
        EIP20Token.balances := FMap.empty;
        EIP20Token.total_supply := 0;
        EIP20Token.allowances := FMap.empty;
      |} in
    Ok {|
      (** EIP20Token initialization: *)
      token_state := token_state;
      (** BAT initialization: *)
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

  (** ** Create Tokens *)
  (** This entrypoint allows users to fund the crowdsale in return for tokens *)
  Definition try_create_tokens (sender : Address)
                               (sender_payload : Amount)
                               (current_slot : nat)
                               (state : State)
                               : result State Error :=
  (** Early return if funding is finalized, funding period
      hasn't started yet, or funding period is over *)
    do _ <- throwIf (state.(isFinalized)
            || (Nat.ltb current_slot state.(fundingStart))
            || (Nat.ltb state.(fundingEnd) current_slot)) default_error;
    (** Here we deviate slightly from the reference implementation. They only check for = 0,
        but since ConCert's payloads may be negative numbers, we must extend this check to <= 0 *)
    do _ <- throwIf (Z.leb sender_payload 0) default_error;
    (** Note: this conversion from Z to N is safe because by assumption sender_payload > 0 *)
    let tokens := (Z.to_N sender_payload) * state.(tokenExchangeRate) in
    let checkedSupply := (total_supply state) + tokens in
    do _ <- throwIf (state.(tokenCreationCap) <? checkedSupply) default_error;
    let new_token_state : EIP20Token.State := {|
      EIP20Token.total_supply := checkedSupply;
      EIP20Token.balances := FMap.partial_alter (fun balance =>
        Some (with_default 0 balance + tokens)) sender (balances state);
      EIP20Token.allowances := allowances state;
    |} in
    Ok (state<|token_state := new_token_state|>).

  (** ** Refund *)
  (** This entrypoint can be called if crowdsale is not successfully funded.
      Users calling this entrypoint will have their tokens removed and get their money refunded.
  *)
  Definition try_refund (sender : Address)
                        (current_slot : nat)
                        (state : State)
                        : result (State * list ActionBody) Error :=
    (** Early return if funding is finalized, or funding period is NOT over,
        or if total supply exceeds or is equal to the minimum fund tokens. *)
    do _ <- throwIf (state.(isFinalized)
            || (Nat.leb current_slot state.(fundingEnd))
            || (state.(tokenCreationMin) <=? (total_supply state))) default_error;
    do sender_bats <- result_of_option (FMap.find sender (balances state)) default_error;
    do _ <- throwIf (sender_bats =? 0) default_error;
    (** Convert tokens back to the currency of the blockchain, to be sent back to the sender address *)
    let amount_to_send := Z.of_N (sender_bats / state.(tokenExchangeRate)) in
    let new_total_supply := (total_supply) state - sender_bats + (N.modulo sender_bats state.(tokenExchangeRate)) in
    let new_token_state : EIP20Token.State := {|
      EIP20Token.total_supply := new_total_supply;
      EIP20Token.balances := FMap.add sender (N.modulo sender_bats state.(tokenExchangeRate)) (balances state);
      EIP20Token.allowances := allowances state;
    |} in
    let new_state := state<|token_state := new_token_state|> in
    let send_act := act_transfer sender amount_to_send in
      Ok (new_state, [send_act]).

  (** ** Finalize *)
  (** This entrypoint will end the crowdsale and pay out the money to the owner.
      Can only be called if funding was successful.
  *)
  Definition try_finalize (sender : Address)
                          (current_slot : nat)
                          (contract_balance : Amount)
                          (state : State)
                          : result (State * list ActionBody) Error :=
    (** Early return if funding is finalized, or if sender is NOT the fund deposit address,
        or if the total token supply is less than the minimum required amount,
        or if it is too early to end funding and the total token supply has not reached the cap.
        Note: the last requirement makes it possible to end a funding early if the cap has been reached.
    *)
    do _ <- throwIf (state.(isFinalized) ||
                    (address_neqb sender state.(fundDeposit)) ||
                    ((total_supply state) <? state.(tokenCreationMin))) default_error;
    do _ <- throwIf ((Nat.leb current_slot state.(fundingEnd)) &&
                      negb ((total_supply state) =? state.(tokenCreationCap)))
                      default_error;
    (** Send the currency of the contract back to the fund *)
    let send_act := act_transfer state.(fundDeposit) contract_balance in
    let new_token_state : EIP20Token.State := {|
      EIP20Token.total_supply := (total_supply state) + state.(initSupply);
      EIP20Token.balances := FMap.partial_alter
        (fun balance => Some (with_default 0 balance + state.(initSupply)))
        state.(batFundDeposit) (balances state);
      EIP20Token.allowances := allowances state;
    |} in
    let new_state := state<|isFinalized := true|>
                          <|token_state := new_token_state|> in
      Ok (new_state, [send_act]).

  (** ** Receive *)
  (** This is the main entrypoint function.
      All contract calls will be handled by this function
  *)
  Open Scope Z_scope.
  Definition receive_bat (chain : Chain)
                         (ctx : ContractCallContext)
                         (state : State)
                         (maybe_msg : option Msg)
                         : result (State * list ActionBody) Error :=
    let sender := ctx.(ctx_from) in
    let sender_payload := ctx.(ctx_amount) in
    let slot := chain.(current_slot) in
    let contract_balance := ctx.(ctx_contract_balance) in
    match maybe_msg with
    | Some create_tokens =>
        without_actions (try_create_tokens sender sender_payload slot state)
    | Some refund =>
        not_payable ctx (try_refund sender slot state) default_error
    | Some finalize =>
        not_payable ctx (try_finalize sender slot contract_balance state) default_error
    | _ => Err default_error
    end.
  Close Scope Z_scope.

  (** Composes EIP20Token.receive and receive_bat by first executing
      EIP20Token.receive (if the message is an EIP20 message),
      and otherwise executes receive_bat *)
  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (state : State)
                     (maybe_msg : option Msg)
                     : result (State * list ActionBody) Error :=
    match maybe_msg with
    | Some (tokenMsg msg) =>
        do res <- EIP20Token.receive chain ctx state.(token_state) (Some msg) ;
        let new_state := state<|token_state := fst res|> in
            Ok (new_state, snd res)
    | _ => receive_bat chain ctx state maybe_msg
    end.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End BATAltFix.
