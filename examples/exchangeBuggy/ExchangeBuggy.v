(* A buggy token-asset exchange contract inspired by UniSwap and Dexter *)
From Coq Require Import List.
From Coq Require Import ZArith.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2LegacyInterface.
From ConCert.Utils Require Import RecordUpdate.
Import ListNotations.



(* A liquidity exchange contract inspired by the UniSwap and Dexter contracts.
   Allows for exchanging tokens to money, and allows the owner to add tokens to the
   reserve held by this contract. *)
Section ExchangeBuggyContract.
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Open Scope N_scope.

  Record exchange_param :=
    build_exchange_param {
      exchange_owner : Address;
      exchange_token_id : token_id;
      tokens_sold : N;
      callback_addr : Address;
    }.

  Inductive ExchangeMsg :=
  | tokens_to_asset : exchange_param -> ExchangeMsg
  | add_to_tokens_reserve : token_id -> ExchangeMsg.

  Definition Msg := @FA2ReceiverMsg BaseTypes ExchangeMsg.

  Record State :=
    build_state {
      fa2_caddr : Address;
      ongoing_exchanges : list exchange_param;
      price_history : list Amount;
    }.

  Record Setup :=
    build_setup {
      fa2_caddr_ : Address;
    }.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (* begin hide *)
  MetaCoq Run (make_setters State).
  MetaCoq Run (make_setters Setup).
  (* end hide *)

  Section Serialization.

    Global Instance exchange_paramserializable : Serializable exchange_param :=
      Derive Serializable exchange_param_rect <build_exchange_param>.

    Global Instance ExchangeMsg_serializable : Serializable ExchangeMsg :=
      Derive Serializable ExchangeMsg_rect <tokens_to_asset, add_to_tokens_reserve>.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance ClientMsg_serializable : Serializable Msg := FA2Token.FA2ReceiverMsg_serializable.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.

  Definition begin_exchange_tokens_to_assets (ctx : ContractCallContext)
                                             (params : exchange_param)
                                             (exchange_caddr : Address)
                                             (state : State)
                                             : result (State * (list ActionBody)) Error :=
    (* Send out callbacks to check owner token balance, and exchange contract token balance
      to determine if:
      1. Owner has sufficient tokens to exchange
      2. Exchange rate (based off this contract's token balance)
    *)
    let owner_balance_param := {|
      owner := params.(exchange_owner);
      bal_req_token_id := params.(exchange_token_id);
    |} in
    let exchange_balance_param := {|
      owner := exchange_caddr;
      bal_req_token_id := params.(exchange_token_id);
    |} in
    let act := {|
      bal_requests := [owner_balance_param; exchange_balance_param];
      bal_callback := Build_callback _ None ctx.(ctx_contract_address);
    |} in
    let ser_msg := @serialize _ _ (msg_balance_of act) in
    let acts := [act_call state.(fa2_caddr) 0%Z ser_msg] in
    let state := state<| ongoing_exchanges := params :: state.(ongoing_exchanges) |> in
      Ok (state, acts).

  (* Calculates exchange rate *)
  Open Scope Z_scope.
  Definition getInputPrice (tokens_to_be_sold : Amount)
                           (tokens_reserve : Amount)
                           (asset_reserve : Amount) :=
    Z.div (tokens_to_be_sold * 997 * asset_reserve)
          (tokens_reserve * 1000 + tokens_to_be_sold * 997).

  Open Scope nat.
  (* Calculates exchange rate of previously initiated exchange, and returns outgoing transfer actions,
    if the transfer owner has sufficient tokens. *)
  Definition receive_balance_response (responses : list balance_of_response)
                                      (exchange_caddr : Address)
                                      (exchange_asset_reserve : Amount)
                                      (state : State)
                                      : result (State * list ActionBody) Error :=
    do _ <- throwIf (negb (length responses =? 2)) default_error;
    do trx_owner_balance_response <- result_of_option (nth_error responses 0) default_error;
    do exchange_balance_response <- result_of_option (nth_error responses 1) default_error;
    do _ <- throwIf (address_neqb exchange_caddr exchange_balance_response.(request).(owner)) default_error;
    do related_exchange <- result_of_option (last (map Some state.(ongoing_exchanges)) None) default_error;
    (* Check if transfer owner has enough tokens to perform the exchange *)
    do _ <- throwIf (N.ltb trx_owner_balance_response.(balance) related_exchange.(tokens_sold)) default_error;
    let exchange_token_reserve := exchange_balance_response.(balance) in
    let tokens_to_sell := Z.of_N related_exchange.(tokens_sold) in
    let tokens_price :=
      getInputPrice tokens_to_sell (Z.of_N exchange_token_reserve) exchange_asset_reserve in
    (* Send out asset transfer to transfer owner, and send a token transfer message to the FA2 token *)
    let asset_transfer_msg := act_transfer related_exchange.(exchange_owner) tokens_price in
    let token_transfer_param := msg_transfer [{|
      from_ := related_exchange.(exchange_owner);
      txs := [{|
        to_ := exchange_caddr;
        dst_token_id := related_exchange.(exchange_token_id);
        amount := related_exchange.(tokens_sold);
      |}];
      sender_callback_addr := Some related_exchange.(callback_addr);
    |}] in
    let token_transfer_msg :=
      act_call state.(fa2_caddr) 0%Z (@serialize FA2Token.Msg _ (token_transfer_param)) in
    (* Remove exchange from ongoing exchanges in state *)
    let state := state<| ongoing_exchanges := removelast state.(ongoing_exchanges)|>
                      <| price_history := tokens_price :: state.(price_history) |> in
      Ok (state, [asset_transfer_msg; token_transfer_msg]).

  Definition create_tokens (tokenid : token_id)
                           (nr_tokens : Z)
                           (state : State)
                           : result (State * list ActionBody) Error :=
    let msg := @serialize _ _ (msg_create_tokens tokenid) in
    let create_tokens_act := act_call state.(fa2_caddr) nr_tokens msg in
      Ok (state, [create_tokens_act]).

  Open Scope Z_scope.
  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (state : State)
                     (maybe_msg : option Msg)
                     : result (State * list ActionBody) Error :=
    let caddr := ctx.(ctx_contract_address) in
    let exchange_balance := ctx.(ctx_contract_balance) in
    let amount := ctx.(ctx_amount) in
    match maybe_msg with
    | Some (receive_balance_of_param responses) =>
      receive_balance_response responses caddr exchange_balance state
    | Some (other_msg (tokens_to_asset params)) =>
      begin_exchange_tokens_to_assets ctx params caddr state
    | Some (other_msg (add_to_tokens_reserve tokenid)) =>
      create_tokens tokenid amount state
    | _ => Err default_error
    end.

  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : Setup)
                  : result State Error :=
    Ok {|
      fa2_caddr := setup.(fa2_caddr_);
      ongoing_exchanges := [];
      price_history := []
    |}.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End ExchangeBuggyContract.
