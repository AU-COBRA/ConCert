(* A token-asset exchange contract based on Dexter *)

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
Import ListNotations.
Import RecordSetNotations.
From Coq Require Import Program.Basics.
Notation "f 'o' g" := (compose f g) (at level 50).
Require Import FA2Token FA2Interface.


(* A liquidity exchange contract inspired by the Dexter contract.
   Allows for exchanging tokens to money, and allows the owner to add tokens to the
   reserve held by this contract. *)
Section Dexter.
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

Global Instance exchange_paramserializable : Serializable exchange_param :=
  Derive Serializable exchange_param_rect <build_exchange_param>.

Inductive DexterMsg :=
  | tokens_to_asset : exchange_param -> DexterMsg
  | add_to_tokens_reserve : token_id -> DexterMsg.

Global Instance DexterMsg_serializable : Serializable DexterMsg :=
  Derive Serializable DexterMsg_rect <tokens_to_asset, add_to_tokens_reserve>.

Definition Msg := @FA2ReceiverMsg BaseTypes DexterMsg _.


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

MetaCoq Run (make_setters State).
MetaCoq Run (make_setters Setup).

Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance ClientMsg_serializable : Serializable Msg := FA2Token.FA2ReceiverMsg_serializable.

Global Instance state_serializable : Serializable State :=
  Derive Serializable State_rect <build_state>.

End Serialization.

Definition returnIf (cond : bool) := if cond then None else Some tt.
Definition address_not_eqb a b := negb (address_eqb a b).

Definition begin_exchange_tokens_to_assets (caller : Address)
                                           (params : exchange_param)
                                           (dexter_caddr : Address)
                                           (state : State)
                                           : option (State * (list ActionBody)) :=
  (* do _ <- returnIf (address_not_eqb caller params.(exchange_owner)) ; *)
  (* send out callbacks to check owner token balance, and dexter contract token balance
     to determine if:
     1. owner has sufficient tokens to exchange
     2. exchange rate (based off this contract's token balance)
  *)
  let owner_balance_param := {|
    owner := params.(exchange_owner);
    bal_req_token_id := params.(exchange_token_id);
  |} in
  let dexter_balance_param := {|
    owner := dexter_caddr;
    bal_req_token_id := params.(exchange_token_id);
  |} in
  let act := {|
    bal_requests := [owner_balance_param; dexter_balance_param];
    bal_callback := Build_callback _ None;
  |} in
  let ser_msg := @serialize _ _ (msg_balance_of act) in
  let acts := [act_call state.(fa2_caddr) 0%Z ser_msg] in
  let state := state<| ongoing_exchanges := params :: state.(ongoing_exchanges) |> in
  (* Some (state, []). *)
  Some (state, acts).

(* calculates exchange rate *)
Open Scope Z_scope.
Definition getInputPrice (tokens_to_be_sold : Amount)
                         (tokens_reserve : Amount)
                         (asset_reserve : Amount)
                         :=
  Z.div (tokens_to_be_sold * 997 * asset_reserve) (tokens_reserve * 1000 + tokens_to_be_sold * 997).

Open Scope nat.
(* calculates exchange rate of previously initiated exchange, and returns outgoing transfer actions,
   if the transfer owner has sufficient tokens. *)
Definition receive_balance_response (responses : list balance_of_response)
                                    (dexter_caddr : Address)
                                    (dexter_asset_reserve : Amount)
                                    (state : State)
                                    : option (State * list ActionBody) :=
  do _ <- returnIf (negb (length responses =? 2)) ;
  do trx_owner_balance_response <- nth_error responses 0 ;
  do dexter_balance_response <- nth_error responses 1 ;
  do _ <- returnIf (address_not_eqb dexter_caddr dexter_balance_response.(request).(owner)) ;
  do related_exchange <- last (map Some state.(ongoing_exchanges)) None ;
  (* check if transfer owner has enough tokens to perform the exchange *)
  do _ <- returnIf (N.ltb trx_owner_balance_response.(balance) related_exchange.(tokens_sold)) ;
  let dexter_token_reserve := dexter_balance_response.(balance) in
  let tokens_to_sell := Z.of_N related_exchange.(tokens_sold) in
  let tokens_price := getInputPrice tokens_to_sell (Z.of_N dexter_token_reserve) dexter_asset_reserve in
  (* send out asset transfer to transfer owner, and send a token transfer message to the FA2 token *)
  let asset_transfer_msg := act_transfer related_exchange.(exchange_owner) tokens_price in
  let token_transfer_param := msg_transfer [{|
    from_ := related_exchange.(exchange_owner);
    to_ := dexter_caddr;
    transfer_token_id := related_exchange.(exchange_token_id);
    amount := related_exchange.(tokens_sold);
    sender_callback_addr := Some related_exchange.(callback_addr);
  |}] in
  let token_transfer_msg := act_call state.(fa2_caddr) 0%Z (@serialize FA2Token.Msg _ (token_transfer_param)) in
  (* remove exchange from ongoing exchanges in state *)
  let state := state<| ongoing_exchanges := removelast state.(ongoing_exchanges)|>
                    <| price_history := tokens_price :: state.(price_history)   |> in
  Some (state, [asset_transfer_msg; token_transfer_msg]).

Definition create_tokens (tokenid : token_id)
                         (nr_tokens : Z)
                         (state : State)
                         : option (State * list ActionBody) :=
  let msg := @serialize _ _ (msg_create_tokens tokenid) in
  let create_tokens_act := act_call state.(fa2_caddr) nr_tokens msg in
  Some (state, [create_tokens_act])
.

Open Scope Z_scope.
Definition receive (chain : Chain)
                    (ctx : ContractCallContext)
                   (state : State)
                   (maybe_msg : option Msg)
                   : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let caddr := ctx.(ctx_contract_address) in
  let dexter_balance := ctx.(ctx_contract_balance) in
  let amount := ctx.(ctx_amount) in
  match maybe_msg with
  | Some (receive_balance_of_param responses) => receive_balance_response responses caddr dexter_balance state
  | Some (other_msg (tokens_to_asset params)) => begin_exchange_tokens_to_assets sender params caddr state
  | Some (other_msg (add_to_tokens_reserve tokenid)) => create_tokens tokenid amount state
  | _ => None
  end.

Definition init (chain : Chain)
                (ctx : ContractCallContext)
                (setup : Setup) : option State :=
  Some {| fa2_caddr := setup.(fa2_caddr_);
          ongoing_exchanges := [];
          price_history := [] |}.

Definition contract : Contract Setup Msg State :=
  build_contract init receive.

End Dexter.
