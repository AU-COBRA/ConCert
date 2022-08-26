(* This file defines a simple escrow contract based on the "safe remote
purchase" example in Solidity's docs. This contract allows a seller to sell an
item in a trustless setting assuming economically rational actors. With the
premise that the seller wants to sell an item for 1 ETH, the contract works in
the following way:

1. The seller deploys the contract and commits 2 ETH.
2. The buyer commits 2 ETH before the deadline.
3. The seller hands over the item (outside of the smart contract).
4. The buyer confirms he has received the item. He gets 1 ETH back
while the seller gets 3 ETH back.

If the buyer does not commit the funds, the seller gets his money back after the
deadline. The economic rationality shows up in our assumption that the seller
will confirm he has received the item to get his own funds back. *)

From Coq Require Import Bool.
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.



Section Escrow.
  Context `{Base : ChainBase}.

  Set Nonrecursive Elimination Schemes.

  Record Setup :=
    build_setup {
      setup_buyer : Address;
    }.

  Inductive NextStep :=
  (* Waiting for buyer to commit itemvalue * 2 *)
  | buyer_commit
  (* Waiting for buyer to confirm item received *)
  | buyer_confirm
  (* Waiting for buyer and seller to withdraw their funds. *)
  | withdrawals
  (* No next step, sale is done. *)
  | no_next_step.

  Record State :=
    build_state {
      last_action : nat;
      next_step : NextStep;
      seller : Address;
      buyer : Address;
      seller_withdrawable : Amount;
      buyer_withdrawable : Amount;
    }.

  Definition Error : Type := nat.
  Definition default_error : Error := 0%nat.

  Inductive Msg :=
  | commit_money
  | confirm_item_received
  | withdraw.

  (* begin hide *)
  MetaCoq Run (make_setters State).
  (* end hide *)

  Section Serialization.
    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.

    Global Instance NextStep_serializable : Serializable NextStep :=
      Derive Serializable NextStep_rect<buyer_commit, buyer_confirm, withdrawals, no_next_step>.

    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<commit_money, confirm_item_received, withdraw>.
  End Serialization.

  Open Scope Z.
  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : Setup)
                  : result State Error :=
    let seller := ctx_from ctx in
    let buyer := setup_buyer setup in
    do if (buyer =? seller)%address then Err default_error else Ok tt;
    do if ctx_amount ctx =? 0 then Err default_error else Ok tt;
    do if Z.even (ctx_amount ctx) then Ok tt else Err default_error;
    Ok (build_state (current_slot chain) buyer_commit seller buyer 0 0).

  Definition subAmountOption (n m : Amount) : option Amount :=
    if n <? m then None else Some (n - m).

  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (state : State)
                     (msg : option Msg)
                     : result (State * list ActionBody) Error :=
    match msg, next_step state with
    | Some commit_money, buyer_commit =>
      do diff_ <- result_of_option (subAmountOption (ctx_contract_balance ctx) (ctx_amount ctx)) default_error;
      let item_price := diff_ / 2 in
      let expected := item_price * 2 in
      do if (ctx_from ctx =? buyer state)%address then Ok tt else Err default_error;
      do if ctx_amount ctx =? expected then Ok tt else Err default_error;
      Ok (state<|next_step := buyer_confirm|>
              <|last_action := current_slot chain|>, [])

    | Some confirm_item_received, buyer_confirm =>
      let item_price := ctx_contract_balance ctx / 4 in
      do if (ctx_from ctx =? buyer state)%address then Ok tt else Err default_error;
      do if ctx_amount ctx =? 0 then Ok tt else Err default_error;
      let new_state :=
          state<|next_step := withdrawals|>
              <|buyer_withdrawable := item_price|>
              <|seller_withdrawable := item_price * 3|> in
      Ok (new_state, [])

    | Some withdraw, withdrawals =>
      do if ctx_amount ctx =? 0 then Ok tt else Err default_error;
      let from := ctx_from ctx in
      do '(to_pay, new_state) <-
        match from =? buyer state, from =? seller state with
        | true, _ => Ok (buyer_withdrawable state, state<|buyer_withdrawable := 0|>)
        | _, true => Ok (seller_withdrawable state, state<|seller_withdrawable := 0|>)
        | _, _ => Err default_error
        end%address;
      do if to_pay >? 0 then Ok tt else Err default_error;
      let new_state :=
          if (buyer_withdrawable new_state =? 0) && (seller_withdrawable new_state =? 0)
          then new_state<|next_step := no_next_step|>
          else new_state in
      Ok (new_state, [act_transfer (ctx_from ctx) to_pay])
    | Some withdraw, buyer_commit =>
      do if ctx_amount ctx =? 0 then Ok tt else Err default_error;
      do if (last_action state + 50 <? current_slot chain)%nat then Err default_error else Ok tt;
      do if (ctx_from ctx =? seller state)%address then Ok tt else Err default_error;
      let balance := ctx_contract_balance ctx in
      Ok (state<|next_step := no_next_step|>, [act_transfer (seller state) balance])

    | _, _ => Err default_error
    end.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End Escrow.
