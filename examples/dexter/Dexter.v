(* A token-asset exchange contract based on Dexter
   https://gitlab.com/camlcase-dev/dexter/-/blob/f4ef07ea672a1397b58c2134b3437bb5ef69bcaa/dexter-contracts-ligo/dexter.ligo *)
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Examples.EIP20 Require EIP20Token.

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
      tokens_sold : N;
    }.

  Inductive Msg :=
    | tokens_to_asset : exchange_param -> Msg
    | add_to_tokens_reserve : Msg.

  Record Setup :=
    build_setup {
      token_caddr_ : Address;
      token_pool_ : N;
    }.

  Record State :=
    build_state {
      token_pool : N;
      price_history : list Amount;
      token_caddr : Address;
    }.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  MetaCoq Run (make_setters State).
  MetaCoq Run (make_setters Setup).

  Section Serialization.

    Global Instance exchange_paramserializable : Serializable exchange_param :=
      Derive Serializable exchange_param_rect <build_exchange_param>.

    Global Instance DexterMsg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <tokens_to_asset, add_to_tokens_reserve>.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.

  (* calculates exchange rate *)
  Open Scope Z_scope.
  Definition getInputPrice (tokens_to_be_sold : Amount)
                           (tokens_reserve : Amount)
                           (asset_reserve : Amount) :=
    Z.div (tokens_to_be_sold * 997 * asset_reserve)
          (tokens_reserve * 1000 + tokens_to_be_sold * 997).

  Definition begin_exchange_tokens_to_assets (dexter_asset_reserve : Amount)
                                             (caller : Address)
                                             (params : exchange_param)
                                             (dexter_caddr : Address)
                                             (state : State)
                                             : result (State * (list ActionBody)) Error :=
    do _ <- throwIf (address_neqb caller params.(exchange_owner)) default_error;
    let tokens_to_sell := Z.of_N params.(tokens_sold) in
    let tokens_price := getInputPrice tokens_to_sell (Z.of_N state.(token_pool)) dexter_asset_reserve in
    (* send out asset transfer to transfer owner, and send a token transfer message to the FA2 token *)
    let asset_transfer_msg := act_transfer params.(exchange_owner) tokens_price in
    let token_transfer_param :=
      EIP20Token.transfer_from params.(exchange_owner) dexter_caddr params.(tokens_sold) in
    let token_transfer_msg := act_call state.(token_caddr) 0%Z (@serialize EIP20Token.Msg _ (token_transfer_param)) in
    let new_state := state<|token_pool := N.add state.(token_pool) params.(tokens_sold)|>
                          <| price_history := state.(price_history) ++ [tokens_price]|> in
    Ok (new_state, [asset_transfer_msg; token_transfer_msg]).

  Open Scope Z_scope.
  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (state : State)
                     (maybe_msg : option Msg)
                     : result (State * list ActionBody) Error :=
    let sender := ctx.(ctx_from) in
    let caddr := ctx.(ctx_contract_address) in
    let dexter_balance := ctx.(ctx_contract_balance) in
    match maybe_msg with
    | Some (tokens_to_asset params) =>
        begin_exchange_tokens_to_assets dexter_balance sender params caddr state
    (* Ignore any other type of call to this contract *)
    | _ => Ok (state, [])
    end.

  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : Setup)
                  : result State Error :=
    Ok {|
      token_pool := setup.(token_pool_);
      token_caddr := setup.(token_caddr_);
      price_history := []
    |}.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End Dexter.
