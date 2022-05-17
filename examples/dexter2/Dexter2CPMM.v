(** * Dexter 2 CPMM contract *)
(** This file contains an implementation of the Dexter2 CPMM contract
    https://gitlab.com/dexter2tz/dexter2tz/-/blob/1cec9d9333eba756603d6cd90ea9c70d482a5d3d/dexter.mligo
    In addition this file contains proof of functional correctness w.r.t the
    informal specification https://gitlab.com/dexter2tz/dexter2tz/-/blob/1cec9d9333eba756603d6cd90ea9c70d482a5d3d/docs/informal-spec/dexter2-cpmm.md

    This contract is an implementation of a Constant Product Market Maker (CPMM).
    When paired with a FA1.2 or FA2 token contract and a Dexter2 liquidity contract,
    this contract serves as a decentralized exchange allowing users to trade between
    XTZ and tokens. Additionally users can also add or withdraw funds from the
    exchanges trading reserves. Traders pay a 0.3% fee, the fee goes to the owners
    of the trading reserves, this way user are incentivised to add funds to the reserves.
*)
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2LegacyInterface.
From ConCert.Examples.Dexter2 Require Import Dexter2FA12.
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.



(** * Contract types *)
Section DexterTypes.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

(** ** Type synonyms *)

Definition update_token_pool_internal_ := list FA2LegacyInterface.balance_of_response.
Definition token_id := FA2LegacyInterface.token_id.
Definition token_contract_transfer := FA2LegacyInterface.transfer.
Definition balance_of := FA2LegacyInterface.balance_of_response.
Definition mintOrBurn := Dexter2FA12.mintOrBurn_param.
Definition baker_address := option Address.

(** ** Entrypoint types *)

Record add_liquidity_param :=
  build_add_liquidity_param{
    owner : Address;
    minLqtMinted : N;
    maxTokensDeposited : N;
    add_deadline : nat
}.

Record remove_liquidity_param :=
  build_remove_liquidity_param{
    liquidity_to : Address;
    lqtBurned : N;
    minXtzWithdrawn : N;
    minTokensWithdrawn : N;
    remove_deadline : nat
}.

Record xtz_to_token_param :=
  build_xtz_to_token_param{
    tokens_to : Address;
    minTokensBought : N;
    xtt_deadline : nat
}.

Record token_to_xtz_param :=
  build_token_to_xtz_param{
    xtz_to : Address;
    tokensSold : N;
    minXtzBought : N;
    ttx_deadline : nat
}.

Record token_to_token_param :=
  build_token_to_token_param{
    outputDexterContract : Address;
    to_ : Address;
    minTokensBought_ : N;
    tokensSold_ : N;
    ttt_deadline : nat
}.

Record set_baker_param :=
  build_set_baker_param{
    baker : baker_address;
    freezeBaker_ : bool
}.

Inductive DexterMsg :=
| AddLiquidity : add_liquidity_param -> DexterMsg
| RemoveLiquidity : remove_liquidity_param -> DexterMsg
| XtzToToken : xtz_to_token_param -> DexterMsg
| TokenToXtz : token_to_xtz_param -> DexterMsg
| SetBaker : set_baker_param -> DexterMsg
| SetManager : Address -> DexterMsg
| SetLqtAddress : Address -> DexterMsg
| UpdateTokenPool : DexterMsg
| TokenToToken : token_to_token_param -> DexterMsg.

Definition Msg := @FA2Token.FA2ReceiverMsg _ DexterMsg.


(** ** Storage types *)

Record State :=
  build_state {
    tokenPool : N;
    xtzPool : N;
    lqtTotal : N;
    selfIsUpdatingTokenPool : bool;
    freezeBaker : bool;
    manager : Address;
    tokenAddress : Address;
    tokenId : token_id;
    lqtAddress : Address
  }.

Record Setup :=
  build_setup {
    lqtTotal_ : N;
    manager_ : Address;
    tokenAddress_ : Address;
    tokenId_ : token_id
  }.

(* begin hide *)
MetaCoq Run (make_setters State).
MetaCoq Run (make_setters Setup).
(* end hide *)

End DexterTypes.

Module Type Dexter2Serializable.
  Section DS.
    Context `{ChainBase}.
    Axiom add_liquidity_param_serializable : Serializable add_liquidity_param.
    Existing Instance add_liquidity_param_serializable.

    Axiom remove_liquidity_param_serializable : Serializable remove_liquidity_param.
    Existing Instance remove_liquidity_param_serializable.

    Axiom xtz_to_token_param_serializable : Serializable xtz_to_token_param.
    Existing Instance xtz_to_token_param_serializable.

    Axiom token_to_xtz_param_serializable : Serializable token_to_xtz_param.
    Existing Instance token_to_xtz_param_serializable.

    Axiom set_baker_param_serializable : Serializable set_baker_param.
    Existing Instance set_baker_param_serializable.

    Axiom token_to_token_param_serializable : Serializable token_to_token_param.
    Existing Instance token_to_token_param_serializable.

    Axiom DexterMsg_serializable : Serializable DexterMsg.
    Existing Instance DexterMsg_serializable.

    Axiom Dexter2FA12_Msg_serialize : Serializable Dexter2FA12.Msg.
    Existing Instance Dexter2FA12_Msg_serialize.

    Axiom setup_serializable : Serializable Setup.
    Existing Instance setup_serializable.

    Axiom ClientMsg_serializable : Serializable (@FA2Token.FA2ReceiverMsg _ DexterMsg).
    Existing Instance ClientMsg_serializable.

    Axiom state_serializable : Serializable State.
    Existing Instance state_serializable.

    Axiom FA2Token_Msg_serializable : Serializable FA2Token.Msg.
    Existing Instance FA2Token_Msg_serializable.

  End DS.
End Dexter2Serializable.

Module Type NullAddress.
  Section NullAddress.
    Parameter BaseTypes : ChainBase.
    Existing Instance BaseTypes.

    (** Null address that will newer contain contracts *)
    Parameter null_address : Address.

    (** Place holder for tezos set delegate operation *)
    Parameter set_delegate_call : baker_address -> list ActionBody.
    Axiom delegate_call : forall addr, Forall (fun action => 
      match action with
      | act_transfer _ _ => False
      | act_call _ _ _ => False
      | act_deploy _ _ _ => False
      end) (set_delegate_call addr).
  End NullAddress.
End NullAddress.


(** * Contract functions *)
Module Dexter2 (SI : Dexter2Serializable) (NAddr : NullAddress).

  Import SI.
  Export NAddr.

  Existing Instance add_liquidity_param_serializable.
  Existing Instance remove_liquidity_param_serializable.
  Existing Instance xtz_to_token_param_serializable.
  Existing Instance token_to_xtz_param_serializable.
  Existing Instance set_baker_param_serializable.
  Existing Instance token_to_token_param_serializable.
  Existing Instance DexterMsg_serializable.
  Existing Instance Dexter2FA12_Msg_serialize.
  Existing Instance setup_serializable.
  Existing Instance ClientMsg_serializable.
  Existing Instance state_serializable.
  Existing Instance FA2Token_Msg_serializable.
  Existing Instance BaseTypes.

  Section DexterDefs.
    Open Scope N_scope.

    (** ** Helper functions *)

    (** [Amount] is defined as an alias to [Z]. We use these conversion function to mark
        the places explicitly where the conversion from amounts happens. *)
    Definition amount_to_N : Amount -> N := Z.to_N.
    Definition N_to_amount : N -> Amount := Z.of_N.

    Definition result : Type := option (State * list ActionBody).
    Definition sub (n m : N) : option N := do _ <- throwIf (n <? m) ; Some (n - m).
    Definition div (n m : N) : option N := do _ <- throwIf (m =? 0) ; Some (n / m).
    Definition ceildiv (n m : N) : option N :=
      if N.modulo n m =? 0
      then div n m
      else do result <- div n m ; Some (result + 1).
    Definition ceildiv_ (n m : N) : N :=
      if N.modulo n m =? 0
      then n / m
      else (n / m) + 1.
    Opaque ceildiv.
    Opaque ceildiv_.
    Opaque div.
    Opaque sub.

    Definition non_zero_amount (amt : Z) : bool:= (0 <? amt)%Z.
    Global Arguments non_zero_amount _ /. (* always unfold, if applied *)


    Definition call_liquidity_token (addr : Address) (amt : N) (msg : Dexter2FA12.Msg) :=
      act_call addr (N_to_amount amt) (serialize msg).

    (** Note that [quantity] is allowed to be negative. In this case it correspons to burning *)
    Definition mint_or_burn (state : State) (target : Address) (quantitiy : Z) : option ActionBody :=
        do _ <- throwIf (address_eqb state.(lqtAddress) null_address) ; (* error lqtAddress not set *)
        Some (call_liquidity_token state.(lqtAddress)
                                  0
                                  (Dexter2FA12.msg_mint_or_burn
                                      (Dexter2FA12.build_mintOrBurn_param quantitiy target))).

    Definition call_to_token (token_addr : Address) (amt : N) (msg : FA2Token.Msg) :=
      act_call token_addr (N_to_amount amt) (serialize msg).

    Definition token_transfer (state : State) (from to : Address) (amount : N) : ActionBody :=
      call_to_token state.(tokenAddress)
                    0
                    (FA2Token.msg_transfer
                      [FA2LegacyInterface.build_transfer from [FA2LegacyInterface.build_transfer_destination to state.(tokenId) amount] None]).

    Definition xtz_transfer (to : Address) (amount : N) : option ActionBody :=
      if address_is_contract to
      then None (* error_INVALID_TO_ADDRESS *)
      else Some (act_transfer to (N_to_amount amount)).


    (** ** Add liquidity *)
    Definition add_liquidity (chain : Chain) (ctx : ContractCallContext)
                            (state : State) (param : add_liquidity_param)
                            : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      do _ <- throwIf (param.(add_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
      do lqt_minted <- div ((amount_to_N ctx.(ctx_amount)) * state.(lqtTotal)) state.(xtzPool) ; (* error_DIV_by_0 *)
      do tokens_deposited <- ceildiv ((amount_to_N ctx.(ctx_amount)) * state.(tokenPool)) state.(xtzPool) ; (* error_DIV_by_0 *)
      do _ <- throwIf (param.(maxTokensDeposited) <? tokens_deposited) ; (* error_MAX_TOKENS_DEPOSITED_MUST_BE_GREATER_THAN_OR_EQUAL_TO_TOKENS_DEPOSITED *)
      do _ <- throwIf (lqt_minted <? param.(minLqtMinted)) ; (* error_LQT_MINTED_MUST_BE_GREATER_THAN_MIN_LQT_MINTED *)
      let new_state := state<| lqtTotal := state.(lqtTotal) + lqt_minted |>
                            <| tokenPool := state.(tokenPool) + tokens_deposited |>
                            <| xtzPool := state.(xtzPool) + (amount_to_N ctx.(ctx_amount))|> in
      let op_token := token_transfer state ctx.(ctx_from) ctx.(ctx_contract_address) tokens_deposited in
      do op_lqt <- mint_or_burn state param.(owner) (Z.of_N lqt_minted) ;
      Some (new_state, [op_token; op_lqt]).

    (** ** Remove liquidity *)
    Definition remove_liquidity (chain : Chain) (ctx : ContractCallContext)
                                (state : State) (param : remove_liquidity_param)
                                : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      do _ <- throwIf (param.(remove_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) ; (* error_AMOUNT_MUST_BE_ZERO *)
      do xtz_withdrawn <-  div (param.(lqtBurned) * state.(xtzPool)) state.(lqtTotal) ; (* error_DIV_by_0 *)
      do tokens_withdrawn <- div (param.(lqtBurned) * state.(tokenPool)) state.(lqtTotal) ; (* error_DIV_by_0 *)
      do _ <- throwIf (xtz_withdrawn <? param.(minXtzWithdrawn)) ; (* error_THE_AMOUNT_OF_XTZ_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_WITHDRAWN *)
      do _ <- throwIf (tokens_withdrawn <? param.(minTokensWithdrawn)) ; (* error_THE_AMOUNT_OF_TOKENS_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_WITHDRAWN *)
      do new_lqtPool <- sub state.(lqtTotal) param.(lqtBurned) ; (* error_CANNOT_BURN_MORE_THAN_THE_TOTAL_AMOUNT_OF_LQT *)
      do new_tokenPool <- sub state.(tokenPool) tokens_withdrawn ; (* error_TOKEN_POOL_MINUS_TOKENS_WITHDRAWN_IS_NEGATIVE *)
      do new_xtzPool <- sub state.(xtzPool) xtz_withdrawn ; (* mutez subtraction run time error *)
      do op_lqt <- mint_or_burn state ctx.(ctx_from) (0 - (Z.of_N param.(lqtBurned)))%Z ;
      let op_token := token_transfer state ctx.(ctx_contract_address) param.(liquidity_to) tokens_withdrawn in
      do opt_xtz <- xtz_transfer param.(liquidity_to) xtz_withdrawn ;
      let new_state :=
        {| tokenPool :=  new_tokenPool;
          xtzPool := new_xtzPool;
          lqtTotal := new_lqtPool;
          selfIsUpdatingTokenPool := state.(selfIsUpdatingTokenPool);
          freezeBaker := state.(freezeBaker);
          manager := state.(manager);
          tokenAddress := state.(tokenAddress);
          tokenId := state.(tokenId);
          lqtAddress := state.(lqtAddress) |} in
      Some (new_state, [op_lqt; op_token; opt_xtz]).

    (** ** XTZ to tokens *)
    Definition xtz_to_token (chain : Chain) (ctx : ContractCallContext)
                            (state : State) (param : xtz_to_token_param)
                            : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      do _ <- throwIf (param.(xtt_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
      do tokens_bought <- div
        ((amount_to_N ctx.(ctx_amount)) * 997 * state.(tokenPool))
          (state.(xtzPool) * 1000 + ((amount_to_N ctx.(ctx_amount)) * 997)) ; (* error_DIV_by_0 *)
      do _ <- throwIf (tokens_bought <? param.(minTokensBought)) ; (* error_TOKENS_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_BOUGHT *)
      do new_tokenPool <- sub state.(tokenPool) tokens_bought ; (* error_TOKEN_POOL_MINUS_TOKENS_BOUGHT_IS_NEGATIVE *)
      let new_state := state<| xtzPool := state.(xtzPool) + (amount_to_N ctx.(ctx_amount)) |>
                            <| tokenPool := new_tokenPool |> in
      let op := token_transfer state ctx.(ctx_contract_address) param.(tokens_to) tokens_bought in
      Some (new_state, [op]).

    (** ** Tokes to XTZ *)
    Definition token_to_xtz (chain : Chain) (ctx : ContractCallContext)
                            (state : State) (param : token_to_xtz_param)
                            : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      do _ <- throwIf (param.(ttx_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) ; (* error_AMOUNT_MUST_BE_ZERO *)
      do xtz_bought <- div
        (param.(tokensSold) * 997 * state.(xtzPool))
          (state.(tokenPool) * 1000 + (param.(tokensSold) * 997)) ; (* error_DIV_by_0 *)
      do _ <- throwIf (xtz_bought <? param.(minXtzBought)) ; (* error_XTZ_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_BOUGHT *)
      do new_xtzPool <- sub state.(xtzPool) xtz_bought ; (* mutez subtraction run time error *)
      let op_token := token_transfer state ctx.(ctx_from) ctx.(ctx_contract_address) param.(tokensSold) in
      do op_tez <- xtz_transfer param.(xtz_to) xtz_bought ;
      let new_state := state<| tokenPool := state.(tokenPool) + param.(tokensSold) |>
                            <| xtzPool := new_xtzPool |> in
      Some (new_state, [op_token; op_tez]).

    (** ** Default entrypoint *)
    Definition default_ (chain : Chain) (ctx : ContractCallContext)
                        (state : State) : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      let new_state := state<| xtzPool := state.(xtzPool) + amount_to_N ctx.(ctx_amount) |> in
        Some (new_state, []).

    (** ** Set baker *)
    Definition set_baker (chain : Chain) (ctx : ContractCallContext)
                        (state : State) (param : set_baker_param)
                        : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) ; (* error_AMOUNT_MUST_BE_ZERO *)
      do _ <- throwIf (negb (address_eqb ctx.(ctx_from) state.(manager))) ; (* error_ONLY_MANAGER_CAN_SET_BAKER *)
      do _ <- throwIf (state.(freezeBaker)) ; (* error_BAKER_PERMANENTLY_FROZEN *)
        Some (state<| freezeBaker := param.(freezeBaker_) |>, set_delegate_call param.(baker)).

    (** ** Set manager *)
    Definition set_manager (chain : Chain) (ctx : ContractCallContext)
                          (state : State) (new_manager : Address)
                          : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) ; (* error_AMOUNT_MUST_BE_ZERO *)
      do _ <- throwIf (negb (address_eqb ctx.(ctx_from) state.(manager))) ; (* error_ONLY_MANAGER_CAN_SET_MANAGER *)
        Some (state<| manager := new_manager |>, []).

    (** ** Set liquidity address *)
    Definition set_lqt_address (chain : Chain) (ctx : ContractCallContext)
                              (state : State) (new_lqt_address : Address)
                              : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) ; (* error_AMOUNT_MUST_BE_ZERO *)
      do _ <- throwIf (negb (address_eqb ctx.(ctx_from) state.(manager))) ; (* error_ONLY_MANAGER_CAN_SET_LQT_ADRESS *)
      do _ <- throwIf (negb (address_eqb state.(lqtAddress) null_address)) ; (* error_LQT_ADDRESS_ALREADY_SET *)
        Some (state<| lqtAddress := new_lqt_address |>, []).

    (** ** Update token pool *)
    Definition update_token_pool (chain : Chain) (ctx : ContractCallContext)
                                (state : State) : result :=
      do _ <- throwIf (negb (address_eqb ctx.(ctx_from) ctx.(ctx_origin))) ; (* error_CALL_NOT_FROM_AN_IMPLICIT_ACCOUNT *)
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) ; (* error_AMOUNT_MUST_BE_ZERO *)
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_UNEXPECTED_REENTRANCE_IN_UPDATE_TOKEN_POOL *)
      let balance_of_request :=
        FA2LegacyInterface.Build_balance_of_request ctx.(ctx_contract_address) state.(tokenId) in
      let balance_of_param :=
        FA2LegacyInterface.Build_balance_of_param [balance_of_request] (FA2LegacyInterface.Build_callback _ None ctx.(ctx_contract_address)) in
      let op := call_to_token state.(tokenAddress) 0 (FA2Token.msg_balance_of balance_of_param) in
        Some (state<| selfIsUpdatingTokenPool := true |>, [op]).

    (** ** Update token pool internal *)
    Definition update_token_pool_internal (chain : Chain) (ctx : ContractCallContext)
                                          (state : State) (token_pool : update_token_pool_internal_)
                                          : result :=
      do _ <- throwIf ((negb state.(selfIsUpdatingTokenPool)) ||
                        (negb (address_eqb ctx.(ctx_from) state.(tokenAddress)))) ; (* error_THIS_ENTRYPOINT_MAY_ONLY_BE_CALLED_BY_GETBALANCE_OF_TOKENADDRESS *)
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) ; (* error_AMOUNT_MUST_BE_ZERO *)
      do token_pool <-
        match token_pool with
        | [] => None (* error_INVALID_FA2_BALANCE_RESPONSE *)
        | x :: xs => Some x.(balance)
        end ;
      let new_state := state<| tokenPool := token_pool |><| selfIsUpdatingTokenPool := false |> in
      Some (new_state, []).

    Definition call_to_other_token (token_addr : Address) (amount : N)
              (msg : @FA2Token.FA2ReceiverMsg _ DexterMsg) :=
      act_call token_addr (N_to_amount amount) (serialize msg).

    (** ** Tokens to tokens *)
    Definition token_to_token (chain : Chain) (ctx : ContractCallContext)
                              (state : State) (param : token_to_token_param)
                              : result :=
      do _ <- throwIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) ; (* error_AMOUNT_MUST_BE_ZERO *)
      do _ <- throwIf (param.(ttt_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
      do xtz_bought <- div
        (param.(tokensSold_) * 997 * state.(xtzPool))
          (state.(tokenPool) * 1000 + (param.(tokensSold_) * 997)) ; (* error_DIV_by_0 *)
      do new_xtzPool <- sub state.(xtzPool) xtz_bought ; (* mutez subtraction run time error *)
      let new_state := state<| tokenPool := state.(tokenPool) + param.(tokensSold_) |>
                            <| xtzPool := new_xtzPool |> in
      let op1 := token_transfer state ctx.(ctx_from) ctx.(ctx_contract_address) param.(tokensSold_) in
      let op2 := call_to_other_token
                  param.(outputDexterContract)
                  xtz_bought
                  (FA2Token.other_msg (XtzToToken {|
                                            tokens_to := param.(to_);
                                            minTokensBought := param.(minTokensBought_);
                                            xtt_deadline := param.(ttt_deadline)
                                          |})) in 
      Some (new_state, [op1; op2]).

    (** ** Receive *)
    Definition receive_cpmm (chain : Chain)
                      (ctx : ContractCallContext)
                      (state : State)
                      (maybe_msg : option Msg)
                      : result :=
      match maybe_msg with
      | Some (FA2Token.other_msg (AddLiquidity param)) =>
          add_liquidity chain ctx state param
      | Some (FA2Token.other_msg (RemoveLiquidity param)) =>
          remove_liquidity chain ctx state param
      | Some (FA2Token.other_msg (SetBaker param)) =>
          set_baker chain ctx state param
      | Some (FA2Token.other_msg (SetManager param)) =>
          set_manager chain ctx state param
      | Some (FA2Token.other_msg (SetLqtAddress param)) =>
          set_lqt_address chain ctx state param
      | None =>
          default_ chain ctx state
      | Some (FA2Token.other_msg UpdateTokenPool) =>
          update_token_pool chain ctx state
      | Some (FA2Token.other_msg (XtzToToken param)) =>
          xtz_to_token chain ctx state param
      | Some (FA2Token.other_msg (TokenToXtz param)) =>
          token_to_xtz chain ctx state param
      | Some (FA2Token.other_msg (TokenToToken param)) =>
          token_to_token chain ctx state param
      | Some (FA2Token.receive_balance_of_param responses) =>
          update_token_pool_internal chain ctx state responses
      | _ => None
      end.

    (** ** Init *)
    Definition init_cpmm (chain : Chain)
                    (ctx : ContractCallContext)
                    (setup : Setup) : option State :=
      Some {|
        tokenPool := 0;
        xtzPool := 0;
        lqtTotal := setup.(lqtTotal_);
        selfIsUpdatingTokenPool := false;
        freezeBaker := false;
        manager := setup.(manager_);
        tokenAddress := setup.(tokenAddress_);
        tokenId := setup.(tokenId_);
        lqtAddress := null_address
      |}.

    Definition contract : Contract Setup Msg State :=
      build_contract init_cpmm receive_cpmm.

  End DexterDefs.
End Dexter2.

Module DSInstances <: Dexter2Serializable.
    (* Serialisation instances (omitted).

       NOTE: we use [<:] to make the definitions transparent, so the
       implementation details can be revealed, if needed *)
    (* begin hide *)
    Global Instance add_liquidity_param_serializable `{ChainBase} : Serializable add_liquidity_param :=
      Derive Serializable add_liquidity_param_rect <build_add_liquidity_param>.

    Global Instance remove_liquidity_param_serializable `{ChainBase} : Serializable remove_liquidity_param :=
      Derive Serializable remove_liquidity_param_rect <build_remove_liquidity_param>.

    Global Instance xtz_to_token_param_serializable `{ChainBase} : Serializable xtz_to_token_param :=
      Derive Serializable xtz_to_token_param_rect <build_xtz_to_token_param>.

    Global Instance token_to_xtz_param_serializable `{ChainBase} : Serializable token_to_xtz_param :=
      Derive Serializable token_to_xtz_param_rect <build_token_to_xtz_param>.

    Global Instance set_baker_param_serializable `{ChainBase} : Serializable set_baker_param :=
      Derive Serializable set_baker_param_rect <build_set_baker_param>.

    Global Instance token_to_token_param_serializable `{ChainBase} : Serializable token_to_token_param :=
      Derive Serializable token_to_token_param_rect <build_token_to_token_param>.

    Global Instance DexterMsg_serializable `{ChainBase} : Serializable DexterMsg :=
        Derive Serializable DexterMsg_rect <AddLiquidity,
                                            RemoveLiquidity,
                                            XtzToToken,
                                            TokenToXtz,
                                            SetBaker,
                                            SetManager,
                                            SetLqtAddress,
                                            UpdateTokenPool,
                                            TokenToToken>.

    Global Instance Dexter2FA12_Msg_serialize `{ChainBase} : Serializable Dexter2FA12.Msg :=
      D2LqtSInstances.msg_serializable.

    Global Instance setup_serializable `{ChainBase} : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance ClientMsg_serializable : Serializable (@FA2Token.FA2ReceiverMsg BaseTypes DexterMsg) :=
      fun _ => @FA2Token.FA2ReceiverMsg_serializable _ _ _.

    Global Instance state_serializable `{ChainBase} : Serializable State :=
      Derive Serializable State_rect <build_state>.

    Global Instance FA2Token_Msg_serializable `{ChainBase} : Serializable FA2Token.Msg :=
      FA2Token.msg_serializable.

End DSInstances.
  (* end hide *)

Module NullAddressAxiom <: NullAddress.
  Section NAddr.
    Parameter BaseTypes : ChainBase.
    Existing Instance BaseTypes.

    Parameter null_address : Address.
    Parameter set_delegate_call : baker_address -> list ActionBody.
    Axiom delegate_call : forall addr, Forall (fun action => 
      match action with
      | act_transfer _ _ => False
      | act_call _ _ _ => False
      | act_deploy _ _ _ => False
      end) (set_delegate_call addr).
  End NAddr.
End NullAddressAxiom.

(** Instantiating the implementaion with required instances for serialisation/deserialisation *)
Module DEX2 := Dexter2 DSInstances NullAddressAxiom.
