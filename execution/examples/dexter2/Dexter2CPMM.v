(** * Dexter 2 CPMM contract *)
(** This file contains an implementation of the Dexter2 CPMM contract
    https://gitlab.com/dexter2tz/dexter2tz/-/blob/master/dexter.mligo
    In addition this file contains proof of functional correctness w.r.t the
    informal specification https://gitlab.com/dexter2tz/dexter2tz/-/blob/master/docs/informal-spec/dexter2-cpmm.md

    This contract is an implementation of a Constant Product Market Maker (CPMM).
    When paired with a FA1.2 or FA2 token contract and a Dexter2 liquidity contract,
    this contract serves as a decentralized exchange allowing users to trade between
    XTZ and tokens. Additionally users can also add or withdraw funds from the
    exchanges trading reserves. Traders pay a 0.3% fee, the fee goes to the owners
    of the trading reserves, this way user are incentivised to add funds to the reserves.
*)

From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Extras.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import InterContractCommunication.
From ConCert.Execution.Examples Require Import Common.
From ConCert.Execution.Examples Require Import FA2Token.
From ConCert.Execution.Examples Require Import FA2Interface.
From ConCert.Execution.Examples Require Import Dexter2FA12.
From ConCert.Execution.Examples Require Import SerializableUtil.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
Import ListNotations.


(** * Contract types *)
Section DexterTypes.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

(** ** Type synonyms *)

Definition update_token_pool_internal_ := list FA2Interface.balance_of_response.
Definition token_id := FA2Interface.token_id.
Definition token_contract_transfer := FA2Interface.transfer.
Definition balance_of := FA2Interface.balance_of_response.
Definition mintOrBurn := Dexter2FA12.mintOrBurn_param.

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
    baker : option Address;
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

    Axiom ClientMsg_serializable : Serializable (@FA2Token.FA2ReceiverMsg _ DexterMsg DexterMsg_serializable).
    Existing Instance ClientMsg_serializable.

    Axiom state_serializable : Serializable State.
    Existing Instance state_serializable.

    Axiom FA2Token_Msg_serializable : Serializable FA2Token.Msg.
    Existing Instance FA2Token_Msg_serializable.

  End DS.
End Dexter2Serializable.

(** * Contract functions *)

Module Dexter2 (SI : Dexter2Serializable).

  Import SI.

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

  Section DexterDefs.
    Context `{BaseTypes : ChainBase}.
    Open Scope N_scope.

    (** ** Helper functions *)

    (** [Amount] is defined as an alias to [Z]. We use these conversion function to mark
        the places explicitly where the conversion from amounts happens. *)
    Definition amount_to_N : Amount -> N := Z.to_N.
    Definition N_to_amount : N -> Amount := Z.of_N.

    Definition result : Type := option (State * list ActionBody).
    Definition isNone {A : Type} (a : option A) := match a with | Some _ => false | None => true end.
    Definition isSome {A : Type} (a : option A) := negb (isNone a).
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

    (** Place holder for tezos set delegate operation *)
    Definition set_delegate_call (addr : option Address) : list ActionBody := [].

    Definition non_zero_amount (amt : Z) : bool:= (0 <? amt)%Z.
    Global Arguments non_zero_amount _ /. (* always unfold, if applied *)

    (** Null address that will newer contain contracts *)
    Parameter null_address : Address.

    Definition Msg := @FA2Token.FA2ReceiverMsg BaseTypes DexterMsg _.

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
                     [FA2Interface.build_transfer from to state.(tokenId) amount None]).

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
      FA2Interface.Build_balance_of_request ctx.(ctx_contract_address) state.(tokenId) in
    let balance_of_param :=
      FA2Interface.Build_balance_of_param [balance_of_request] (FA2Interface.Build_callback _ None) in
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
             (msg : @FA2Token.FA2ReceiverMsg _ DexterMsg _) :=
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
  Definition receive (chain : Chain)
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
  Definition init (chain : Chain)
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
    build_contract init receive.

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

    Global Instance ClientMsg_serializable : Serializable (@FA2Token.FA2ReceiverMsg BaseTypes DexterMsg _) :=
      fun _ => @FA2Token.FA2ReceiverMsg_serializable _ _ _.

    Global Instance state_serializable `{ChainBase} : Serializable State :=
      Derive Serializable State_rect <build_state>.

    Global Instance FA2Token_Msg_serializable `{ChainBase} : Serializable FA2Token.Msg :=
      FA2Token.msg_serializable.

End DSInstances.
  (* end hide *)

(** Instantiating the implementaion with required instances for serialisation/deserialisation *)
Module DEX2 := Dexter2 DSInstances.

Import DEX2.

  (** * Properties *)
Section Theories.
  Context {BaseTypes : ChainBase}.
  Open Scope N_scope.
  Global Arguments amount_to_N /.

  (* Tactics and facts about helper functions (omitted) *)
  (* begin hide *)
  Transparent div.
  Transparent ceildiv.
  Transparent ceildiv_.
  Lemma div_eq : forall n m p,
      div n m = Some p ->
      n / m = p /\ m <> 0.
  Proof.
    intros * div_some.
    unfold div in div_some.
    cbn in div_some.
    destruct_match eqn:m_not_zero in div_some;
      try congruence.
    destruct_throw_if m_not_zero.
    now apply N.eqb_neq in m_not_zero.
  Qed.

  Lemma div_zero : forall n m,
    div n m = None ->
    m = 0.
  Proof.
    intros * div_some.
    cbn in div_some.
    destruct_match eqn:m_zero in div_some;
      try congruence.
    destruct_throw_if m_zero.
    now apply N.eqb_eq in m_zero.
  Qed.
  Opaque div.

  Lemma ceildiv_eq : forall n m p,
    ceildiv n m = Some p ->
    ceildiv_ n m = p /\ m <> 0.
  Proof.
    intros * ceildiv_some.
    unfold ceildiv_.
    unfold ceildiv in ceildiv_some.
    destruct_match eqn:modulo_zero.
    - now apply div_eq in ceildiv_some.
    - cbn in ceildiv_some.
      destruct_match eqn:div_some in ceildiv_some;
        try congruence.
      apply div_eq in div_some.
      now inversion_clear ceildiv_some.
  Qed.

  Lemma ceildiv_zero : forall n m,
    ceildiv n m = None ->
    m = 0.
  Proof.
    intros * ceildiv_some.
    unfold ceildiv in ceildiv_some.
    destruct_match eqn:modulo_zero in ceildiv_some.
    - now apply div_zero in ceildiv_some.
    - cbn in ceildiv_some.
      destruct_match eqn:div_some in ceildiv_some;
        try congruence.
      now apply div_zero in div_some.
  Qed.
  Opaque ceildiv.
  Opaque ceildiv_.

  Transparent sub.
  Lemma sub_eq : forall n m p,
    sub n m = Some p ->
    n - m = p /\ m <= n.
  Proof.
    intros * sub_some.
    cbn in sub_some.
    destruct_match eqn:m_le_n in sub_some;
      try congruence.
    destruct_throw_if m_le_n.
    now rewrite <- N.ltb_ge.
  Qed.

  Lemma sub_fail : forall n m,
    sub n m = None ->
    n < m.
  Proof.
    intros * sub_some.
    cbn in sub_some.
    destruct_match eqn:n_lt_m in sub_some;
      try congruence.
    destruct_throw_if n_lt_m.
    now apply N.ltb_lt.
  Qed.
  Opaque sub.

  Lemma isSome_some : forall {A : Type} (x : option A) (y : A),
    x = Some y -> isSome x = true.
  Proof.
    intros.
    now subst.
  Qed.

  Lemma isSome_none : forall {A : Type} (x : option A),
    x = None -> isSome x = false.
  Proof.
    intros.
    now subst.
  Qed.

  Lemma isSome_exists : forall {A : Type} (x : option A),
    isSome x = true <-> exists y : A, x = Some y.
  Proof.
    split.
    - now destruct x eqn:x_eq.
    - intros (y & x_eq).
      now eapply isSome_some.
  Qed.

  Lemma isSome_not_exists : forall {A : Type} (x : option A),
    isSome x = false <-> forall y : A, x <> Some y.
  Proof.
    split.
    - now destruct x eqn:x_eq.
    - intros x_eq.
      eapply isSome_none.
      now destruct x.
  Qed.

  Ltac math_convert_step :=
    match goal with
    | H : sub _ _ = Some _ |- _ => apply sub_eq in H as [<- H]
    | H : sub _ _ = None |- _ => apply sub_fail in H
    | H : div _ _ = Some _ |- _ => apply div_eq in H as [<- H]
    | H : div _ _ = None |- _ => apply div_zero in H
    | H : ceildiv _ _ = Some _ |- _ => apply ceildiv_eq in H as [<- H]
    | H : ceildiv _ _ = None |- _ => apply ceildiv_zero in H
    end.

  Tactic Notation "math_convert" := repeat math_convert_step.

  Ltac receive_simpl_step :=
    match goal with
    | H : Blockchain.receive _ _ _ _ _ = Some (_, _) |- _ =>
        unfold Blockchain.receive in H; cbn in H
    | H : receive _ _ _ _ = Some (_, _) |- _ =>
        unfold receive in H;
        cbn in H
    | |- receive _ _ _ _ = _ =>
        unfold receive; cbn
    | H : Some _ = Some _ |- _ =>
        inversion_clear H
    | H : Some _ = None |- _ =>
        inversion H
    | H : None = Some _ |- _ =>
        inversion H
    | H : throwIf _ = None |- _ => destruct_throw_if H
    | H : throwIf _ = Some ?u |- _ => destruct_throw_if H
    | H : option_map (fun s : State => (s, _)) match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
      let a := fresh "H" in
      destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
    | H : match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
      let a := fresh "H" in
      destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
    | H : option_map (fun s : State => (s, _)) (if ?m then ?a else ?b) = Some _ |- _ =>
      match a with
      | None =>
        let a := fresh "H" in
        destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
      | _ => match b with
             | None =>
               let a := fresh "H" in
               destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
             | _ => idtac
      end end
    | H : (if ?m then ?a else ?b) = Some _ |- _ =>
      match a with
      | None =>
        let a := fresh "H" in
        destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
      | _ => match b with
             | None =>
               let a := fresh "H" in
               destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
             | _ => idtac
      end end
    end.

  Tactic Notation "receive_simpl" := repeat (unfold call_to_token,call_to_other_token;receive_simpl_step).
  (* end hide *)



  (** ** Set baker correct *)
  (** [set_baker] only changes [freezeBaker] in state *)
  Lemma set_baker_state_eq : forall prev_state new_state chain ctx new_acts param,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetBaker param))) = Some (new_state, new_acts) ->
      prev_state<| freezeBaker := param.(freezeBaker_) |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  Lemma set_baker_freeze_baker_correct : forall prev_state new_state chain ctx new_acts param,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetBaker param))) = Some (new_state, new_acts) ->
      new_state.(freezeBaker) = param.(freezeBaker_).
  Proof.
    intros * receive_some.
    apply set_baker_state_eq in receive_some.
    now subst.
  Qed.

  (** [set_baker] produces no new_acts *)
  Lemma set_baker_new_acts_correct : forall chain ctx prev_state param new_state new_acts,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetBaker param))) = Some (new_state, new_acts) ->
      new_acts = set_delegate_call param.(baker).
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  (** If the requirements are met then then receive on set_baker msg must succeed and
      if receive on set_baker msg succeeds then requirements must hold *)
  Lemma set_baker_is_some : forall prev_state chain ctx param,
    (ctx_amount ctx <= 0)%Z /\
    prev_state.(selfIsUpdatingTokenPool) = false /\
    ctx.(ctx_from) = prev_state.(manager) /\
    prev_state.(freezeBaker) = false
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (SetBaker param))) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (amount_zero & not_updating & sender_is_manager & not_frozen).
      do 2 eexists.
      receive_simpl.
      destruct_match eqn:updating_check.
      destruct_match eqn:amount_check.
      destruct_match eqn:sender_check.
      destruct_match eqn:frozen_check.
      + reflexivity.
      + now rewrite not_frozen in frozen_check.
      + now rewrite sender_is_manager, address_eq_refl in sender_check.
      + receive_simpl.
        now apply Z.ltb_ge in amount_zero.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      rewrite Z.ltb_ge in *.
      repeat split; auto.
      now destruct_address_eq.
  Qed.



  (** ** Set manager correct *)
  (** [set_manager] only changes [manager] in state *)
  Lemma set_manager_state_eq : forall prev_state new_state chain ctx new_acts new_manager,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetManager new_manager))) = Some (new_state, new_acts) ->
      prev_state<| manager := new_manager |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  Lemma set_manager_manager_correct : forall prev_state new_state chain ctx new_acts new_manager,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetManager new_manager))) = Some (new_state, new_acts) ->
      new_state.(manager) = new_manager.
  Proof.
    intros * receive_some.
    apply set_manager_state_eq in receive_some.
    now subst.
  Qed.

  (** [set_manager] produces no new_acts *)
  Lemma set_manager_new_acts_correct : forall chain ctx prev_state new_manager new_state new_acts,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetManager new_manager))) = Some (new_state, new_acts) ->
      new_acts = [].
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  (** If the requirements are met then then receive on set_manager msg must succeed and
      if receive on set_manager msg succeeds then requirements must hold *)
  Lemma set_manager_is_some : forall prev_state chain ctx new_manager,
    (ctx_amount ctx <= 0)%Z /\
    prev_state.(selfIsUpdatingTokenPool) = false /\
    ctx.(ctx_from) = prev_state.(manager)
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (SetManager new_manager))) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (amount_zero & not_updating & sender_is_manager).
      do 2 eexists.
      receive_simpl.
      destruct_match eqn:updating_check.
      destruct_match eqn:amount_check.
      destruct_match eqn:sender_check.
      + reflexivity.
      + now rewrite sender_is_manager, address_eq_refl in sender_check.
      + receive_simpl.
        now apply Z.ltb_ge in amount_zero.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      rewrite Z.ltb_ge in *.
      repeat split; auto.
      now destruct_address_eq.
  Qed.



  (** ** Set liquidity address correct *)
  (** [set_lqt_address] only changes [lqtAddress] in state *)
  Lemma set_lqt_address_state_eq : forall prev_state new_state chain ctx new_acts new_lqt_address,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetLqtAddress new_lqt_address))) = Some (new_state, new_acts) ->
      prev_state<| lqtAddress := new_lqt_address |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  Lemma set_lqt_address_correct : forall prev_state new_state chain ctx new_acts new_lqt_address,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetLqtAddress new_lqt_address))) = Some (new_state, new_acts) ->
      new_state.(lqtAddress) = new_lqt_address.
  Proof.
    intros * receive_some.
    apply set_lqt_address_state_eq in receive_some.
    now subst.
  Qed.

  (** [set_lqt_address] produces no new_acts *)
  Lemma set_lqt_address_new_acts_correct : forall chain ctx prev_state new_lqt_address new_state new_acts,
    receive chain ctx prev_state (Some (FA2Token.other_msg (SetLqtAddress new_lqt_address))) = Some (new_state, new_acts) ->
      new_acts = [].
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  (** If the requirements are met then then receive on set_lqt_address msg must succeed and
      if receive on set_lqt_address msg succeeds then requirements must hold *)
  Lemma set_lqt_address_is_some : forall prev_state chain ctx new_lqt_address,
    (ctx_amount ctx <= 0)%Z /\
    prev_state.(selfIsUpdatingTokenPool) = false /\
    ctx.(ctx_from) = prev_state.(manager) /\
    prev_state.(lqtAddress) = null_address
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (SetLqtAddress new_lqt_address))) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (amount_zero & not_updating & sender_is_manager & lqt_address_not_set).
      do 2 eexists.
      receive_simpl.
      destruct_match eqn:updating_check.
      destruct_match eqn:amount_check.
      destruct_match eqn:sender_check.
      destruct_match eqn:lqt_check.
      + reflexivity.
      + now rewrite lqt_address_not_set, address_eq_refl in lqt_check.
      + now rewrite sender_is_manager, address_eq_refl in sender_check.
      + receive_simpl.
        now apply Z.ltb_ge in amount_zero.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      rewrite Z.ltb_ge in *.
      repeat split; auto;
        now destruct_address_eq.
  Qed.



  (** ** Default entrypoint correct *)
  (** [default_] only changes [xtzPool] in state *)
  Lemma default_state_eq : forall prev_state new_state chain ctx new_acts,
    receive chain ctx prev_state None = Some (new_state, new_acts) ->
      prev_state<| xtzPool := prev_state.(xtzPool) + amount_to_N ctx.(ctx_amount) |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  Lemma default_correct : forall prev_state new_state chain ctx new_acts,
    receive chain ctx prev_state None = Some (new_state, new_acts) ->
      new_state.(xtzPool) = prev_state.(xtzPool) + amount_to_N ctx.(ctx_amount).
  Proof.
    intros * receive_some.
    apply default_state_eq in receive_some.
    now subst.
  Qed.

  (** [default_] produces no new_acts *)
  Lemma default_new_acts_correct : forall chain ctx prev_state new_state new_acts,
    receive chain ctx prev_state None = Some (new_state, new_acts) ->
      new_acts = [].
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  (** If the requirements are met then then receive on None msg must succeed and
      if receive on None msg succeeds then requirements must hold *)
  Lemma default_entrypoint_is_some : forall prev_state chain ctx,
    prev_state.(selfIsUpdatingTokenPool) = false
    <->
    exists new_state new_acts, receive chain ctx prev_state None = Some (new_state, new_acts).
  Proof.
    split.
    - intros not_updating.
      do 2 eexists.
      receive_simpl.
      destruct_match eqn:updating_check.
      + reflexivity.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
  Qed.



  (** ** Update token pool correct *)
  (** [update_token_pool] only changes [selfIsUpdatingTokenPool] in state *)
  Lemma update_token_pool_state_eq : forall prev_state new_state chain ctx new_acts,
    receive chain ctx prev_state (Some (FA2Token.other_msg UpdateTokenPool)) = Some (new_state, new_acts) ->
      prev_state<| selfIsUpdatingTokenPool := true |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  Lemma update_token_pool_correct : forall prev_state new_state chain ctx new_acts,
    receive chain ctx prev_state (Some (FA2Token.other_msg UpdateTokenPool)) = Some (new_state, new_acts) ->
      new_state.(selfIsUpdatingTokenPool) = true.
  Proof.
    intros * receive_some.
    apply update_token_pool_state_eq in receive_some.
    now subst.
  Qed.

  (** [update_token_pool] produces an call act with amount = 0, calling
      the token contract with a balance of request *)
  Lemma update_token_pool_new_acts_correct : forall chain ctx prev_state new_state new_acts,
    receive chain ctx prev_state (Some (FA2Token.other_msg UpdateTokenPool)) = Some (new_state, new_acts) ->
      new_acts = [
        act_call prev_state.(tokenAddress) 0%Z (serialize
          (msg_balance_of (Build_balance_of_param 
            ([Build_balance_of_request ctx.(ctx_contract_address) prev_state.(tokenId)])
            (FA2Interface.Build_callback _ None))))
      ].
  Proof.
    intros * receive_some.
    now receive_simpl.
  Qed.

  (** If the requirements are met then then receive on update_token_pool msg must succeed and
      if receive on update_token_pool msg succeeds then requirements must hold *)
  Lemma update_token_pool_is_some : forall prev_state chain ctx,
    (ctx_amount ctx <= 0)%Z /\
    prev_state.(selfIsUpdatingTokenPool) = false /\
    ctx.(ctx_from) = ctx.(ctx_origin)
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg UpdateTokenPool)) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (amount_zero & not_updating & sender_eq_origin).
      do 2 eexists.
      receive_simpl.
      destruct_match eqn:sender_check.
      destruct_match eqn:amount_check.
      destruct_match eqn:updating_check.
      + reflexivity.
      + now rewrite not_updating in updating_check.
      + receive_simpl.
        now apply Z.ltb_ge in amount_zero.
      + now rewrite sender_eq_origin, address_eq_refl in sender_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      rewrite Z.ltb_ge in *.
      rewrite Bool.negb_false_iff in *.
      now destruct_address_eq.
  Qed.

  Tactic Notation "invert_responses_Some" :=
    match goal with
    | [H : match ?rs with
           | [] => _
           | _ => _
           end = Some _ |- _] =>
        match type of rs with
        | list balance_of_response =>
            destruct rs;inversion H;clear H
        | _ => fail "No match on list of balance_of_response"
        end
    end.



  (** ** Update token pool internal correct *)
  (** [update_token_pool_internal] only changes [selfIsUpdatingTokenPool] and [tokenPool] in state *)
  Lemma update_token_pool_internal_state_eq : forall prev_state new_state chain ctx new_acts responses,
    receive chain ctx prev_state (Some (FA2Token.receive_balance_of_param responses)) = Some (new_state, new_acts) ->
      prev_state<| selfIsUpdatingTokenPool := false |>
                <| tokenPool := match responses with
                                | [] => 0
                                | response :: t => response.(balance)
                                end |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
    now invert_responses_Some.
  Qed.

  Lemma update_token_pool_internal_update_correct : forall prev_state new_state chain ctx new_acts responses,
    receive chain ctx prev_state (Some (FA2Token.receive_balance_of_param responses)) = Some (new_state, new_acts) ->
      new_state.(selfIsUpdatingTokenPool) = false.
  Proof.
    intros * receive_some.
    apply update_token_pool_internal_state_eq in receive_some.
    now subst.
  Qed.

  (** [update_token_pool_internal] produces no new actions *)
  Lemma update_token_pool_internal_new_acts_correct : forall chain ctx prev_state new_state new_acts responses,
    receive chain ctx prev_state (Some (FA2Token.receive_balance_of_param responses)) = Some (new_state, new_acts) ->
      new_acts = [].
  Proof.
    intros * receive_some.
    receive_simpl.
  Qed.

  (** If the requirements are met then then receive on update_token_pool_internal msg must succeed and
      if receive on update_token_pool_internal msg succeeds then requirements must hold *)
  Lemma update_token_pool_internal_is_some : forall prev_state chain ctx responses,
    (ctx_amount ctx <= 0)%Z /\
    prev_state.(selfIsUpdatingTokenPool) = true /\
    ctx.(ctx_from) = prev_state.(tokenAddress) /\
    responses <> []
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.receive_balance_of_param responses)) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (amount_zero & updating & sender_is_token_contract & responses_not_empty).
      unfold receive. cbn.
      destruct_match eqn:sender_check.
      destruct_match eqn:amount_check.
      destruct_match eqn:response.
      destruct_match eqn:response_check in response.
      + congruence.
      + eauto.
      + now destruct_match in response.
      + receive_simpl.
        now apply Z.ltb_ge in amount_zero.
      + now rewrite updating, sender_is_token_contract, address_eq_refl in sender_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      rewrite Bool.orb_false_iff in *.
      rewrite Bool.negb_false_iff in *.
      rewrite Z.ltb_ge in *.
      invert_responses_Some;subst.
      repeat split;auto.
      + easy.
      + now destruct_address_eq.
  Qed.



  (** ** Add liquidity correct *)
  (** [add_liquidity] only changes [lqtTotal], [tokenPool] and [xtzPool] in state *)
  Lemma add_liquidity_state_eq : forall prev_state new_state chain ctx new_acts param,
    let lqt_minted := amount_to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) in
    let tokens_deposited := ceildiv_ (amount_to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (AddLiquidity param))) = Some (new_state, new_acts) ->
      prev_state<| lqtTotal := prev_state.(lqtTotal) +  lqt_minted |>
                <| tokenPool := prev_state.(tokenPool) + tokens_deposited |>
                <| xtzPool := prev_state.(xtzPool) + amount_to_N ctx.(ctx_amount) |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
    now math_convert.
  Qed.

  Lemma add_liquidity_correct : forall prev_state new_state chain ctx new_acts param,
    receive chain ctx prev_state (Some (FA2Token.other_msg (AddLiquidity param))) = Some (new_state, new_acts) ->
      new_state.(lqtTotal) = prev_state.(lqtTotal) + amount_to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) /\
      new_state.(tokenPool) = prev_state.(tokenPool) + ceildiv_ (amount_to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) /\
      new_state.(xtzPool) = prev_state.(xtzPool) + amount_to_N ctx.(ctx_amount).
  Proof.
    intros * receive_some.
    apply add_liquidity_state_eq in receive_some.
    now subst.
  Qed.

  (** In the informal specification it is stated that tokens should be trasnfered from owner,
      but in the implementation it is trasnfered from the sender.
      For this we assume that the implementation is correct over the informal specification since
      that is what other formalizations seem to have assumed *)
  Lemma add_liquidity_new_acts_correct : forall chain ctx prev_state new_state new_acts param,
    let lqt_minted := amount_to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) in
    let tokens_deposited := ceildiv_ (amount_to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (AddLiquidity param))) = Some (new_state, new_acts) ->
      new_acts =
      [
        (act_call prev_state.(tokenAddress) 0%Z
          (serialize (FA2Token.msg_transfer
          [build_transfer ctx.(ctx_from) ctx.(ctx_contract_address) prev_state.(tokenId) tokens_deposited None])));
        (act_call prev_state.(lqtAddress) 0%Z
          (serialize (Dexter2FA12.msg_mint_or_burn {| target := param.(owner); quantity := Z.of_N lqt_minted|})))
      ].
  Proof.
    intros * receive_some.
    receive_simpl.
    now math_convert.
  Qed.

  (** If the requirements are met then then receive on add_liquidity msg must succeed and
      if receive on add_liquidity msg succeeds then requirements must hold *)
  Lemma add_liquidity_is_some : forall prev_state chain ctx param,
    let lqt_minted := amount_to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) in
    let tokens_deposited := ceildiv_ (amount_to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) in
    prev_state.(selfIsUpdatingTokenPool) = false /\
    (current_slot chain < param.(add_deadline))%nat /\
    tokens_deposited <= param.(maxTokensDeposited)  /\
    param.(minLqtMinted) <= lqt_minted /\
    prev_state.(xtzPool) <> 0 /\
    prev_state.(lqtAddress) <> null_address
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (AddLiquidity param))) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (not_updating & deadline_not_hit & max_tokens_not_hit &
              enough_minted & xtzPool_not_zero & lqt_addr_set).
      unfold receive.
      cbn in *.
      destruct_match eqn:updating_check.
      destruct_match eqn:deadline_check.
      destruct_match eqn:div_check; math_convert.
      destruct_match eqn:ceildiv_check; math_convert.
      destruct_match eqn:max_tokens_check.
      destruct_match eqn:min_lqt_check.
      destruct_match eqn:mint_act; try congruence;
      destruct_match eqn:lqt_addr_set_check in mint_act; try congruence.
      + eauto.
      + now apply address_eq_ne in lqt_addr_set.
      + now apply N.ltb_ge in enough_minted.
      + now apply N.ltb_ge in max_tokens_not_hit.
      + congruence.
      + congruence.
      + apply leb_correct_conv in deadline_not_hit.
        now rewrite deadline_not_hit in deadline_check.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      math_convert.
      rewrite leb_iff_conv,N.ltb_ge in *.
      repeat split; auto.
      now destruct_address_eq.
  Qed.



  (** ** Remove liquidity correct *)
  (** [remove_liquidity] only changes [lqtTotal], [tokenPool] and [xtzPool] in state *)
  Lemma remove_liquidity_state_eq : forall prev_state new_state chain ctx new_acts param,
    let xtz_withdrawn := (param.(lqtBurned) * prev_state.(xtzPool)) / prev_state.(lqtTotal) in
    let tokens_withdrawn := (param.(lqtBurned) * prev_state.(tokenPool)) / prev_state.(lqtTotal) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (RemoveLiquidity param))) = Some (new_state, new_acts) ->
      prev_state<| lqtTotal := prev_state.(lqtTotal) - param.(lqtBurned) |>
                <| tokenPool := prev_state.(tokenPool) - tokens_withdrawn |>
                <| xtzPool := prev_state.(xtzPool) - xtz_withdrawn |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
    now math_convert;cbv.
  Qed.

  Lemma remove_liquidity_correct : forall prev_state new_state chain ctx new_acts param,
    receive chain ctx prev_state (Some (FA2Token.other_msg (RemoveLiquidity param))) = Some (new_state, new_acts) ->
      new_state.(lqtTotal) = prev_state.(lqtTotal) - param.(lqtBurned) /\
      new_state.(tokenPool) = prev_state.(tokenPool) -  (param.(lqtBurned) * prev_state.(tokenPool)) / prev_state.(lqtTotal) /\
      new_state.(xtzPool) = prev_state.(xtzPool) - (param.(lqtBurned) * prev_state.(xtzPool)) / prev_state.(lqtTotal).
  Proof.
    intros * receive_some.
    apply remove_liquidity_state_eq in receive_some.
    now subst.
  Qed.

  (** [remove_liquidity] should produce three acts
  - A call action to LQT contract burning [lqtBurned] from [sender]
  - A call action to token contract transferring [tokens_withdrawn] from this contract to [liquidity_to]
  - A transfer action transferring [xtz_withdrawn] from this contract to [liquidity_to]
   *)
  Lemma remove_liquidity_new_acts_correct : forall chain ctx prev_state new_state new_acts param,
    let xtz_withdrawn := (param.(lqtBurned) * prev_state.(xtzPool)) / prev_state.(lqtTotal) in
    let tokens_withdrawn := (param.(lqtBurned) * prev_state.(tokenPool)) / prev_state.(lqtTotal) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (RemoveLiquidity param))) = Some (new_state, new_acts) ->
      new_acts =
      [
        (act_call prev_state.(lqtAddress) 0%Z
          (serialize (Dexter2FA12.msg_mint_or_burn {| target := ctx.(ctx_from); quantity := - Z.of_N param.(lqtBurned)|})));
        (act_call prev_state.(tokenAddress) 0%Z
          (serialize (FA2Token.msg_transfer
          [build_transfer ctx.(ctx_contract_address) param.(liquidity_to) prev_state.(tokenId) tokens_withdrawn None])));
        (act_transfer param.(liquidity_to) (N_to_amount xtz_withdrawn))
      ].
  Proof.
    intros * receive_some.
    receive_simpl.
    math_convert.
    unfold xtz_transfer in *.
    destruct_match in *; try congruence.
    match goal with
      [ H : Some _ = Some _ |- _ ] => now inversion H
    end.
  Qed.

  (** If the requirements are met then then receive on remove_liquidity msg must succeed and
      if receive on remove_liquidity msg succeeds then requirements must hold *)
  Lemma remove_liquidity_is_some : forall prev_state chain ctx param,
    let xtz_withdrawn := (param.(lqtBurned) * prev_state.(xtzPool)) / prev_state.(lqtTotal) in
    let tokens_withdrawn := (param.(lqtBurned) * prev_state.(tokenPool)) / prev_state.(lqtTotal) in
    prev_state.(selfIsUpdatingTokenPool) = false /\
    (current_slot chain < param.(remove_deadline))%nat /\
    (ctx.(ctx_amount) <= 0)%Z /\
    prev_state.(lqtTotal) <> 0 /\
    param.(minXtzWithdrawn) <= xtz_withdrawn /\
    param.(minTokensWithdrawn) <= tokens_withdrawn /\
    tokens_withdrawn <= prev_state.(tokenPool) /\
    xtz_withdrawn <= prev_state.(xtzPool) /\
    param.(lqtBurned) <= prev_state.(lqtTotal) /\
    address_is_contract param.(liquidity_to) = false /\
    prev_state.(lqtAddress) <> null_address
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (RemoveLiquidity param))) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (not_updating & deadline_not_hit & ctx_amount_zero &
              lqtPool_not_zero & enough_xtz_withdrawn & enough_tokens_withdrawn &
              tokens_withdrawn_le_total & xtz_withdrawn_le_total & lqt_burned_le_total &
              to_not_contract & lqt_addr_set).
      unfold receive.
      cbn in *.
      destruct_match eqn:updating_check.
      destruct_match eqn:deadline_check.
      destruct_match eqn:ctx_amount_check.
      destruct_match eqn:xtz_div_check; math_convert; try easy.
      destruct_match eqn:tokens_div_check; math_convert; try easy.
      destruct_match eqn:min_xtz_check.
      destruct_match eqn:min_tokens_check.
      destruct_match eqn:burned_check; math_convert; try easy.
      destruct_match eqn:token_pool_check; math_convert; try easy.
      destruct_match eqn:xtz_pool_check; math_convert; try easy.
      destruct_match eqn:mint_act; try congruence;
      destruct_match eqn:lqt_addr_set_check in mint_act; try congruence.
      destruct_match eqn:transfer_act.
      + eauto.
      + unfold xtz_transfer in transfer_act.
        now rewrite to_not_contract in transfer_act.
      + now apply address_eq_ne in lqt_addr_set.
      + now apply N.ltb_ge in enough_tokens_withdrawn.
      + now apply N.ltb_ge in enough_xtz_withdrawn.
      + now apply Z.ltb_ge in ctx_amount_zero.
      + apply leb_correct_conv in deadline_not_hit.
        now rewrite deadline_not_hit in deadline_check.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      math_convert.
      rewrite leb_iff_conv,N.ltb_ge,Z.ltb_ge in *.
      unfold xtz_transfer in *.
      destruct_match in *; try congruence.
      repeat split; auto.
      now destruct_address_eq.
  Qed.


  (** ** XTZ to token correct *)
  (** [xtz_to_token] only changes [tokenPool] and [xtzPool] in state *)
  Lemma xtz_to_token_state_eq : forall prev_state new_state chain ctx new_acts param,
    let tokens_bought := ((amount_to_N ctx.(ctx_amount)) * 997 * prev_state.(tokenPool)) /
                            (prev_state.(xtzPool) * 1000 + ((amount_to_N ctx.(ctx_amount)) * 997)) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (XtzToToken param))) = Some (new_state, new_acts) ->
      prev_state<| tokenPool := prev_state.(tokenPool) - tokens_bought |>
                <| xtzPool := prev_state.(xtzPool) + amount_to_N ctx.(ctx_amount) |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
    now math_convert.
  Qed.

  Lemma xtz_to_token_correct : forall prev_state new_state chain ctx new_acts param,
    receive chain ctx prev_state (Some (FA2Token.other_msg (XtzToToken param))) = Some (new_state, new_acts) ->
      new_state.(tokenPool) = prev_state.(tokenPool) -  (((amount_to_N ctx.(ctx_amount)) * 997 * prev_state.(tokenPool)) /
                            (prev_state.(xtzPool) * 1000 + ((amount_to_N ctx.(ctx_amount)) * 997)) ) /\
      new_state.(xtzPool) = prev_state.(xtzPool) + amount_to_N ctx.(ctx_amount).
  Proof.
    intros * receive_some.
    apply xtz_to_token_state_eq in receive_some.
    now subst.
  Qed.

  (** [xtz_to_token] should produce one action
  - A call action to token contract transferring [tokens_bought] from this contract to [tokens_to]
  *)
  Lemma xtz_to_token_new_acts_correct : forall chain ctx prev_state new_state new_acts param,
    let tokens_bought := ((amount_to_N ctx.(ctx_amount)) * 997 * prev_state.(tokenPool)) /
                            (prev_state.(xtzPool) * 1000 + ((amount_to_N ctx.(ctx_amount)) * 997)) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (XtzToToken param))) = Some (new_state, new_acts) ->
      new_acts =
      [
        (act_call prev_state.(tokenAddress) 0%Z
          (serialize (FA2Token.msg_transfer
          [build_transfer ctx.(ctx_contract_address) param.(tokens_to) prev_state.(tokenId) tokens_bought None])))
      ].
  Proof.
    intros * receive_some.
    receive_simpl.
    now math_convert.
  Qed.

  (** If the requirements are met then then receive on xtz_to_token msg must succeed and
      if receive on xtz_to_token msg succeeds then requirements must hold *)
  Lemma xtz_to_token_is_some : forall prev_state chain ctx param,
    let tokens_bought := ((amount_to_N ctx.(ctx_amount)) * 997 * prev_state.(tokenPool)) /
                            (prev_state.(xtzPool) * 1000 + ((amount_to_N ctx.(ctx_amount)) * 997)) in
    prev_state.(selfIsUpdatingTokenPool) = false /\
    (current_slot chain < param.(xtt_deadline))%nat /\
    (prev_state.(xtzPool) <> 0 \/ (0 < ctx.(ctx_amount))%Z) /\
    param.(minTokensBought) <= tokens_bought /\
    tokens_bought <= prev_state.(tokenPool)
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (XtzToToken param))) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (not_updating & deadline_not_hit & not_zero &
              enough_tokens_bought & tokens_bought_le_total).
      unfold receive.
      cbn in *.
      destruct_match eqn:updating_check.
      destruct_match eqn:deadline_check.
      destruct_match eqn:xtz_div_check; math_convert; try easy.
      destruct_match eqn:min_tokens_check.
      destruct_match eqn:token_pool_check; math_convert; try easy.
      + now apply N.ltb_ge in enough_tokens_bought.
      + apply leb_correct_conv in deadline_not_hit.
        now rewrite deadline_not_hit in deadline_check.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      math_convert.
      rewrite leb_iff_conv,N.ltb_ge in *.
      now repeat split.
  Qed.


  (** ** Token to xtz correct *)
  (** [token_to_xtz] only changes [tokenPool] and [xtzPool] in state *)
  Lemma token_to_xtz_state_eq : forall prev_state new_state chain ctx new_acts param,
    let xtz_bought := (param.(tokensSold) * 997 * prev_state.(xtzPool)) /
                            (prev_state.(tokenPool) * 1000 + (param.(tokensSold) * 997)) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (TokenToXtz param))) = Some (new_state, new_acts) ->
      prev_state<| tokenPool := prev_state.(tokenPool) + param.(tokensSold) |>
                <| xtzPool := prev_state.(xtzPool) - xtz_bought |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
    now math_convert.
  Qed.

  Lemma token_to_xtz_correct : forall prev_state new_state chain ctx new_acts param,
    receive chain ctx prev_state (Some (FA2Token.other_msg (TokenToXtz param))) = Some (new_state, new_acts) ->
      new_state.(tokenPool) = prev_state.(tokenPool) + param.(tokensSold) /\
      new_state.(xtzPool) = prev_state.(xtzPool) - ((param.(tokensSold) * 997 * prev_state.(xtzPool)) /
                            (prev_state.(tokenPool) * 1000 + (param.(tokensSold) * 997))).
  Proof.
    intros * receive_some.
    apply token_to_xtz_state_eq in receive_some.
    now subst.
  Qed.

  (** token_to_xtz should produce two actions
  - A call action to token contract transferring [tokens_sold] from [sender] to this contract
  - A transfer action transferring [xtz_bought] from this contract to [xtz_to]
   *)
  Lemma token_to_xtz_new_acts_correct : forall chain ctx prev_state new_state new_acts param,
    let xtz_bought := (param.(tokensSold) * 997 * prev_state.(xtzPool)) /
                            (prev_state.(tokenPool) * 1000 + (param.(tokensSold) * 997)) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (TokenToXtz param))) = Some (new_state, new_acts) ->
      new_acts =
      [
        (act_call prev_state.(tokenAddress) 0%Z
          (serialize (FA2Token.msg_transfer
          [build_transfer ctx.(ctx_from) ctx.(ctx_contract_address) prev_state.(tokenId) param.(tokensSold) None])));
        (act_transfer param.(xtz_to) (N_to_amount xtz_bought))
      ].
  Proof.
    intros * receive_some.
    receive_simpl.
    math_convert.
    unfold xtz_transfer in *. 
    destruct_match in *; try congruence.
    match goal with
      [H : Some _ = Some _ |- _] => now inversion H
    end.
  Qed.

  (** If the requirements are met then then receive on token_to_xtz msg must succeed and
      if receive on token_to_xtz msg succeeds then requirements must hold *)
  Lemma token_to_xtz_is_some : forall prev_state chain ctx param,
    let xtz_bought := (param.(tokensSold) * 997 * prev_state.(xtzPool)) /
                            (prev_state.(tokenPool) * 1000 + (param.(tokensSold) * 997)) in
    prev_state.(selfIsUpdatingTokenPool) = false /\
    (current_slot chain < param.(ttx_deadline))%nat /\
    (ctx.(ctx_amount) <= 0)%Z /\
    param.(minXtzBought) <= xtz_bought /\
    (prev_state.(tokenPool) <> 0 \/ param.(tokensSold) <> 0) /\
    address_is_contract param.(xtz_to) = false /\
    xtz_bought <= prev_state.(xtzPool)
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (TokenToXtz param))) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (not_updating & deadline_not_hit & ctx_amount_zero &
              enough_xtz_bought & not_zero & to_not_contract &
              xtz_bought_le_total).
      unfold receive.
      cbn.
      destruct_match eqn:updating_check.
      destruct_match eqn:deadline_check.
      destruct_match eqn:amount_check.
      destruct_match eqn:div_check; math_convert; try easy.
      destruct_match eqn:min_xtz_check.
      destruct_match eqn:xtz_pool_check; math_convert; try easy.
      destruct_match eqn:transfer_act.
      + eauto.
      + unfold xtz_transfer in transfer_act.
        now rewrite to_not_contract in transfer_act.
      + now apply N.ltb_ge in enough_xtz_bought.
      + now apply Z.ltb_ge in ctx_amount_zero.
      + apply leb_correct_conv in deadline_not_hit.
        now rewrite deadline_not_hit in deadline_check.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      math_convert.
      rewrite leb_iff_conv,N.ltb_ge,Z.ltb_ge in *.
      unfold xtz_transfer in *.
      destruct_match in *;
        try congruence.
      now repeat split.
  Qed.



  (** ** Token to token correct *)
  (** [token_to_token] only changes [tokenPool] and [xtzPool] in state *)
  Lemma token_to_token_state_eq : forall prev_state new_state chain ctx new_acts param,
    let xtz_bought := (param.(tokensSold_) * 997 * prev_state.(xtzPool)) /
                            (prev_state.(tokenPool) * 1000 + (param.(tokensSold_) * 997)) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (TokenToToken param))) = Some (new_state, new_acts) ->
      prev_state<| tokenPool := prev_state.(tokenPool) + param.(tokensSold_) |>
                <| xtzPool := prev_state.(xtzPool) - xtz_bought |> = new_state.
  Proof.
    intros * receive_some.
    receive_simpl.
    now math_convert.
  Qed.

  Lemma token_to_token_correct : forall prev_state new_state chain ctx new_acts param,
    receive chain ctx prev_state (Some (FA2Token.other_msg (TokenToToken param))) = Some (new_state, new_acts) ->
      new_state.(tokenPool) = prev_state.(tokenPool) + param.(tokensSold_) /\
      new_state.(xtzPool) = prev_state.(xtzPool) - ((param.(tokensSold_) * 997 * prev_state.(xtzPool)) /
                            (prev_state.(tokenPool) * 1000 + (param.(tokensSold_) * 997))).
  Proof.
    intros * receive_some.
    apply token_to_token_state_eq in receive_some.
    now subst.
  Qed.

  (** token_to_token should produce two actions
  - A call action to token contract transferring [tokens_sold] from [sender] to this contract
  - A call action to [outputDexterContract] [xtz_to_token] entrypoint with [xtz_bought] amount attached
   *)
  Lemma token_to_token_new_acts_correct : forall chain ctx prev_state new_state new_acts param,
    let xtz_bought := (param.(tokensSold_) * 997 * prev_state.(xtzPool)) /
                            (prev_state.(tokenPool) * 1000 + (param.(tokensSold_) * 997)) in
    receive chain ctx prev_state (Some (FA2Token.other_msg (TokenToToken param))) = Some (new_state, new_acts) ->
      new_acts =
      [
        (act_call prev_state.(tokenAddress) 0%Z
          (serialize (FA2Token.msg_transfer
          [build_transfer ctx.(ctx_from) ctx.(ctx_contract_address) prev_state.(tokenId) param.(tokensSold_) None])));
        (act_call param.(outputDexterContract) (N_to_amount xtz_bought)
          (serialize ((FA2Token.other_msg (XtzToToken
          {| tokens_to := param.(to_);
             minTokensBought := param.(minTokensBought_);
             xtt_deadline := param.(ttt_deadline) |})))))
      ].
  Proof.
    intros * receive_some.
    receive_simpl.
    now math_convert.
  Qed.

  (** If the requirements are met then then receive on token_to_token msg must succeed and
      if receive on token_to_token msg succeeds then requirements must hold *)
  Lemma token_to_token_is_some : forall prev_state chain ctx param,
    let xtz_bought := (param.(tokensSold_) * 997 * prev_state.(xtzPool)) /
                            (prev_state.(tokenPool) * 1000 + (param.(tokensSold_) * 997)) in
    prev_state.(selfIsUpdatingTokenPool) = false /\
    (current_slot chain < param.(ttt_deadline))%nat /\
    (ctx.(ctx_amount) <= 0)%Z /\
    xtz_bought <= prev_state.(xtzPool) /\
    (prev_state.(tokenPool) <> 0 \/ param.(tokensSold_) <> 0)
    <->
    exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (TokenToToken param))) = Some (new_state, new_acts).
  Proof.
    split.
    - intros (not_updating & deadline_not_hit & ctx_amount_zero &
              xtz_bought_le_total & not_zero).
      unfold receive.
      cbn.
      destruct_match eqn:updating_check.
      destruct_match eqn:amount_check.
      destruct_match eqn:deadline_check.
      destruct_match eqn:div_check; math_convert; try easy.
      destruct_match eqn:xtz_pool_check; math_convert; try easy.
      + apply leb_correct_conv in deadline_not_hit.
        now rewrite deadline_not_hit in deadline_check.
      + now apply Z.ltb_ge in ctx_amount_zero.
      + now rewrite not_updating in updating_check.
    - intros (new_state & new_acts & receive_some).
      receive_simpl.
      math_convert.
      rewrite leb_iff_conv,Z.ltb_ge in *.
      now repeat split.
  Qed.



  (** ** Init correct *)
  Lemma init_state_eq : forall chain ctx setup state,
    init chain ctx setup = Some state ->
      state = {|
        tokenPool := 0;
        xtzPool := 0;
        lqtTotal := setup.(lqtTotal_);
        selfIsUpdatingTokenPool := false;
        freezeBaker := false;
        manager := setup.(manager_);
        tokenAddress := setup.(tokenAddress_);
        lqtAddress := null_address;
        tokenId := setup.(tokenId_)
      |}.
  Proof.
    intros * init_some.
    now inversion init_some.
  Qed.

  Lemma init_correct : forall chain ctx setup state,
    init chain ctx setup = Some state ->
      tokenPool state = 0 /\
      xtzPool state = 0 /\
      lqtTotal state = setup.(lqtTotal_) /\
      selfIsUpdatingTokenPool state = false /\
      freezeBaker state = false /\
      manager state = setup.(manager_) /\
      tokenAddress state = setup.(tokenAddress_) /\
      lqtAddress state = null_address /\
      tokenId state = setup.(tokenId_).
  Proof.
    intros * init_some.
    apply init_state_eq in init_some.
    now subst.
  Qed.

  (** Initialization should always succeed *)
  Lemma init_is_some : forall chain ctx setup,
    exists state, init chain ctx setup = state.
  Proof.
    intros.
    eauto.
  Qed.



  (* begin hide *)
  Ltac split_hypotheses :=
    match goal with
    | [ H : _ /\ _ |- _ ] => destruct H as []
    end.

  Ltac rewrite_acts_correct :=
    match goal with
    | [ H : receive _ _ _ _ = Some _ |- _ ] =>
      first [apply set_baker_new_acts_correct in H as new_acts_eq
            |apply set_manager_new_acts_correct in H as new_acts_eq
            |apply set_lqt_address_new_acts_correct in H as new_acts_eq
            |apply default_new_acts_correct in H as new_acts_eq
            |apply update_token_pool_new_acts_correct in H as new_acts_eq
            |apply update_token_pool_internal_new_acts_correct in H as new_acts_eq
            |apply add_liquidity_new_acts_correct in H as new_acts_eq
            |apply remove_liquidity_new_acts_correct in H as new_acts_eq
            |apply xtz_to_token_new_acts_correct in H as new_acts_eq
            |apply token_to_xtz_new_acts_correct in H as new_acts_eq
            |apply token_to_token_new_acts_correct in H as new_acts_eq ];
      subst
    end.

  Ltac rewrite_state_eq :=
    match goal with
    | [ H : receive _ _ _ _ = Some _ |- _ ] =>
      first [apply set_baker_state_eq in H as new_acts_eq
            |apply set_manager_state_eq in H as new_acts_eq
            |apply set_lqt_address_state_eq in H as new_acts_eq
            |apply default_state_eq in H as new_acts_eq
            |apply update_token_pool_state_eq in H as new_acts_eq
            |apply update_token_pool_internal_state_eq in H as new_acts_eq
            |apply add_liquidity_state_eq in H as new_acts_eq
            |apply remove_liquidity_state_eq in H as new_acts_eq
            |apply xtz_to_token_state_eq in H as new_acts_eq
            |apply token_to_xtz_state_eq in H as new_acts_eq
            |apply token_to_token_state_eq in H as new_acts_eq ];
      subst
    end.

  Ltac rewrite_receive_is_some :=
    match goal with
    | [ H : receive _ _ _ _ = Some _ |- _ ] =>
      first [specialize set_baker_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize set_manager_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize set_lqt_address_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize default_entrypoint_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize update_token_pool_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize update_token_pool_internal_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize add_liquidity_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize remove_liquidity_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize xtz_to_token_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize token_to_xtz_is_some as (_ & []); [now (do 2 eexists; apply H) |]
            |specialize token_to_token_is_some as (_ & []); [now (do 2 eexists; apply H) |] ];
      repeat split_hypotheses; subst
    end.
  (* end hide *)



  (** ** Outgoing acts facts *)
  (** If contract emits self calls then they are for the XtzToToken entrypoint or default entrypoint *)
  Lemma self_calls' bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      (tokenAddress cstate <> caddr ->
      Forall (fun act_body =>
        match act_body with
        | act_transfer to _ => True
        | act_call to _ msg => to = caddr ->
            (exists p, msg = serialize (FA2Token.other_msg (XtzToToken p))) \/
            (exists p, msg = serialize (msg_mint_or_burn p))
        | _ => False
        end) (outgoing_acts bstate caddr)).
  Proof.
    contract_induction; intros; cbn in *; auto.
    - now apply list.Forall_cons in IH as [_ IH].
    - destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        rewrite_acts_correct;
        rewrite_state_eq;
        try (apply Forall_app; split);
        try apply IH; auto;
        rewrite ?list.Forall_cons, ?list.Forall_nil;
        try easy.
    - destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        rewrite_acts_correct;
        rewrite_state_eq;
        try (apply Forall_app; split);
        apply list.Forall_cons in IH as [? IH];
        try apply IH; auto;
        rewrite ?list.Forall_cons, ?list.Forall_nil;
        try easy.
    - now rewrite <- perm.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      instantiate (CallFacts := fun _ _ _ _ => True).
      unset_all; subst;cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
  Qed.

  Local Open Scope Z_scope.
  Lemma call_amount_zero bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
      Forall (fun act_body =>
        match act_body with
        | act_transfer _ amount => True
        | act_call _ amount msg => amount = 0 \/ exists p, msg = serialize (FA2Token.other_msg (XtzToToken p))
        | act_deploy amount _ _ => amount = 0
        end) (outgoing_acts bstate caddr).
  Proof.
    intros.
    apply (lift_outgoing_acts_prop contract); auto.
    intros * receive_some.
    cbn in receive_some.
      destruct msg.
      + destruct m; try destruct d;
          try (now receive_simpl);
          rewrite_acts_correct;
          rewrite ?list.Forall_cons, list.Forall_nil;
          intuition.
          now right.
      + now receive_simpl.
  Qed.

  Lemma no_contract_deployment bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
      Forall (fun act_body =>
        match act_body with
        | act_deploy amount _ _ => False
        | _ => True
        end) (outgoing_acts bstate caddr).
  Proof.
    intros.
    apply (lift_outgoing_acts_prop contract); auto.
    intros * receive_some.
    cbn in receive_some.
    destruct msg; try destruct m; try destruct d;
      try (now receive_simpl);
      rewrite_acts_correct; auto.
    now cbv.
  Qed.



  (** ** Contract balance facts *)
  Lemma contract_balance_correct' : forall bstate caddr (trace : ChainTrace empty_state bstate),
    let effective_balance := (env_account_balances bstate caddr - (sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr)))%Z in
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate deploy_info,
      contract_state bstate caddr = Some cstate /\
      deployment_info Setup trace caddr = Some deploy_info /\
       (deploy_info.(deployment_amount) = 0%Z -> Z.of_N (xtzPool cstate) = effective_balance).
  Proof.
    intros.
    subst effective_balance.
    contract_induction; intros; auto.
    - cbn in *.
      apply init_correct in init_some as (_ & ? & _).
      lia.
    - cbn in IH.
      lia.
    - instantiate (CallFacts := fun _ ctx _ _ =>
        (0 <= ctx_amount ctx)%Z).
      unfold CallFacts in facts.
      cbn in receive_some.
      destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        try rewrite_acts_correct;
        try rewrite_state_eq;
        try rewrite_receive_is_some;
        unfold N_to_amount in *;
        try match goal with
        | H : (?x <= ?y)%Z, G : (?y <= ?x)%Z |- _ => apply Z.le_antisymm in H; auto; rewrite H in *
        end;
        cbn;
        try lia.
    - unfold CallFacts in facts.
      cbn in receive_some.
      destruct head;
        auto;
        cbn in IH;
        destruct action_facts as (? & ? & ?);
        subst;
      try destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        try rewrite_acts_correct;
        try rewrite_state_eq;
        try rewrite_receive_is_some;
        unfold N_to_amount in *;
        try match goal with
        | H : (?x <= ?y)%Z, G : (?y <= ?x)%Z |- _ => apply Z.le_antisymm in H; auto; rewrite H in *
        end;
        cbn;
        try lia.
    - now erewrite sumZ_permutation in IH by eauto.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      unset_all; subst.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      intros.
      subst. cbn.
      now apply Z.ge_le.
  Qed.

  Definition no_transfers (queue : list ActionBody) :=
    Forall (fun act_body =>
      match act_body with
      | act_transfer to _ => False
      | act_call to _ msg => forall p, msg <> serialize (FA2Token.other_msg (XtzToToken p))
      | _ => True
      end) queue.

  Lemma contract_balance_correct : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate deploy_info,
      contract_state bstate caddr = Some cstate /\
      deployment_info Setup trace caddr = Some deploy_info /\
       (deploy_info.(deployment_amount) = 0%Z ->
        no_transfers (outgoing_acts bstate caddr) ->
          Z.of_N (xtzPool cstate) = env_account_balances bstate caddr).
  Proof.
    intros * deployed.
    eapply contract_balance_correct' in deployed as balance_correct.
    destruct balance_correct as (cstate & deploy_info & deployed_state & ? & balance_correct).
    eapply call_amount_zero in deployed as amount_zero; try now constructor.
    do 2 eexists.
    intuition.
    rewrite balance_correct by auto.
    clear balance_correct.
    rename H1 into no_transfer.
    unfold no_transfers in no_transfer.
    assert (sum_zero : sumZ (fun act : ActionBody => act_body_amount act) (outgoing_acts bstate caddr) = 0%Z).
    - induction outgoing_acts; auto.
      apply list.Forall_cons in no_transfer as (no_transfer & no_transfers).
      apply list.Forall_cons in amount_zero as (amount_zero & amounts_zero).
      destruct a; auto; cbn; rewrite IHl by auto;
        clear IHl no_transfers amounts_zero.
      + now destruct amount_zero as [-> | []].
      + now subst.
    - lia.
  Qed.

  Lemma xtz_pool_bound : forall bstate caddr (trace : ChainTrace empty_state bstate),
    let effective_balance := (env_account_balances bstate caddr - (sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr)))%Z in
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
       Z.of_N (xtzPool cstate) <= effective_balance.
  Proof.
    intros.
    subst effective_balance.
    contract_induction; intros; auto.
    - instantiate (DeployFacts := fun _ ctx =>
        (0 <= ctx_amount ctx)%Z).
      unfold DeployFacts in facts.
      cbn in *.
      apply init_correct in init_some as (_ & -> & _).
      lia.
    - cbn in IH.
      lia.
    - instantiate (CallFacts := fun _ ctx _ _ =>
        (0 <= ctx_amount ctx)%Z).
      unfold CallFacts in facts.
      cbn in receive_some.
      destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        try rewrite_acts_correct;
        try rewrite_state_eq;
        try rewrite_receive_is_some;
        unfold N_to_amount in *;
        try match goal with
        | H : (?x <= ?y)%Z, G : (?y <= ?x)%Z |- _ => apply Z.le_antisymm in H; auto; rewrite H in *
        end;
        cbn;
        try lia.
    - unfold CallFacts in facts.
      cbn in receive_some.
      destruct head;
        auto;
        cbn in IH;
        destruct action_facts as (? & ? & ?);
        subst;
      try destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        try rewrite_acts_correct;
        try rewrite_state_eq;
        try rewrite_receive_is_some;
        unfold N_to_amount in *;
        try match goal with
        | H : (?x <= ?y)%Z, G : (?y <= ?x)%Z |- _ => apply Z.le_antisymm in H; auto; rewrite H in *
        end;
        cbn;
        try lia.
    - now erewrite sumZ_permutation in IH by eauto.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      unset_all; subst.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      + cbn.
        lia.
      + intros.
        subst. cbn.
        now apply Z.ge_le.
  Qed.

  Lemma transfer_bound bstate caddr :
    let transfered_balance := sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr) in
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate : State,
      contract_state bstate caddr = Some cstate /\
      transfered_balance <= env_account_balances bstate caddr.
  Proof.
    intros.
    subst transfered_balance.
    contract_induction; intros; cbn in *; auto.
    - instantiate (DeployFacts := fun _ ctx =>
        (0 <= ctx_amount ctx)%Z).
      auto.
    - lia.
    - instantiate (CallFacts := fun _ ctx state out_acts =>
        (0 <= ctx_amount ctx)%Z /\
        Z.of_N (xtzPool state) <= ctx_contract_balance ctx- sumZ (fun act => act_body_amount act) out_acts).
      destruct facts.
      destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        rewrite_acts_correct;
        try rewrite_receive_is_some;
        unfold N_to_amount in *;
        try match goal with
        | H : (?x <= ?y)%Z, G : (?y <= ?x)%Z |- _ => apply Z.le_antisymm in H; auto; rewrite H in *
        end;
        cbn;
        try lia.
    - destruct facts.
      destruct head;
        auto;
        cbn in IH;
        destruct action_facts as (? & ? & ?);
        subst.
      + receive_simpl.
        cbn in *.
        lia.
      + try destruct msg; try destruct m; try destruct d;
          try (now receive_simpl);
          rewrite_acts_correct;
          try rewrite_receive_is_some;
          unfold N_to_amount in *;
          try match goal with
          | H : (?x <= ?y)%Z, G : (?y <= ?x)%Z |- _ => apply Z.le_antisymm in H; auto; rewrite H in *
          end;
          cbn in *;
          try lia.
    - now rewrite <- perm.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      unset_all; subst.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      + cbn.
        lia.
      + intros ? ? deployed_state_.
        subst. cbn.
        split.
        * now apply Z.ge_le.
        * apply (account_balance_nonnegative _ to_addr) in from_reachable as ?H.
          destruct from_reachable.
          specialize xtz_pool_bound as (? & deployed_state' & ?); eauto.
          cbn in *.
          rewrite deployed_state in deployed_state'.
          rewrite deployed_state in deployed_state_.
          rewrite deployed_state_ in deployed_state'.
          inversion deployed_state'.
          subst.
          destruct_address_eq; try easy; lia.
  Qed.



  (** ** Total supply correct *)
  Definition mintedOrBurnedTokens_acts (act_body : ActionBody) : Z :=
    match act_body with
    | act_call _ _ msg_serialized =>
      match @deserialize Dexter2FA12.Msg D2LqtSInstances.msg_serializable msg_serialized with
      | Some msg => mintedOrBurnedTokens (Some msg)
      | _ => 0
      end
    | _ => 0
    end.

  Definition mintedOrBurnedTokens_tx (tx : Tx) : Z :=
    match tx.(tx_body) with
    | tx_call (Some msg_serialized) =>
      match @deserialize Dexter2FA12.Msg D2LqtSInstances.msg_serializable msg_serialized with
      | Some msg => mintedOrBurnedTokens (Some msg)
      | _ => 0
      end
    | _ => 0
    end.

  Lemma deserialize_balance_of_ne_mint_or_burn : forall n m,
    @deserialize Dexter2FA12.Msg D2LqtSInstances.msg_serializable (serialize (FA2Token.msg_balance_of n)) <>
    Some (Dexter2FA12.msg_mint_or_burn m).
  Proof.
    intros.
    Transparent serialize deserialize.
    cbn.
    rewrite !Nat2Z.id.
    destruct (Z.of_nat 3 <? 0); auto.
    cbn.
    destruct_match; try discriminate.
    destruct p.
    now destruct_match.
    Opaque serialize deserialize.
  Qed.

  Lemma forall_filter_cons : forall P (Q : Action -> ActionBody) R x l,
    Forall P (map Q (filter R (x :: l))) -> Forall P (map Q (filter R l)).
  Proof.
    intros * forall_l. cbn in forall_l.
    destruct_match in forall_l; auto.
    now eapply Forall_inv_tail.
  Qed.

  Lemma outgoing_acts_no_mint_before_set_lqt_addr : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        (cstate.(lqtAddress) = null_address ->
          Forall (fun act_body =>
            match act_body with
            | act_call _ _ msg =>
              match @deserialize Dexter2FA12.Msg D2LqtSInstances.msg_serializable msg with
              | Some (msg_mint_or_burn _) => False
              | _ => True
              end
            | _ => True
            end) (outgoing_acts bstate caddr)).
  Proof.
    intros * trace deployed.
    trace_induction; cbn in *.
    - (* Step block *)
      destruct IH as (state & deployed_state & IH).
      rewrite outgoing_acts_after_block_nil; eauto.
      eapply contract_addr_format; eauto.
      now constructor.
    - (* Action transfer *)
      destruct IH as (state & deployed_state & sum_eq).
      eexists.
      split; eauto.
      intros lqtAddr.
      subst.
      apply sum_eq in lqtAddr.
      clear sum_eq.
      unfold outgoing_acts in *.
      rewrite queue_prev, queue_new in *.
      now apply forall_filter_cons in lqtAddr.
    - (* Action deploy *)
      destruct (address_eqb_spec caddr to_addr) as [<-|].
      + (* Deploy this contract *)
        inversion deployed.
        subst. clear deployed IH.
        apply wc_init_strong in init_some as (setup' & state' & _ & deployed_state' & init_some).
        subst.
        rewrite deserialize_serialize.
        eexists.
        split; eauto.
        intros lqtAddr.
        rewrite outgoing_acts_after_deploy_nil; auto.
        rewrite queue_new.
        apply undeployed_contract_no_out_queue in not_deployed; auto.
        * rewrite queue_prev in not_deployed.
          now apply list.Forall_cons in not_deployed.
        * now constructor.
      + (* Deploy other contract *)
        destruct IH as (state' & deployed_state' & sum_eq); auto.
        eexists.
        split; eauto.
        subst.
        intros lqtAddr.
        apply sum_eq in lqtAddr.
        clear sum_eq.
        unfold outgoing_acts in *.
        rewrite queue_prev, queue_new in *.
        now apply forall_filter_cons in lqtAddr.
    - (* Action call *)
      destruct IH as (state & deployed_state' & sum_eq).
      destruct (address_eqb_spec caddr to_addr) as [<-|].
      + (* Call this contract *)
        rewrite deployed in deployed0.
        inversion deployed0.
        subst. clear deployed0.
        apply wc_receive_strong in receive_some as
          (prev_state' & msg' & new_state' & serialize_prev_state & _ & serialize_new_state & receive_some).
        cbn in receive_some.
        rewrite <- serialize_new_state, deserialize_serialize.
        rewrite deployed_state, serialize_prev_state in deployed_state'.
        inversion deployed_state'. subst.
        clear deployed_state' serialize_prev_state.
        eexists.
        split; eauto.
        intros lqtAddr.
        destruct msg'; try destruct m; try destruct d;
          try (now receive_simpl);
          rewrite_acts_correct;
          rewrite_state_eq;
          try (apply sum_eq in lqtAddr as lqtAddr'; clear sum_eq);
          unfold outgoing_acts in *;
          rewrite queue_prev, queue_new in *;
          try apply forall_filter_cons in lqtAddr';
          auto;
          cbn;
          rewrite ?address_eq_refl;
          cbn;
          rewrite ?list.Forall_cons;
          repeat split; try easy;
          rewrite_receive_is_some;
          try easy.
        * subst.
          now eapply forall_filter_cons.
        * destruct_match eqn:match_deser; auto.
          destruct m; auto.
          now apply deserialize_balance_of_ne_mint_or_burn in match_deser.
      + (* Call other contract *)
        eexists.
        split; eauto.
        intros lqtAddr.
        apply sum_eq in lqtAddr.
        clear sum_eq.
        unfold outgoing_acts in *.
        rewrite queue_prev, queue_new in *.
        apply forall_filter_cons in lqtAddr.
        subst.
        rewrite filter_app, map_app, <- Forall_app.
        split; auto.
        rewrite Extras.filter_map.
        cbn.
        rewrite address_eq_ne, filter_false by auto.
        now cbn.
    - (* Invalid action *)
      destruct IH as (state & deployed_state & sum_eq).
      eexists.
      split; eauto.
      intros lqtAddr.
      unfold outgoing_acts in *.
      rewrite queue_prev, <- queue_new in *.
      apply sum_eq in lqtAddr.
      clear sum_eq.
      now apply forall_filter_cons in lqtAddr.
    - (* Permutation *)
      destruct IH as (state & deployed_state & sum_eq).
      eexists.
      split; eauto.
      intros lqtAddr.
      apply sum_eq in lqtAddr.
      clear sum_eq.
      eapply Permutation_filter in perm.
      eapply Permutation.Permutation_map in perm.
      eapply forall_respects_permutation; eauto.
Qed.

  Lemma outgoing_acts_all_mint_same_dest : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        Forall (fun act_body =>
          match act_body with
          | act_call to _ msg_serialized =>
            match @deserialize Dexter2FA12.Msg D2LqtSInstances.msg_serializable msg_serialized with
            | Some (msg_mint_or_burn _) => to = lqtAddress cstate
            | _ => True
            end
          | _ => True
          end
        ) (outgoing_acts bstate caddr).
  Proof.
    contract_induction;
      intros; auto.
    - cbn.
      now apply list.Forall_cons in IH as [].
    - instantiate (CallFacts := fun _ _ state out_acts =>
        state.(lqtAddress) = null_address ->
          Forall (fun act_body =>
            match act_body with
            | act_call _ _ msg =>
              match @deserialize Dexter2FA12.Msg D2LqtSInstances.msg_serializable msg with
              | Some (msg_mint_or_burn _) => False
              | _ => True
              end
            | _ => True
            end) out_acts).
      unfold CallFacts in facts.
      cbn in receive_some.
      destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        rewrite_acts_correct;
        rewrite_state_eq;
        apply Forall_app;
        split; auto;
        rewrite ?list.Forall_cons, ?list.Forall_nil;
        try easy.
      + cbn.
        repeat split; auto.
        now rewrite deserialize_serialize.
      + cbn.
        repeat split; auto.
        now rewrite deserialize_serialize.
      + rewrite_receive_is_some.
        apply facts in H2.
        apply All_Forall.In_Forall.
        intros act act_in.
        eapply Forall_forall in H2; eauto.
        destruct act; auto.
        destruct_match; auto.
        destruct m; auto.
      + cbn.
        destruct_match eqn:contradiction; auto.
        destruct m; auto.
        now apply deserialize_balance_of_ne_mint_or_burn in contradiction.
    - apply list.Forall_cons in IH as [].
      unfold CallFacts in facts.
      cbn in receive_some.
      destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        rewrite_acts_correct;
        rewrite_state_eq;
        apply Forall_app;
        split; auto;
        rewrite ?list.Forall_cons, ?list.Forall_nil;
        try easy.
      + cbn.
        repeat split; auto.
        now rewrite deserialize_serialize.
      + cbn.
        repeat split; auto.
        now rewrite deserialize_serialize.
      + rewrite_receive_is_some.
        apply facts, Forall_inv_tail in H4.
        apply All_Forall.In_Forall.
        intros act act_in.
        eapply Forall_forall in H4; eauto.
        destruct act; auto.
        destruct_match; auto.
        destruct m; auto.
      + cbn.
        destruct_match eqn:contradiction; auto.
        destruct m; auto.
        now apply deserialize_balance_of_ne_mint_or_burn in contradiction.
    - now rewrite <- perm.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      unset_all; subst.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      intros state' deployed' deployed_state'. cbn.
      rewrite deployed in deployed'.
      inversion deployed'.
      subst.
      destruct from_reachable as [trace].
      clear deployed'.
      specialize outgoing_acts_no_mint_before_set_lqt_addr as (state & state_deployed & ?); eauto.
      rewrite deployed_state' in state_deployed.
      now inversion state_deployed.
  Qed.

  Lemma outgoing_acts_sum_filter_eq : forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        sumZ mintedOrBurnedTokens_acts (filter (actTo cstate.(lqtAddress)) (outgoing_acts bstate caddr)) =
        sumZ mintedOrBurnedTokens_acts (outgoing_acts bstate caddr).
  Proof. 
    intros * [trace] deployed.
    apply outgoing_acts_all_mint_same_dest in deployed as mint_or_burn_to_lqt_addr; auto.
    destruct mint_or_burn_to_lqt_addr as (cstate & deployed_state & mint_or_burn_to_lqt_addr).
    exists cstate.
    split; auto.
    clear trace deployed deployed_state.
    induction outgoing_acts.
    - reflexivity.
    - apply list.Forall_cons in mint_or_burn_to_lqt_addr as [mint_or_burn_to_lqt_addr IH%IHl].
      clear IHl.
      cbn.
      rewrite <- IH. clear IH.
      destruct a eqn:H; cbn; destruct_address_eq; auto.
      destruct_match; auto.
      now destruct_match.
  Qed.

  Lemma outgoing_txs_no_mint_before_set_lqt_addr : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        (cstate.(lqtAddress) = null_address ->
          Forall (fun tx =>
            match tx.(tx_body) with
            | tx_call (Some msg) =>
              match @deserialize Dexter2FA12.Msg D2LqtSInstances.msg_serializable msg with
              | Some (msg_mint_or_burn _) => False
              | _ => True
              end
            | _ => True
            end) (outgoing_txs trace caddr)).
  Proof.
    intros * deployed.
    remember empty_state.
    induction trace.
    - now subst.
    - subst.
      apply deployed_contract_state_typed in deployed as deployed_state.
      + destruct deployed_state as (state & deployed_state).
        exists state.
        split; auto.
        assert (reach : reachable to) by (constructor; now econstructor).
        destruct_chain_step.
        * (* Step block *)
          intros.
          destruct IHtrace as (state' & deployed_state' & sum_eq);
              try rewrite_environment_equiv; auto.
          cbn in *.
          rewrite deployed_state in deployed_state'.
          inversion deployed_state'.
          now subst.
        * destruct_action_eval.
         -- (* Action transfer *)
            destruct IHtrace as (state' & deployed_state' & sum_eq);
              try rewrite_environment_equiv; auto.
            cbn in *.
            rewrite deployed_state in deployed_state'.
            inversion deployed_state'.
            intros lqtAddr.
            subst.
            destruct_address_eq; auto.
            apply sum_eq in lqtAddr.
            apply Forall_cons; auto.
            now inversion lqtAddr.
         -- (* Action deploy *)
            rewrite_environment_equiv.
            cbn in *.
            intros lqtAddr.
            destruct (address_eqb_spec caddr to_addr) as [<-|]; auto.
          --- (* Deploy contract *)
              specialize undeployed_contract_no_out_txs as H; auto.
              unfold outgoing_txs in H.
              destruct_address_eq;
                try apply Forall_cons; cbn; auto;
                rewrite H; auto.
          --- (* Deploy other contract *)
              destruct IHtrace as (state' & deployed_state' & sum_eq); auto.
              rewrite deployed_state in deployed_state'.
              inversion deployed_state'.
              subst.
              destruct_address_eq; auto.
              apply sum_eq in lqtAddr.
              apply Forall_cons; auto.
              now inversion lqtAddr.
         -- (* Action call *)
            destruct IHtrace as (state' & deployed_state' & sum_eq);
              try rewrite_environment_equiv; auto.
            cbn in *.
            intros lqtAddr.
            destruct (address_eqb_spec caddr to_addr) as [<-|]; auto.
          --- (* Call contract *)
              rewrite deployed in deployed0.
              inversion deployed0.
              subst.
              apply wc_receive_strong in receive_some as
                (prev_state' & msg' & new_state' & serialize_prev_state & msg_ser & serialize_new_state & receive_some).
              cbn in receive_some.
              rewrite <- serialize_new_state, deserialize_serialize in deployed_state.
              inversion deployed_state.
              rewrite deployed_state0, serialize_prev_state in deployed_state'.
              inversion deployed_state'.
              subst.
              clear deployed0 deployed_state deployed_state'.
              assert (lqt_addr_preserved : lqtAddress state' = lqtAddress state \/ exists a, msg' = Some (FA2Token.other_msg (SetLqtAddress a))).
              { destruct msg'; try destruct m; try destruct d;
                  try (now receive_simpl);
                  rewrite_state_eq.
              }
              destruct (address_eqb_spec caddr from_addr) as [<-|]; auto.
          ---- (* Self call *)
                rewrite address_eq_refl.
                edestruct outgoing_acts_no_mint_before_set_lqt_addr as (cstate & deployed_state' & out_acts_forall); eauto.
                cbn in deployed_state'.
                rewrite deployed_state0, serialize_prev_state in deployed_state'.
                inversion deployed_state'.
                subst. clear deployed_state'.
                unfold outgoing_acts in out_acts_forall.
                rewrite queue_prev in out_acts_forall.
                cbn in out_acts_forall.
                rewrite address_eq_refl in out_acts_forall.
                cbn in out_acts_forall.
                apply Forall_cons. cbn.
                { destruct lqt_addr_preserved as [lqt_addr_preserved | lqt_addr_preserved]; auto.
                  - rewrite <- lqt_addr_preserved in lqtAddr.
                    apply Forall_inv in out_acts_forall; auto.
                    destruct msg; auto.
                  - destruct lqt_addr_preserved as [? lqt_addr_preserved].
                    rewrite lqt_addr_preserved in receive_some.
                    rewrite_receive_is_some.
                    apply Forall_inv in out_acts_forall; auto.
                    destruct msg; auto.
                }
                destruct lqt_addr_preserved as [lqt_addr_preserved | lqt_addr_preserved];
                  try now rewrite <- lqt_addr_preserved in lqtAddr.
                destruct lqt_addr_preserved as [? lqt_addr_preserved].
                rewrite lqt_addr_preserved in receive_some.
                now rewrite_receive_is_some.
          ---- (* Call by other contract *)
              rewrite address_eq_ne by auto.
              destruct lqt_addr_preserved as [lqt_addr_preserved | lqt_addr_preserved];
                try now rewrite <- lqt_addr_preserved in lqtAddr.
              destruct lqt_addr_preserved as [? lqt_addr_preserved].
              rewrite lqt_addr_preserved in receive_some.
              now rewrite_receive_is_some.
          --- (* Call other contract *)
              rewrite deployed_state in deployed_state'.
              inversion deployed_state'.
              subst. clear deployed_state'.
              destruct_address_eq; auto.
              subst.
              apply Forall_cons; auto.
              edestruct outgoing_acts_no_mint_before_set_lqt_addr as (cstate & deployed_state' & out_acts_forall); eauto.
              cbn in deployed_state'.
              rewrite deployed_state in deployed_state'.
              inversion deployed_state'.
              subst. clear deployed_state'.
              unfold outgoing_acts in out_acts_forall.
              rewrite queue_prev in out_acts_forall.
              cbn in out_acts_forall.
              rewrite address_eq_refl in out_acts_forall.
              cbn in out_acts_forall.
              apply Forall_inv in out_acts_forall; auto.
              destruct msg; auto.
        * (* Invalid action *)
          intros lqtAddr.
          destruct IHtrace as (state' & deployed_state' & sum_eq);
            try rewrite_environment_equiv; auto.
          cbn in *.
          rewrite deployed_state in deployed_state'.
          inversion deployed_state'.
          now subst.
        * (* Permutation *)
          intros lqtAddr.
          destruct IHtrace as (state' & deployed_state' & sum_eq);
            rewrite env_eq in *; auto.
          cbn in *.
          rewrite deployed_state in deployed_state'.
          inversion deployed_state'.
          now subst.
    + constructor.
      now econstructor.
  Qed.

  Lemma outgoing_txs_all_mint_same_dest : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        Forall (fun tx =>
          match tx.(tx_body) with
          | tx_call (Some msg) =>
            match @deserialize Dexter2FA12.Msg D2LqtSInstances.msg_serializable msg with
            | Some (msg_mint_or_burn _) => tx.(tx_to) = lqtAddress cstate
            | _ => True
            end
          | _ => True
          end
        ) (outgoing_txs trace caddr).
  Proof.
    intros * deployed.
    remember empty_state.
    induction trace.
    - now subst.
    - subst.
      apply deployed_contract_state_typed in deployed as deployed_state.
      + destruct deployed_state as (state & deployed_state).
        exists state.
        split; auto.
        destruct_chain_step.
        * (* Step block *)
          rewrite_environment_equiv.
          destruct IHtrace as (state' & deployed_state' & sum_eq); auto.
          cbn in *.
          rewrite deployed_state in deployed_state'.
          now inversion deployed_state'.
        * destruct_action_eval.
         -- (* Action transfer *)
            destruct IHtrace as (state' & deployed_state' & sum_eq);
              try rewrite_environment_equiv; auto.
            cbn in *.
            rewrite deployed_state in deployed_state'.
            inversion deployed_state'.
            clear deployed_state'.
            subst.
            destruct_address_eq; auto.
            apply list.Forall_cons.
            now split.
         -- (* Action deploy *)
            rewrite_environment_equiv.
            cbn in *.
            destruct (address_eqb_spec caddr to_addr) as [<-|]; auto.
          --- (* Deploy contract *)
              eapply undeployed_contract_no_out_txs in not_deployed; auto.
              unfold outgoing_txs in not_deployed.
              rewrite not_deployed.
              destruct_address_eq; auto.
              now apply list.Forall_cons.
          --- (* Deploy other contract *)
              destruct IHtrace as (state' & deployed_state' & sum_eq); auto.
              rewrite deployed_state in deployed_state'.
              inversion deployed_state'.
              clear deployed_state'.
              subst.
              destruct_address_eq; auto.
              now apply list.Forall_cons.
         -- (* Action call *)
            destruct IHtrace as (state' & deployed_state' & sum_eq);
              try rewrite_environment_equiv; auto.
            cbn in *.
            destruct (address_eqb_spec caddr to_addr) as [<-|]; auto.
          --- (* Call contract *)
              rewrite deployed in deployed0.
              inversion deployed0.
              (*rewrite deployed_state0 in deployed_state'.*)
              subst.
              apply wc_receive_strong in receive_some as
                (prev_state' & msg' & new_state' & serialize_prev_state & msg_ser & serialize_new_state & receive_some).
              cbn in receive_some.
              rewrite <- serialize_new_state, deserialize_serialize in deployed_state.
              inversion deployed_state.
              rewrite deployed_state0, serialize_prev_state in deployed_state'.
              inversion deployed_state'.
              subst.
              clear deployed0 deployed_state deployed_state'.
              assert (lqt_addr_preserved : lqtAddress state' = lqtAddress state \/ exists a, msg' = Some (FA2Token.other_msg (SetLqtAddress a))).
              { destruct msg'; try destruct m; try destruct d;
                  try (now receive_simpl);
                  rewrite_state_eq.
              }
              destruct (address_eqb_spec caddr from_addr) as [<-|]; auto.
          ---- (* Self call *)
                rewrite address_eq_refl.
                apply Forall_cons. cbn.
                { destruct lqt_addr_preserved as [<- | lqt_addr_preserved]; auto.
                  - edestruct outgoing_acts_all_mint_same_dest as (cstate & deployed_state' & out_acts_forall); eauto.
                    cbn in deployed_state'.
                    rewrite deployed_state0, serialize_prev_state in deployed_state'.
                    inversion deployed_state'.
                    subst. clear deployed_state'.
                    unfold outgoing_acts in out_acts_forall.
                    rewrite queue_prev in out_acts_forall.
                    cbn in out_acts_forall.
                    rewrite address_eq_refl in out_acts_forall.
                    cbn in out_acts_forall.
                    apply Forall_inv in out_acts_forall.
                    now destruct msg.
                  - edestruct outgoing_acts_no_mint_before_set_lqt_addr as (cstate & deployed_state' & out_acts_forall); eauto.
                    cbn in deployed_state'.
                    rewrite deployed_state0, serialize_prev_state in deployed_state'.
                    inversion deployed_state'.
                    subst. clear deployed_state'.
                    unfold outgoing_acts in out_acts_forall.
                    rewrite queue_prev in out_acts_forall.
                    cbn in out_acts_forall.
                    rewrite address_eq_refl in out_acts_forall.
                    cbn in out_acts_forall.
                    destruct lqt_addr_preserved as [? lqt_addr_preserved].
                    rewrite lqt_addr_preserved in receive_some.
                    rewrite_receive_is_some.
                    apply Forall_inv in out_acts_forall; auto.
                    destruct msg; auto.
                    destruct_match; auto.
                    now destruct m.
                }
                destruct lqt_addr_preserved as [<- | lqt_addr_preserved]; auto.
                destruct lqt_addr_preserved as [? lqt_addr_preserved].
                rewrite lqt_addr_preserved in receive_some.
                rewrite_receive_is_some.
                edestruct outgoing_txs_no_mint_before_set_lqt_addr as (cstate & deployed_state' & out_acts_forall); eauto.
                cbn in deployed_state'.
                rewrite deployed_state0, serialize_prev_state in deployed_state'.
                inversion deployed_state'.
                subst. clear deployed_state'.
                apply out_acts_forall in H2.
                clear out_acts_forall.
                apply All_Forall.In_Forall.
                intros act act_in.
                eapply Forall_forall in H2; eauto.
                destruct_match; auto.
                destruct msg0; auto.
                destruct_match; auto.
                now destruct_match.
          ---- (* Call by other contract *)
              rewrite address_eq_ne by auto.
              destruct lqt_addr_preserved as [<- | lqt_addr_preserved]; auto.
              destruct lqt_addr_preserved as [? lqt_addr_preserved].
              rewrite lqt_addr_preserved in receive_some.
              rewrite_receive_is_some.
              edestruct outgoing_txs_no_mint_before_set_lqt_addr as (cstate & deployed_state' & out_acts_forall); eauto.
              cbn in deployed_state'.
              rewrite deployed_state0, serialize_prev_state in deployed_state'.
              inversion deployed_state'.
              subst. clear deployed_state'.
              apply out_acts_forall in H2.
              clear out_acts_forall.
              apply All_Forall.In_Forall.
              intros act act_in.
              eapply Forall_forall in H2; eauto.
              destruct_match; auto.
              destruct msg0; auto.
              destruct_match; auto.
              now destruct_match.
          --- (* Call other contract *)
              rewrite deployed_state in deployed_state'.
              inversion deployed_state'.
              clear deployed_state'.
              subst.
              destruct_address_eq; auto.
              apply list.Forall_cons.
              split; auto.
              cbn.
              edestruct outgoing_acts_all_mint_same_dest as (cstate & deployed_state' & out_acts_forall); eauto.
              cbn in deployed_state'.
              rewrite deployed_state in deployed_state'.
              inversion deployed_state'.
              subst. clear deployed_state'.
              unfold outgoing_acts in out_acts_forall.
              rewrite queue_prev in out_acts_forall.
              cbn in out_acts_forall.
              rewrite address_eq_refl in out_acts_forall.
              cbn in out_acts_forall.
              apply Forall_inv in out_acts_forall.
              now destruct msg.
        * (* Invalid action *)
          destruct IHtrace as (state' & deployed_state' & sum_eq);
            try rewrite_environment_equiv; auto.
          cbn in *.
          rewrite deployed_state in deployed_state'.
          now inversion deployed_state'.
        * (* Permutation *)
          destruct IHtrace as (state' & deployed_state' & sum_eq);
            rewrite env_eq in *; auto.
          cbn in *.
          rewrite deployed_state in deployed_state'.
          now inversion deployed_state'.
    + constructor.
      now econstructor.
  Qed.

  Lemma outgoing_txs_sum_filter_eq : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        sumZ mintedOrBurnedTokens_tx (filter (txCallTo cstate.(lqtAddress)) (outgoing_txs trace caddr)) =
        sumZ mintedOrBurnedTokens_tx (outgoing_txs trace caddr).
  Proof. 
    intros * deployed.
    apply (outgoing_txs_all_mint_same_dest _ _ trace) in deployed as mint_or_burn_to_lqt_addr; auto.
    destruct mint_or_burn_to_lqt_addr as (cstate & deployed_state & mint_or_burn_to_lqt_addr).
    exists cstate.
    split; auto.
    clear deployed deployed_state.
    induction (outgoing_txs trace caddr).
    - reflexivity.
    - apply list.Forall_cons in mint_or_burn_to_lqt_addr as [mint_or_burn_to_lqt_addr IH%IHl].
      clear IHl.
      cbn.
      rewrite <- IH. clear IH.
      destruct a eqn:H.
      destruct tx_body eqn:H1;
        auto.
      destruct_match eqn:H2; auto.
      cbn in *.
      do 3 (destruct_match; auto).
      now destruct_address_eq.
  Qed.

  (** [lqtTotal] is equal to the initial tokens + minted tokens - burned tokens *)
  Lemma lqt_total_correct' : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate depinfo,
      contract_state bstate caddr = Some cstate /\
      deployment_info Setup trace caddr = Some depinfo /\
      let initial_tokens := lqtTotal_ (deployment_setup depinfo) in
      Z.of_N cstate.(lqtTotal) = (Z.of_N initial_tokens) + sumZ mintedOrBurnedTokens_acts (outgoing_acts bstate caddr)
        + sumZ mintedOrBurnedTokens_tx (outgoing_txs trace caddr).
  Proof.
    contract_induction;
      intros; auto.
    - cbn in *.
      now apply init_correct in init_some.
    - rewrite IH.
      cbn.
      rewrite <- 3!Z.add_assoc.
      rewrite Z.add_cancel_l.
      rewrite Z.add_shuffle3.
      rewrite Z.add_cancel_l.
      rewrite Z.add_cancel_r.
      unfold mintedOrBurnedTokens_tx.
      destruct out_act.
      + now destruct tx_act_match as [_ [_ [-> | ->]]].
      + now destruct tx_act_match as [_ [_ ->]].
      + now destruct tx_act_match as [_ ->].
    - cbn in receive_some.
      destruct msg; try destruct m; try destruct d;
        try (now receive_simpl);
        rewrite_acts_correct;
        rewrite_state_eq;
        rewrite_receive_is_some;
        cbn;
        try rewrite deserialize_serialize;
        destruct_match eqn:msg_deserialized;
          try now inversion msg_deserialized;
          cbn;
          try lia.
      destruct_match; try lia.
      now apply deserialize_balance_of_ne_mint_or_burn in msg_deserialized.
    - destruct head;
        auto;
        cbn in IH;
        destruct action_facts as (? & ? & ?);
        subst.
      + now receive_simpl.
      + cbn in receive_some.
        destruct msg; try destruct m; try destruct d;
          try (now receive_simpl);
          rewrite_acts_correct;
          rewrite_state_eq;
          rewrite_receive_is_some;
          cbn;
          try rewrite deserialize_serialize;
          destruct_match eqn:msg_deserialized;
            try now inversion msg_deserialized;
            cbn;
            try lia.
        * destruct_match; try lia.
          now apply deserialize_balance_of_ne_mint_or_burn in msg_deserialized.
        * destruct_match eqn:msg_deserialized0;
            try now inversion msg_deserialized0.
    - now rewrite <- perm.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      instantiate (CallFacts := fun _ _ _ _ => True).
      unset_all; subst;cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
  Qed.

  (** [lqtTotal] is equal to the initial tokens + minted tokens - burned tokens *)
  Lemma lqt_total_correct : forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate depinfo,
      contract_state bstate caddr = Some cstate /\
      deployment_info Setup trace caddr = Some depinfo /\
      let initial_tokens := lqtTotal_ (deployment_setup depinfo) in
      Z.of_N cstate.(lqtTotal) = (Z.of_N initial_tokens) + sumZ mintedOrBurnedTokens_acts (filter (actTo cstate.(lqtAddress)) (outgoing_acts bstate caddr))
        + sumZ mintedOrBurnedTokens_tx (filter (txCallTo cstate.(lqtAddress)) (outgoing_txs trace caddr)).
  Proof.
    intros * deployed.
    eapply lqt_total_correct' in deployed as lqt_correct.
    apply outgoing_acts_sum_filter_eq in deployed as act_filter_eq; try easy.
    destruct lqt_correct as (cstate & depinfo & deployed_state & deployment_info & lqt_correct).
    destruct act_filter_eq as (cstate' & deployed_state' & act_filter_eq).
    rewrite deployed_state in deployed_state'.
    inversion deployed_state'.
    clear deployed_state'. subst.
    do 2 eexists.
    intuition.
    rewrite act_filter_eq.
    apply (outgoing_txs_sum_filter_eq _ _ trace) in deployed as tx_filter_eq.
    destruct tx_filter_eq as (cstate & deployed_state' & tx_filter_eq).
    rewrite deployed_state in deployed_state'.
    inversion deployed_state'.
    clear deployed_state'. subst.
    rewrite tx_filter_eq.
    apply lqt_correct.
  Qed.
  Local Close Scope Z_scope.

  Lemma mintedOrBurnedTokens_call_eq_tx : forall call_info addr,
    (fun callInfo => mintedOrBurnedTokens callInfo.(call_msg)) call_info =
    (fun callInfo => mintedOrBurnedTokens_tx (contract_call_info_to_tx addr callInfo)) call_info.
  Proof.
    intros.
    destruct call_info.
    destruct call_msg.
    - cbn.
      now rewrite deserialize_serialize.
    - reflexivity.
  Qed.

  Lemma deserialize_lqt_token_msg_right_inverse : forall x (y : Dexter2FA12.Msg),
    (forall x' (y' : Address), deserialize x' = Some y' -> x' = serialize y') ->
    deserialize x = Some y ->
    x = serialize y.
  Proof.
    intros * address_right_inverse deser_some.
    Transparent deserialize serialize.
    cbn in *.
    Local Hint Resolve deserialize_nat_right_inverse
                       deserialize_N_right_inverse
                       deserialize_int_right_inverse
                       deserialize_unit_right_inverse
                       deserialize_serialized_value_right_inverse : deser.
    repeat (try match goal with
    | H : match _ with Some _ => _ | None => _ end = Some _ |- _ = _ => let H2 := fresh "H" in destruct_match eqn:H2 in H; [| discriminate]
    | H : match ?x with 0%nat => _ | S _ => _ end = Some _ |- _ = _ => destruct x; [| try discriminate]
    | H : (let (_, _) := ?p in _) = Some _ |- _ = _ => destruct p
    | H : Some _ = Some _ |- _ = _ => inversion_clear H
    | H : extract_ser_value _ _ = @Some (interp_type ser_unit) ?i |- _ = _ => apply deserialize_unit_right_inverse in H as ->; destruct i
    | H : @deserialize_product _ _ _ _ _ = Some _ |- _ = _ => apply deserialize_product_right_inverse in H as ->; try clear H
    | |- forall _ _, _ -> _ => intros * deser_some; cbn in *
    end; auto with deser).
    Opaque deserialize serialize.
  Qed.


  (** ** lqtTotal/total_supply invariant *)
  Section LqtPoolCorrect.

    Arguments lqt_contract {_ _ _ _} _.
    Arguments lqt_total_supply_correct {_ _ _ _} _.

    (** [lqtTotal] of the main contract is equal to [total_supply] of the liquidity token *)
    (** We define the statement for the liquidity token interface contract interface.
        [LqtTokenInterface]. That is, for any contract with correct signature satisfying
        an additional correctness property, namely [total_supply] is equal to the initial
        tokens + minted tokens - burned tokens *)
    Definition lqtTotal_total_supply_invariant (i_lqt_contract : LqtTokenInterface) : Prop :=
      forall bstate caddr_main caddr_lqt (trace : ChainTrace empty_state bstate),
      env_contracts bstate caddr_main = Some (contract : WeakContract) ->
      env_contracts bstate caddr_lqt = Some (i_lqt_contract.(lqt_contract) : WeakContract) ->
      exists state_main state_lqt depinfo_main depinfo_lqt,
        contract_state bstate caddr_main = Some state_main /\
        contract_state bstate caddr_lqt = Some state_lqt /\
        deployment_info Setup trace caddr_main = Some depinfo_main /\
        deployment_info Dexter2FA12.Setup trace caddr_lqt = Some depinfo_lqt /\
        let initial_tokens_main := lqtTotal_ (deployment_setup depinfo_main) in
        let initial_tokens_lqt := initial_pool (deployment_setup depinfo_lqt) in
        (state_main.(lqtAddress) = caddr_lqt ->
         state_lqt.(admin) = caddr_main ->
        initial_tokens_main = initial_tokens_lqt ->
        filter (actTo state_main.(lqtAddress)) (outgoing_acts bstate caddr_main) = [] ->
          state_main.(lqtTotal) = state_lqt.(total_supply)).

    (** We prove that the invariant hold for any contract satisfying the interface *)
    Lemma lqt_pool_correct_interface :
      forall (i_lqt_contract : LqtTokenInterface), (* for any correct liquidity token *)
         (forall x (y : Address), deserialize x = Some y -> x = serialize y) -> (* a technical condition for serialisation *)
        lqtTotal_total_supply_invariant i_lqt_contract.
    Proof.
      intros ? ? ? ? ? ? deployed_main deployed_lqt.
      apply (lqt_total_correct _ _ trace) in deployed_main as main_correct.
      destruct main_correct as (state_main & depinfo_main & deployed_state_main & deploy_info_main & main_correct).
      apply (lqt_total_supply_correct _ _ _ trace) in deployed_lqt as lqt_correct.
      destruct lqt_correct as (state_lqt & depinfo_lqt & inc_calls_lqt & deployed_state_lqt & deploy_info_lqt & inc_acts_lqt & lqt_correct).
      specialize incomming_eq_outgoing as incoming_eq.
      edestruct incoming_eq as (? & inc_acts_lqt' & calls_eq);
        [| apply deployed_main | apply deployed_lqt |].
      - intros. eapply deserialize_lqt_token_msg_right_inverse; auto.
      - setoid_rewrite inc_acts_lqt in inc_acts_lqt'.
        inversion inc_acts_lqt'.
        subst. clear inc_acts_lqt'.
        do 4 eexists.
        repeat split; eauto.
        cbn.
        intros addr_main_eq addr_lqt_eq init_pool_eq no_waiting_mint_acts.
        apply N2Z.inj.
        rewrite main_correct, lqt_correct, init_pool_eq, no_waiting_mint_acts, addr_main_eq, addr_lqt_eq.
        rewrite Z.add_0_r, Z.add_cancel_l.
        rewrite calls_eq, sumZ_map.
        apply sumZ_eq.
        intros.
        now rewrite <- mintedOrBurnedTokens_call_eq_tx.
    Qed.
  End LqtPoolCorrect.

  (** Now, we prove that the concrete implemention of the liquidity token satisfies the
      inter-contract invariant *)
  Theorem lqt_pool_correct_lqt_fa12 :
    (forall x (y : Address), deserialize x = Some y -> x = serialize y) ->
    lqtTotal_total_supply_invariant Dexter2FA12.LqtFA12Token.
  Proof.
    apply lqt_pool_correct_interface.
  Qed.
  
End Theories.
