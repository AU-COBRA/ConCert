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
Require Import FA2Token FA2Interface Dexter2FA12.


Section Dexter.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

(* ---------------------------------------------------------------------- *)
(* Type Synonyms                                                          *)
(* ---------------------------------------------------------------------- *)

Definition update_token_pool_internal_ := list FA2Interface.balance_of_response.
Definition token_id := FA2Interface.token_id.
Definition token_contract_transfer := FA2Interface.transfer.
Definition balance_of := FA2Interface.balance_of_response.
Definition mintOrBurn := Dexter2FA12.mintOrBurn_param.

(* ---------------------------------------------------------------------- *)
(* Entrypoints                                                            *)
(* ---------------------------------------------------------------------- *)

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

Global Instance add_liquidity_param_serializable : Serializable add_liquidity_param :=
  Derive Serializable add_liquidity_param_rect <build_add_liquidity_param>.

Global Instance remove_liquidity_param_serializable : Serializable remove_liquidity_param :=
  Derive Serializable remove_liquidity_param_rect <build_remove_liquidity_param>.

Global Instance xtz_to_token_param_serializable : Serializable xtz_to_token_param :=
  Derive Serializable xtz_to_token_param_rect <build_xtz_to_token_param>.

Global Instance token_to_xtz_param_serializable : Serializable token_to_xtz_param :=
  Derive Serializable token_to_xtz_param_rect <build_token_to_xtz_param>.

Global Instance set_baker_param_serializable : Serializable set_baker_param :=
  Derive Serializable set_baker_param_rect <build_set_baker_param>.

Global Instance token_to_token_param_serializable : Serializable token_to_token_param :=
  Derive Serializable token_to_token_param_rect <build_token_to_token_param>.

Global Instance DexterMsg_serializable : Serializable DexterMsg :=
    Derive Serializable DexterMsg_rect <AddLiquidity,
                                        RemoveLiquidity,
                                        XtzToToken,
                                        TokenToXtz,
                                        SetBaker,
                                        SetManager,
                                        SetLqtAddress,
                                        UpdateTokenPool,
                                        TokenToToken>.

Definition Msg := @FA2Token.FA2ReceiverMsg BaseTypes DexterMsg _.

(* ---------------------------------------------------------------------- *)
(* Storage                                                                *)
(* ---------------------------------------------------------------------- *)

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
    lqtAddress : option Address
  }.

Record Setup :=
  build_setup {
    lqtTotal_ : N;
    manager_ : Address;
    tokenAddress_ : Address;
    tokenId_ : token_id
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

(* ---------------------------------------------------------------------- *)
(* Functions                                                              *)
(* ---------------------------------------------------------------------- *)

Definition result : Type := option (State * list ActionBody).
Definition isNone {A : Type} (a : option A) := match a with | Some _ => false | None => true end.
Definition isSome {A : Type} (a : option A) := negb (isNone a).
Definition returnIf (cond : bool) := if cond then None else Some tt.
Definition is_a_nat (n : Z) : bool := Z.leb 0 n.
Definition ceildiv (n m : N) : N := if N.modulo n m =? 0 then n / m else (n / m) + 1.

Definition mint_or_burn (state : State) (target : Address) (quantitiy : Z) : option ActionBody :=
    do lqtAddress_ <- state.(lqtAddress) ; (* error lqtAddress not set *)
    Some (act_call lqtAddress_ 0%Z
        (serialize (Dexter2FA12.msg_mint_or_burn
        (Dexter2FA12.build_mintOrBurn_param quantitiy target)))).

Definition token_transfer (state : State) (from to : Address) (amount : N) : ActionBody :=
  act_call state.(tokenAddress) 0%Z
    (serialize (FA2Token.msg_transfer
    [FA2Interface.build_transfer from to state.(tokenId) amount None])).

Definition xtz_transfer (to : Address) (amount : Z) : option ActionBody :=
  if address_is_contract to
  then None (* error_INVALID_TO_ADDRESS *)
  else Some (act_transfer to amount).

(* ---------------------------------------------------------------------- *)
(* Entrypoint Functions                                                   *)
(* ---------------------------------------------------------------------- *)

Definition add_liquidity (chain : Chain) (ctx : ContractCallContext)
                         (state : State) (param : add_liquidity_param)
                         : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (param.(add_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
  let lqt_minted := (Z.to_N ctx.(ctx_amount)) * state.(lqtTotal)  / state.(xtzPool) in
  let tokens_deposited := ceildiv ((Z.to_N ctx.(ctx_amount)) * state.(tokenPool)) state.(xtzPool) in
  do _ <- returnIf (param.(maxTokensDeposited) <? tokens_deposited) ; (* error_MAX_TOKENS_DEPOSITED_MUST_BE_GREATER_THAN_OR_EQUAL_TO_TOKENS_DEPOSITED *)
  do _ <- returnIf (lqt_minted <? param.(minLqtMinted)) ; (* error_LQT_MINTED_MUST_BE_GREATER_THAN_MIN_LQT_MINTED *)
  let new_state := state<| lqtTotal := state.(lqtTotal) + lqt_minted |>
                        <| tokenPool := state.(tokenPool) + tokens_deposited |>
                        <| xtzPool := state.(xtzPool) + (Z.to_N ctx.(ctx_amount))|> in
  let op_token := token_transfer state ctx.(ctx_from) ctx.(ctx_contract_address) tokens_deposited in
  do op_lqt <- mint_or_burn state param.(owner) (Z.of_N lqt_minted) ;
  Some (new_state, [op_token; op_lqt]).

Definition remove_liquidity (chain : Chain) (ctx : ContractCallContext)
                            (state : State) (param : remove_liquidity_param)
                            : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (param.(remove_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  let xtz_withdrawn := ((param.(lqtBurned) * state.(xtzPool)) / state.(lqtTotal)) in
  let tokens_withdrawn := param.(lqtBurned) * state.(tokenPool) /  state.(lqtTotal) in
  do _ <- returnIf (xtz_withdrawn <? param.(minXtzWithdrawn)) ; (* error_THE_AMOUNT_OF_XTZ_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_WITHDRAWN *)
  do _ <- returnIf (tokens_withdrawn <? param.(minTokensWithdrawn)) ; (* error_THE_AMOUNT_OF_TOKENS_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_WITHDRAWN *)
  do _ <- returnIf (state.(lqtTotal) <? param.(lqtBurned)) ; (* error_CANNOT_BURN_MORE_THAN_THE_TOTAL_AMOUNT_OF_LQT *)
  do _ <- returnIf (state.(tokenPool) <? tokens_withdrawn) ; (* error_TOKEN_POOL_MINUS_TOKENS_WITHDRAWN_IS_NEGATIVE *)
  do op_lqt <- mint_or_burn state ctx.(ctx_from) (0 - (Z.of_N param.(lqtBurned)))%Z ;
  let op_token := token_transfer state ctx.(ctx_contract_address) param.(liquidity_to) tokens_withdrawn in
  do opt_xtz <- xtz_transfer param.(liquidity_to) (Z.of_N xtz_withdrawn) ;
  let new_state := state<| xtzPool := state.(xtzPool) - xtz_withdrawn |>
                        <| lqtTotal := state.(lqtTotal) - param.(lqtBurned) |>
                        <| tokenPool := state.(tokenPool) - tokens_withdrawn |> in
  Some (new_state, [op_lqt; op_token; opt_xtz]).

Definition xtz_to_token (chain : Chain) (ctx : ContractCallContext)
                        (state : State) (param : xtz_to_token_param)
                        : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (param.(xtt_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
  let tokens_bought :=
    ((Z.to_N ctx.(ctx_amount)) * 997 * state.(tokenPool)) /
      (state.(xtzPool) * 1000 + ((Z.to_N ctx.(ctx_amount)) * 997)) in
  do _ <- returnIf (tokens_bought <? param.(minTokensBought)) ; (* error_TOKENS_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_BOUGHT *)
  do _ <- returnIf (state.(tokenPool) <? tokens_bought) ; (* error_TOKEN_POOL_MINUS_TOKENS_BOUGHT_IS_NEGATIVE *)
  let new_state := state<| xtzPool := state.(xtzPool) + (Z.to_N ctx.(ctx_amount)) |>
                        <| tokenPool := state.(tokenPool) - tokens_bought |> in
  let op := token_transfer state ctx.(ctx_contract_address) param.(tokens_to) tokens_bought in
  Some (new_state, [op]).

Definition token_to_xtz (chain : Chain) (ctx : ContractCallContext)
                        (state : State) (param : token_to_xtz_param)
                        : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (param.(ttx_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  let xtz_bought :=
    (((param.(tokensSold) * 997 * state.(xtzPool)) /
      (state.(tokenPool) * 1000 + (param.(tokensSold) * 997)))) in
  do _ <- returnIf (xtz_bought <? param.(minXtzBought)) ; (* error_XTZ_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_BOUGHT *)
  let op_token := token_transfer state ctx.(ctx_from) ctx.(ctx_contract_address) param.(tokensSold) in
  do op_tez <- xtz_transfer param.(xtz_to) (Z.of_N xtz_bought) ;
  let new_state := state<| tokenPool := state.(tokenPool) + param.(tokensSold) |>
                        <| xtzPool := state.(xtzPool) - xtz_bought |> in
  Some (new_state, [op_token; op_tez]).

Definition default_ (chain : Chain) (ctx : ContractCallContext)
                    (state : State) : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  let new_state := state<| xtzPool := state.(xtzPool) + Z.to_N ctx.(ctx_amount) |> in
    Some (new_state, []).

Definition set_baker (chain : Chain) (ctx : ContractCallContext)
                     (state : State) (param : set_baker_param)
                     : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  do _ <- returnIf (negb (address_eqb ctx.(ctx_from) state.(manager))) ; (* error_ONLY_MANAGER_CAN_SET_BAKER *)
  do _ <- returnIf (state.(freezeBaker)) ; (* error_BAKER_PERMANENTLY_FROZEN *)
    Some (state<| freezeBaker := param.(freezeBaker_) |>, []).

Definition set_manager (chain : Chain) (ctx : ContractCallContext)
                       (state : State) (new_manager : Address)
                       : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  do _ <- returnIf (negb (address_eqb ctx.(ctx_from) state.(manager))) ; (* error_ONLY_MANAGER_CAN_SET_MANAGER *)
    Some (state<| manager := new_manager |>, []).

Definition set_lqt_address (chain : Chain) (ctx : ContractCallContext)
                           (state : State) (new_lqt_address : Address)
                           : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  do _ <- returnIf (negb (address_eqb ctx.(ctx_from) state.(manager))) ; (* error_ONLY_MANAGER_CAN_SET_LQT_ADRESS *)
  do _ <- returnIf (isSome state.(lqtAddress)) ; (* error_LQT_ADDRESS_ALREADY_SET *)
    Some (state<| lqtAddress := Some new_lqt_address |>, []).

Definition update_token_pool (chain : Chain) (ctx : ContractCallContext)
                             (state : State) : result :=
  do _ <- returnIf (address_is_contract ctx.(ctx_from)) ; (* error_CALL_NOT_FROM_AN_IMPLICIT_ACCOUNT *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_UNEXPECTED_REENTRANCE_IN_UPDATE_TOKEN_POOL *)
  let balance_of_request :=
    FA2Interface.Build_balance_of_request ctx.(ctx_contract_address) state.(tokenId) in
  let balance_of_param :=
    FA2Interface.Build_balance_of_param [balance_of_request] (FA2Interface.Build_callback _ None) in
  let op :=
    act_call state.(tokenAddress) 0%Z (serialize (FA2Token.msg_balance_of balance_of_param)) in
    Some (state<| selfIsUpdatingTokenPool := true |>, [op]).

Definition update_token_pool_internal (chain : Chain) (ctx : ContractCallContext)
                                      (state : State) (token_pool : update_token_pool_internal_)
                                      : result :=
  do _ <- returnIf ((negb state.(selfIsUpdatingTokenPool)) ||
                    (negb (address_eqb ctx.(ctx_from) state.(tokenAddress)))) ; (* error_THIS_ENTRYPOINT_MAY_ONLY_BE_CALLED_BY_GETBALANCE_OF_TOKENADDRESS *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  do token_pool <-
    match token_pool with
    | [] => None (* error_INVALID_FA2_BALANCE_RESPONSE *)
    | x :: xs => Some x.(balance)
    end ;
  let new_state := state<| tokenPool := token_pool |><| selfIsUpdatingTokenPool := false |> in
  Some (new_state, []).

Definition token_to_token (chain : Chain) (ctx : ContractCallContext)
                          (state : State) (param : token_to_token_param)
                          : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  do _ <- returnIf (param.(ttt_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
  let xtz_bought :=
    (((param.(tokensSold_) * 997 * state.(xtzPool)) / 
      (state.(tokenPool) * 1000 + (param.(tokensSold_) * 997)))) in
  let new_state := state<| tokenPool := state.(tokenPool) + param.(tokensSold_) |>
                        <| xtzPool := state.(xtzPool) - xtz_bought |> in
  let op1 := token_transfer state ctx.(ctx_from) ctx.(ctx_contract_address) param.(tokensSold_) in
  let op2 := act_call param.(outputDexterContract) (Z.of_N xtz_bought)
    (serialize (FA2Token.other_msg (XtzToToken {|
      tokens_to := param.(to_);
      minTokensBought := param.(minTokensBought_);
      xtt_deadline := param.(ttt_deadline)
    |}))) in 
  Some (new_state, [op1; op2]).

(* ---------------------------------------------------------------------- *)
(* Main                                                                   *)
(* ---------------------------------------------------------------------- *)

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
    lqtAddress := None
  |}.

Definition contract : Contract Setup Msg State :=
  build_contract init receive.

Section Theories.
End Theories.
End Dexter.
