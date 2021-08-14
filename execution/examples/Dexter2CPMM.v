From Coq Require Import ZArith Lia.
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
    lqtAddress : Address;
    nullAddress : Address
  }.

Record Setup :=
  build_setup {
    lqtTotal_ : N;
    manager_ : Address;
    tokenAddress_ : Address;
    tokenId_ : token_id;
    nullAddress_ : Address
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
(* Helper Functions                                                       *)
(* ---------------------------------------------------------------------- *)

Definition result : Type := option (State * list ActionBody).
Definition isNone {A : Type} (a : option A) := match a with | Some _ => false | None => true end.
Definition isSome {A : Type} (a : option A) := negb (isNone a).
Definition returnIf (cond : bool) := if cond then None else Some tt.
Definition sub (n m : N) : option N := do _ <- returnIf (n <? m) ; Some (n - m).
Definition div (n m : N) : option N := do _ <- returnIf (m =? 0) ; Some (n / m).
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


(* Place holder for tezos set delegate operation *)
Definition set_delegate_call (addr : option Address) : list ActionBody := [].

Definition mint_or_burn (state : State) (target : Address) (quantitiy : Z) : option ActionBody :=
    do _ <- returnIf (address_eqb state.(lqtAddress) state.(nullAddress)) ; (* error lqtAddress not set *)
    Some (act_call state.(lqtAddress) 0%Z
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
  do lqt_minted <- div ((Z.to_N ctx.(ctx_amount)) * state.(lqtTotal)) state.(xtzPool) ; (* error_DIV_by_0 *)
  do tokens_deposited <- ceildiv ((Z.to_N ctx.(ctx_amount)) * state.(tokenPool)) state.(xtzPool) ; (* error_DIV_by_0 *)
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
  do xtz_withdrawn <-  div (param.(lqtBurned) * state.(xtzPool)) state.(lqtTotal) ; (* error_DIV_by_0 *)
  do tokens_withdrawn <- div (param.(lqtBurned) * state.(tokenPool)) state.(lqtTotal) ; (* error_DIV_by_0 *)
  do _ <- returnIf (xtz_withdrawn <? param.(minXtzWithdrawn)) ; (* error_THE_AMOUNT_OF_XTZ_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_WITHDRAWN *)
  do _ <- returnIf (tokens_withdrawn <? param.(minTokensWithdrawn)) ; (* error_THE_AMOUNT_OF_TOKENS_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_WITHDRAWN *)
  do new_lqtPool <- sub state.(lqtTotal) param.(lqtBurned) ; (* error_CANNOT_BURN_MORE_THAN_THE_TOTAL_AMOUNT_OF_LQT *)
  do new_tokenPool <- sub state.(tokenPool) tokens_withdrawn ; (* error_TOKEN_POOL_MINUS_TOKENS_WITHDRAWN_IS_NEGATIVE *)
  do new_xtzPool <- sub state.(xtzPool) xtz_withdrawn ; (* mutez subtraction run time error *)
  do op_lqt <- mint_or_burn state ctx.(ctx_from) (0 - (Z.of_N param.(lqtBurned)))%Z ;
  let op_token := token_transfer state ctx.(ctx_contract_address) param.(liquidity_to) tokens_withdrawn in
  do opt_xtz <- xtz_transfer param.(liquidity_to) (Z.of_N xtz_withdrawn) ;
  let new_state := state<| xtzPool := new_xtzPool |>
                        <| lqtTotal := new_lqtPool|>
                        <| tokenPool := new_tokenPool |> in
  Some (new_state, [op_lqt; op_token; opt_xtz]).

Definition xtz_to_token (chain : Chain) (ctx : ContractCallContext)
                        (state : State) (param : xtz_to_token_param)
                        : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (param.(xtt_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
  do tokens_bought <- div
    ((Z.to_N ctx.(ctx_amount)) * 997 * state.(tokenPool))
      (state.(xtzPool) * 1000 + ((Z.to_N ctx.(ctx_amount)) * 997)) ; (* error_DIV_by_0 *)
  do _ <- returnIf (tokens_bought <? param.(minTokensBought)) ; (* error_TOKENS_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_BOUGHT *)
  do new_tokenPool <- sub state.(tokenPool) tokens_bought ; (* error_TOKEN_POOL_MINUS_TOKENS_BOUGHT_IS_NEGATIVE *)
  let new_state := state<| xtzPool := state.(xtzPool) + (Z.to_N ctx.(ctx_amount)) |>
                        <| tokenPool := new_tokenPool |> in
  let op := token_transfer state ctx.(ctx_contract_address) param.(tokens_to) tokens_bought in
  Some (new_state, [op]).

Definition token_to_xtz (chain : Chain) (ctx : ContractCallContext)
                        (state : State) (param : token_to_xtz_param)
                        : result :=
  do _ <- returnIf state.(selfIsUpdatingTokenPool) ; (* error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE *)
  do _ <- returnIf (param.(ttx_deadline) <=? chain.(current_slot))%nat ; (* error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE *)
  do _ <- returnIf (0 <? ctx.(ctx_amount))%Z ; (* error_AMOUNT_MUST_BE_ZERO *)
  do xtz_bought <- div
    (param.(tokensSold) * 997 * state.(xtzPool))
      (state.(tokenPool) * 1000 + (param.(tokensSold) * 997)) ; (* error_DIV_by_0 *)
  do _ <- returnIf (xtz_bought <? param.(minXtzBought)) ; (* error_XTZ_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_BOUGHT *)
  do new_xtzPool <- sub state.(xtzPool) xtz_bought ; (* mutez subtraction run time error *)
  let op_token := token_transfer state ctx.(ctx_from) ctx.(ctx_contract_address) param.(tokensSold) in
  do op_tez <- xtz_transfer param.(xtz_to) (Z.of_N xtz_bought) ;
  let new_state := state<| tokenPool := state.(tokenPool) + param.(tokensSold) |>
                        <| xtzPool := new_xtzPool |> in
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
    Some (state<| freezeBaker := param.(freezeBaker_) |>, set_delegate_call param.(baker)).

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
  do _ <- returnIf (negb (address_eqb state.(lqtAddress) state.(nullAddress))) ; (* error_LQT_ADDRESS_ALREADY_SET *)
    Some (state<| lqtAddress := new_lqt_address |>, []).

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
  do xtz_bought <- div
    (param.(tokensSold_) * 997 * state.(xtzPool))
      (state.(tokenPool) * 1000 + (param.(tokensSold_) * 997)) ; (* error_DIV_by_0 *)
  do new_xtzPool <- sub state.(xtzPool) xtz_bought ; (* mutez subtraction run time error *)
  let new_state := state<| tokenPool := state.(tokenPool) + param.(tokensSold_) |>
                        <| xtzPool := new_xtzPool |> in
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
    lqtAddress := setup.(nullAddress_);
    nullAddress := setup.(nullAddress_)
  |}.

Definition contract : Contract Setup Msg State :=
  build_contract init receive.

Section Theories.

(* ---------------------------------------------------------------------- *)
(* Tactics and facts about helper functions                               *)
(* ---------------------------------------------------------------------- *)

Ltac returnIf H :=
  match type of H with
  | returnIf _ = None =>
    let G := fresh "G" in
      unfold returnIf in H;
      destruct_match eqn:G in H; try congruence;
      clear H;
      rename G into H
  | returnIf _ = Some ?u =>
    let G := fresh "G" in
      unfold returnIf in H;
      destruct_match eqn:G in H; try congruence;
      clear H u;
      rename G into H
  end.

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
  returnIf m_not_zero.
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
  returnIf m_zero.
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
  returnIf m_le_n.
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
  returnIf n_lt_m.
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
  | H : returnIf _ = None |- _ => returnIf H
  | H : returnIf _ = Some ?u |- _ => returnIf H
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

Tactic Notation "receive_simpl" := repeat receive_simpl_step.



(* ---------------------------------------------------------------------- *)
(* Set baker correct                                                      *)
(* ---------------------------------------------------------------------- *)

(* set_baker only changes freezeBaker in state *)
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

(* set_baker produces no new_acts *)
Lemma set_baker_new_acts_correct : forall chain ctx prev_state param new_state new_acts,
  receive chain ctx prev_state (Some (FA2Token.other_msg (SetBaker param))) = Some (new_state, new_acts) ->
    new_acts = set_delegate_call param.(baker).
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

(* If the requirements are met then then receive on set_baker msg must succeed and
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
    rename H0 into ctx_amount_zero.
    apply Z.ltb_ge in ctx_amount_zero.
    repeat split; auto.
    now destruct_address_eq.
Qed.



(* ---------------------------------------------------------------------- *)
(* Set manager correct                                                    *)
(* ---------------------------------------------------------------------- *)

(* set_manager only changes manager in state *)
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

(* set_manager produces no new_acts *)
Lemma set_manager_new_acts_correct : forall chain ctx prev_state new_manager new_state new_acts,
  receive chain ctx prev_state (Some (FA2Token.other_msg (SetManager new_manager))) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

(* If the requirements are met then then receive on set_manager msg must succeed and
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
    rename H0 into ctx_amount_zero.
    apply Z.ltb_ge in ctx_amount_zero.
    repeat split; auto.
    now destruct_address_eq.
Qed.


(* ---------------------------------------------------------------------- *)
(* Set liquidity address correct                                          *)
(* ---------------------------------------------------------------------- *)

(* set_lqt_address only changes lqt address in state *)
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

(* set_lqt_address produces no new_acts *)
Lemma set_lqt_address_new_acts_correct : forall chain ctx prev_state new_lqt_address new_state new_acts,
  receive chain ctx prev_state (Some (FA2Token.other_msg (SetLqtAddress new_lqt_address))) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

(* If the requirements are met then then receive on set_lqt_address msg must succeed and
    if receive on set_lqt_address msg succeeds then requirements must hold *)
Lemma set_lqt_address_is_some : forall prev_state chain ctx new_lqt_address,
  (ctx_amount ctx <= 0)%Z /\
  prev_state.(selfIsUpdatingTokenPool) = false /\
  ctx.(ctx_from) = prev_state.(manager) /\
  prev_state.(lqtAddress) = prev_state.(nullAddress)
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
    rename H0 into ctx_amount_zero.
    rename H2 into lqt_address_not_set.
    apply Z.ltb_ge in ctx_amount_zero.
    repeat split; auto;
      now destruct_address_eq.
Qed.

(* ---------------------------------------------------------------------- *)
(* default entrypoint correct                                             *)
(* ---------------------------------------------------------------------- *)

(* default_ only changes xtzPool in state *)
Lemma default_state_eq : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state None = Some (new_state, new_acts) ->
    prev_state<| xtzPool := prev_state.(xtzPool) + Z.to_N (ctx.(ctx_amount)) |> = new_state.
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

Lemma default_correct : forall prev_state new_state chain ctx new_acts,
  receive chain ctx prev_state None = Some (new_state, new_acts) ->
    new_state.(xtzPool) = prev_state.(xtzPool) + Z.to_N (ctx.(ctx_amount)).
Proof.
  intros * receive_some.
  apply default_state_eq in receive_some.
  now subst.
Qed.

(* default_ produces no new_acts *)
Lemma default_new_acts_correct : forall chain ctx prev_state new_state new_acts,
  receive chain ctx prev_state None = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

(* If the requirements are met then then receive on None msg must succeed and
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

(* ---------------------------------------------------------------------- *)
(* update token pool correct                                              *)
(* ---------------------------------------------------------------------- *)

(* update_token_pool only changes selfIsUpdatingTokenPool in state *)
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

(* update_token_pool produces an call act with amount = 0, calling
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
  receive_simpl.
Qed.

(* If the requirements are met then then receive on update_token_pool msg must succeed and
    if receive on update_token_pool msg succeeds then requirements must hold *)
Lemma update_token_pool_is_some : forall prev_state chain ctx,
  (ctx_amount ctx <= 0)%Z /\
  prev_state.(selfIsUpdatingTokenPool) = false /\
  address_is_contract ctx.(ctx_from) = false
  <->
  exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg UpdateTokenPool)) = Some (new_state, new_acts).
Proof.
  split.
  - intros (amount_zero & not_updating & sender_not_contract).
    do 2 eexists.
    receive_simpl.
    destruct_match eqn:sender_check.
    destruct_match eqn:amount_check.
    destruct_match eqn:updating_check.
    + reflexivity.
    + now rewrite not_updating in updating_check.
    + receive_simpl.
      now apply Z.ltb_ge in amount_zero.
    + now rewrite sender_not_contract in sender_check.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    rename H0 into ctx_amount_zero.
    now apply Z.ltb_ge in ctx_amount_zero.
Qed.

(* ---------------------------------------------------------------------- *)
(* update token pool internal correct                                     *)
(* ---------------------------------------------------------------------- *)

(* update_token_pool_internal only changes selfIsUpdatingTokenPool and tokenPool in state *)
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
  rename H1 into response.
  destruct_match eqn:resonses_empty_check in response;
    try congruence.
  now inversion_clear response.
Qed.

Lemma update_token_pool_internal_update_correct : forall prev_state new_state chain ctx new_acts responses,
  receive chain ctx prev_state (Some (FA2Token.receive_balance_of_param responses)) = Some (new_state, new_acts) ->
    new_state.(selfIsUpdatingTokenPool) = false.
Proof.
  intros * receive_some.
  apply update_token_pool_internal_state_eq in receive_some.
  now subst.
Qed.

(* update_token_pool_internal produces no new actions *)
Lemma update_token_pool_internal_new_acts_correct : forall chain ctx prev_state new_state new_acts responses,
  receive chain ctx prev_state (Some (FA2Token.receive_balance_of_param responses)) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

(* If the requirements are met then then receive on update_token_pool_internal msg must succeed and
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
    rename H0 into ctx_amount_zero.
    rename H into sender_check.
    rename H1 into responses_check.
    apply Bool.orb_false_elim in sender_check as
      (is_updating & sender_is_token_contract).
    apply Z.ltb_ge in ctx_amount_zero.
    destruct responses eqn:response in responses_check;
      try congruence.
    subst.
    repeat split; auto.
    + now apply Bool.negb_false_iff in is_updating.
    + now destruct_address_eq.
Qed.

(* ---------------------------------------------------------------------- *)
(* Add liquidity correct                                                  *)
(* ---------------------------------------------------------------------- *)

(* add_liquidity only changes lqtTotal, tokenPool and xtzPool in state *)
Lemma add_liquidity_state_eq : forall prev_state new_state chain ctx new_acts param,
  let lqt_minted := Z.to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) in
  let tokens_deposited := ceildiv_ (Z.to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) in
  receive chain ctx prev_state (Some (FA2Token.other_msg (AddLiquidity param))) = Some (new_state, new_acts) ->
    prev_state<| lqtTotal := prev_state.(lqtTotal) +  lqt_minted |>
              <| tokenPool := prev_state.(tokenPool) + tokens_deposited |>
              <| xtzPool := prev_state.(xtzPool) + Z.to_N ctx.(ctx_amount) |> = new_state.
Proof.
  intros * receive_some.
  receive_simpl.
  now math_convert.
Qed.

Lemma add_liquidity_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (FA2Token.other_msg (AddLiquidity param))) = Some (new_state, new_acts) ->
    new_state.(lqtTotal) = prev_state.(lqtTotal) + Z.to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) /\
    new_state.(tokenPool) = prev_state.(tokenPool) + ceildiv_ (Z.to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) /\
    new_state.(xtzPool) = prev_state.(xtzPool) + Z.to_N ctx.(ctx_amount).
Proof.
  intros * receive_some.
  apply add_liquidity_state_eq in receive_some.
  now subst.
Qed.

(* add_liquidity should produce two acts
    1: an call action to the token contract requesting <tokens_deposited> tokens to be moved from <owner> to this contract
    2: an call action to the lqt contract requsting <lqt_minted> tokens to be minted to <owner>
 *)
Lemma add_liquidity_new_acts_correct : forall chain ctx prev_state new_state new_acts param,
  let lqt_minted := Z.to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) in
  let tokens_deposited := ceildiv_ (Z.to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) in
  receive chain ctx prev_state (Some (FA2Token.other_msg (AddLiquidity param))) = Some (new_state, new_acts) ->
    new_acts =
    [
      (act_call prev_state.(tokenAddress) 0%Z
        (serialize (FA2Token.msg_transfer
        [build_transfer param.(owner) ctx.(ctx_contract_address) prev_state.(tokenId) tokens_deposited None])));
      (act_call prev_state.(lqtAddress) 0%Z
        (serialize (Dexter2FA12.msg_mint_or_burn {| target := param.(owner); quantity := Z.of_N lqt_minted|})))
    ].
Proof.
  intros * receive_some.
  receive_simpl.
  math_convert.
  unfold token_transfer.
  repeat f_equal.
  give_up.
Abort.

(* In the informal specification it is stated that tokens should be trasnfered from owner,
    but in the implementation it is trasnfered from the sender.
   For this we assume that the implementation is correct over the informal specification since
    that is what other formalizations seem to have assumed *)
Lemma add_liquidity_new_acts_correct : forall chain ctx prev_state new_state new_acts param,
  let lqt_minted := Z.to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) in
  let tokens_deposited := ceildiv_ (Z.to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) in
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

(* If the requirements are met then then receive on add_liquidity msg must succeed and
    if receive on add_liquidity msg succeeds then requirements must hold *)
Lemma add_liquidity_is_some : forall prev_state chain ctx param,
  let lqt_minted := Z.to_N ctx.(ctx_amount) * prev_state.(lqtTotal) / prev_state.(xtzPool) in
  let tokens_deposited := ceildiv_ (Z.to_N ctx.(ctx_amount) * prev_state.(tokenPool)) prev_state.(xtzPool) in
  prev_state.(selfIsUpdatingTokenPool) = false /\
  (current_slot chain < param.(add_deadline))%nat /\
  tokens_deposited <= param.(maxTokensDeposited)  /\
  param.(minLqtMinted) <= lqt_minted /\
  prev_state.(xtzPool) <> 0 /\
  prev_state.(lqtAddress) <> prev_state.(nullAddress)
  <->
  exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (AddLiquidity param))) = Some (new_state, new_acts).
Proof.
  split.
  - intros (not_updating & deadline_not_hit & max_tokens_not_hit &
            enough_minted & xtzPool_not_zero & lqt_addr_set).
    unfold receive.
    cbn.
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
    rename H0 into deadline_not_hit.
    rename H3 into max_not_hit.
    rename H4 into min_not_hit.
    apply leb_complete_conv in deadline_not_hit.
    apply N.ltb_ge in max_not_hit.
    apply N.ltb_ge in min_not_hit.
    repeat split; auto.
    now destruct_address_eq.
Qed.

(* ---------------------------------------------------------------------- *)
(* Remove liquidity correct                                               *)
(* ---------------------------------------------------------------------- *)

(* remove_liquidity only changes lqtTotal, tokenPool and xtzPool in state *)
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
  now math_convert.
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

(* remove_liquidity should produce three acts
    1: a call action to LQT contract burning <lqtBurned> from <sender>
    2: a call action to token contract transferring <tokens_withdrawn> from this contract to <liquidity_to>
    3: a transfer action transferring <xtz_withdrawn> from this contract to <liquidity_to>
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
      (act_transfer param.(liquidity_to) (Z.of_N xtz_withdrawn))
    ].
Proof.
  intros * receive_some.
  receive_simpl.
  math_convert.
  rename H10 into xtz_act.
  unfold xtz_transfer in xtz_act.
  destruct_match in xtz_act; try congruence.
  now inversion_clear xtz_act.
Qed.

(* If the requirements are met then then receive on remove_liquidity msg must succeed and
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
  prev_state.(lqtAddress) <> prev_state.(nullAddress)
  <->
  exists new_state new_acts, receive chain ctx prev_state (Some (FA2Token.other_msg (RemoveLiquidity param))) = Some (new_state, new_acts).
Proof.
  split.
  - intros (not_updating & deadline_not_hit & ctx_amount_zero &
            lqtPool_not_zero & enough_xtz_withdrawn & enough_tokens_withdrawn &
            tokens_withdrawn_le_total & xtz_withdrawn_le_total & lqt_burned_le_total &
            to_not_contract & lqt_addr_set).
    unfold receive.
    cbn.
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
    rename H0 into deadline_not_hit.
    rename H1 into ctx_amount_zero.
    rename H4 into enough_xtz_withdrawn.
    rename H5 into enough_tokens_withdrawn.
    rename H10 into transfer_act.
    apply leb_complete_conv in deadline_not_hit.
    apply N.ltb_ge in enough_tokens_withdrawn.
    apply N.ltb_ge in enough_xtz_withdrawn.
    apply Z.ltb_ge in ctx_amount_zero.
    unfold xtz_transfer in transfer_act.
    destruct_match eqn:to_not_contract in transfer_act;
      try congruence.
    repeat split; auto.
    now destruct_address_eq.
Qed.

(* ---------------------------------------------------------------------- *)
(* xtz to token correct                                                   *)
(* ---------------------------------------------------------------------- *)

(* xtz_to_token only changes tokenPool and xtzPool in state *)
Lemma xtz_to_token_state_eq : forall prev_state new_state chain ctx new_acts param,
  let tokens_bought := ((Z.to_N ctx.(ctx_amount)) * 997 * prev_state.(tokenPool)) /
                          (prev_state.(xtzPool) * 1000 + ((Z.to_N ctx.(ctx_amount)) * 997)) in
  receive chain ctx prev_state (Some (FA2Token.other_msg (XtzToToken param))) = Some (new_state, new_acts) ->
    prev_state<| tokenPool := prev_state.(tokenPool) - tokens_bought |>
              <| xtzPool := prev_state.(xtzPool) + Z.to_N ctx.(ctx_amount) |> = new_state.
Proof.
  intros * receive_some.
  receive_simpl.
  now math_convert.
Qed.

Lemma xtz_to_token_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (FA2Token.other_msg (XtzToToken param))) = Some (new_state, new_acts) ->
    new_state.(tokenPool) = prev_state.(tokenPool) -  (((Z.to_N ctx.(ctx_amount)) * 997 * prev_state.(tokenPool)) /
                          (prev_state.(xtzPool) * 1000 + ((Z.to_N ctx.(ctx_amount)) * 997)) ) /\
    new_state.(xtzPool) = prev_state.(xtzPool) + Z.to_N ctx.(ctx_amount).
Proof.
  intros * receive_some.
  apply xtz_to_token_state_eq in receive_some.
  now subst.
Qed.

(* xtz_to_token should produce one action
    1: a call action to token contract transferring <tokens_bought> from this contract to <tokens_to>
 *)
Lemma xtz_to_token_new_acts_correct : forall chain ctx prev_state new_state new_acts param,
  let tokens_bought := ((Z.to_N ctx.(ctx_amount)) * 997 * prev_state.(tokenPool)) /
                          (prev_state.(xtzPool) * 1000 + ((Z.to_N ctx.(ctx_amount)) * 997)) in
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

(* If the requirements are met then then receive on xtz_to_token msg must succeed and
    if receive on xtz_to_token msg succeeds then requirements must hold *)
Lemma xtz_to_token_is_some : forall prev_state chain ctx param,
  let tokens_bought := ((Z.to_N ctx.(ctx_amount)) * 997 * prev_state.(tokenPool)) /
                          (prev_state.(xtzPool) * 1000 + ((Z.to_N ctx.(ctx_amount)) * 997)) in
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
    cbn.
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
    rename H0 into deadline_not_hit.
    rename H2 into enough_tokens_bought.
    apply leb_complete_conv in deadline_not_hit.
    apply N.ltb_ge in enough_tokens_bought.
    now repeat split.
Qed.



(* ---------------------------------------------------------------------- *)
(* token to xtz correct                                                   *)
(* ---------------------------------------------------------------------- *)

(* token_to_xtz only changes tokenPool and xtzPool in state *)
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

(* token_to_xtz should produce two actions
    1: a call action to token contract transferring <tokens_sold> from <sender> to this contract
    2: a transfer action transferring <xtz_bought> from this contract to <xtz_to>
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
      (act_transfer param.(xtz_to) (Z.of_N xtz_bought))
    ].
Proof.
  intros * receive_some.
  receive_simpl.
  math_convert.
  rename H5 into xtz_act.
  unfold xtz_transfer in xtz_act.
  destruct_match in xtz_act; try congruence.
  now inversion_clear xtz_act.
Qed.

(* If the requirements are met then then receive on token_to_xtz msg must succeed and
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
    rename H0 into deadline_not_hit.
    rename H1 into ctx_amount_zero.
    rename H3 into enough_xtz_bought.
    rename H5 into transfer_act.
    apply leb_complete_conv in deadline_not_hit.
    apply N.ltb_ge in enough_xtz_bought.
    apply Z.ltb_ge in ctx_amount_zero.
    unfold xtz_transfer in transfer_act.
    destruct_match eqn:to_not_contract in transfer_act;
      try congruence.
    now repeat split.
Qed.

(* ---------------------------------------------------------------------- *)
(* token to token correct                                                 *)
(* ---------------------------------------------------------------------- *)

(* token_to_token only changes tokenPool and xtzPool in state *)
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

(* token_to_token should produce two actions
    1: a call action to token contract transferring <tokens_sold> from <sender> to this contract
    2: a call action to <outputDexterContract> xtz_to_token entrypoint with <xtz_bought> amount attached
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
      (act_call param.(outputDexterContract) (Z.of_N xtz_bought)
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

(* If the requirements are met then then receive on token_to_token msg must succeed and
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
    rename H1 into deadline_not_hit.
    rename H0 into ctx_amount_zero.
    apply leb_complete_conv in deadline_not_hit.
    apply Z.ltb_ge in ctx_amount_zero.
    now repeat split.
Qed.

(* ---------------------------------------------------------------------- *)
(* init correct                                                           *)
(* ---------------------------------------------------------------------- *)

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
      lqtAddress := setup.(nullAddress_);
      nullAddress := setup.(nullAddress_);
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
    lqtAddress state = setup.(nullAddress_) /\
    nullAddress state = setup.(nullAddress_) /\
    tokenId state = setup.(tokenId_).
Proof.
  intros * init_some.
  apply init_state_eq in init_some.
  now subst.
Qed.

(* initialization should always succeed *)
Lemma init_is_some : forall chain ctx setup,
  exists state, init chain ctx setup = state.
Proof.
  intros.
  eauto.
Qed.

End Theories.
End Dexter.
