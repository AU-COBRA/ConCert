From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Dexter2 Require Import Dexter2CPMM.
From ConCert.Examples.Dexter2 Require Import Dexter2FA12.
From ConCert.Examples.Dexter2 Require Import Dexter2Gens.
From ConCert.Examples.Dexter2 Require Export Dexter2Printers.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2LegacyInterface.
From Coq Require Import ZArith_base.
From Coq Require Import List.
Import ListNotations.


(** * Test setup *)
(** ** Setup parameters *)
Definition token_contract_base_addr : Address := addr_of_Z 128.
Definition lqt_contract_base_addr : Address := addr_of_Z 129.
Definition cpmm_contract_base_addr : Address := addr_of_Z 130.
Definition null_address_ : Address := creator.
Definition token_id_ : N := 1.
Definition initial_lqt : N := 10.
Definition initial_tokens : N := 500.

Module TestInfo <: Dexter2Info.
  Definition accounts := [person_1; person_2; person_3; person_4; person_5].
  Definition gAddr (c : Chain) := elems [person_1; person_2; person_3; person_4; person_5].
  Definition cpmm_contract_addr := cpmm_contract_base_addr.
  Definition token_contract_addr := token_contract_base_addr.
  Definition token_id := token_id_.
End TestInfo.
Module MG := Dexter2Gens TestInfo. Import MG.

(** ** Setup actions *)
(** Transfer some coins to each user address *)
Definition transfer_initial_funds := map (fun addr => TestUtils.build_transfer creator addr 8) TestInfo.accounts.

(** We deploy the token contract with a single token id configured *)
Definition token_setup := {|
  setup_total_supply        := [(token_id_, 0%N)]; (* Value not used *)
  setup_tokens              := FMap.of_list [(token_id_, Build_token_metadata token_id_ 18%N)];
  initial_permission_policy := {|
    descr_self      := self_transfer_permitted; (* Allow self transfers *)
    descr_operator  := operator_transfer_permitted; (* All operator transfers *)
    descr_receiver  := owner_no_op; (* Value not used *)
    descr_sender    := owner_no_op; (* Value not used *)
    descr_custom    := None; (* Value not used *)
  |};
  transfer_hook_addr_       := None; (* No transfer hook configured *)
|}.
Definition deploy_token := build_deploy creator 0 FA2Token.contract token_setup.
(** Allow CPMM contract to operate on all user accounts' tokens *)
Definition setup_operators := map (fun addr => build_call addr token_contract_base_addr 0
    (msg_update_operators [
      add_operator (Build_operator_param addr cpmm_contract_base_addr all_tokens)
    ])
  ) TestInfo.accounts.
(** Create tokens in some user accounts *)
Definition create_tokens := map (fun addr => build_call addr token_contract_base_addr 1
    (msg_create_tokens token_id_)
  ) [person_1; person_2; person_3].
(** Transfer initial token funds to CPMM contract *)
Definition transfer_cpmm_tokens := [
  build_call creator token_contract_base_addr 5 (msg_create_tokens token_id_);
  build_call creator token_contract_base_addr 0 (msg_transfer [{|
    from_ := creator;
    txs := [{|
      to_ := cpmm_contract_base_addr;
      dst_token_id := token_id_;
      amount := 500%N;
    |}];
    sender_callback_addr := None
  |}])
].
Definition setup_token_contract :=
  deploy_token ::
  setup_operators ++
  create_tokens ++
  transfer_cpmm_tokens.


Definition lqt_setup := {|
  admin_        := cpmm_contract_base_addr;
  lqt_provider  := null_address_;
  initial_pool  := initial_lqt
|}.
Definition deploy_lqt := [build_deploy creator 0 DEX2LQT.contract lqt_setup].


Definition cpmm_setup := {|
  lqtTotal_     := initial_lqt;
  manager_      := null_address_;
  tokenAddress_ := token_contract_base_addr;
  tokenId_      := token_id_
|}.
Definition deploy_cpmm := build_deploy creator 0 DEX2.contract cpmm_setup.
(** Transfer some tez to CPMM contract *)
Definition transfer_cpmm_xtz := TestUtils.build_transfer creator cpmm_contract_base_addr 5.
(** Connect CPMM and Lqt token contracts *)
Definition set_lqt_address := build_call creator cpmm_contract_base_addr 0
  (@FA2Token.other_msg _ DexterMsg (SetLqtAddress lqt_contract_base_addr)).
(** Sync token pool counter *)
Definition update_token_pool := build_call creator cpmm_contract_base_addr 0
  (@FA2Token.other_msg _ DexterMsg UpdateTokenPool).
Definition setup_cpmm_contract := [
  deploy_cpmm;
  transfer_cpmm_xtz;
  set_lqt_address;
  update_token_pool
].

Definition init_cb :=
   add_block empty_chain
    (transfer_initial_funds ++
    setup_token_contract ++
    deploy_lqt ++
    setup_cpmm_contract).
Definition init_cb' :=
  match init_cb with
  | Ok cb => cb
  | Err _ => empty_chain
  end.

Module NotationInfo <: TestNotationParameters.
  Definition gAction := gAction.
  Definition init_cb := init_cb'.
End NotationInfo.
Module TN := TestNotations NotationInfo. Import TN.
(* Sample (gChain). *)

(** * Tests *)
(** Dexter2 uses call to balance_of entrypoint on the token contract
    to sync the token reserves. It is key that there is no way for an
    attacker to manipulate the reserve by interfering with this sync.
    Therefore, we test in both execution orders that there will never be
    callbacks with someone else's balance / incorrect balance.
*)
Definition msg_is_balance_of_callback (cstate : Dexter2CPMM.State)
                                      (msg : Dexter2CPMM.Msg)
                                      : bool :=
  match msg with
  | FA2Token.receive_balance_of_param _ => true
  | _ => false
  end.

Definition callback_safe (env : Environment)
                         (cctx : ContractCallContext)
                         (old_state : Dexter2CPMM.State)
                         (msg : Dexter2CPMM.Msg)
                         (result_opt : option (Dexter2CPMM.State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), FA2Token.receive_balance_of_param responses) =>
    let length_correct := length responses =? 1 in
    let owner_correct :=
      match responses with
      | h :: t => address_eqb (h.(request).(owner)) cpmm_contract_base_addr
      | _ => true
      end in
    let amount_correct :=
      match responses with
      | h :: t => (old_state.(tokenPool) <=? h.(balance))%N
      | _ => true
      end in
    let is_updating := old_state.(selfIsUpdatingTokenPool) in
    (checker (
      length_correct &&
      owner_correct &&
      amount_correct &&
      is_updating
    ))
  | _ => checker false
  end.

(* Extract Constant DepthFirst => "false".
QuickChick ({{msg_is_balance_of_callback}} cpmm_contract_base_addr {{callback_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)

(* Extract Constant DepthFirst => "true".
QuickChick ({{msg_is_balance_of_callback}} cpmm_contract_base_addr {{callback_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(** Next we test that no Dexter operations can happen
    while token reserve is syncing.
    Again we test for both execution models.
*)
Definition is_syncing (state : Dexter2CPMM.State)
                      (msg : Dexter2CPMM.Msg)
                      : bool :=
  state.(selfIsUpdatingTokenPool).

Definition only_callbacks (env : Environment)
                          (cctx : ContractCallContext)
                          (old_state : Dexter2CPMM.State)
                          (msg : Dexter2CPMM.Msg)
                          (result_opt : option (Dexter2CPMM.State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some _, FA2Token.receive_balance_of_param _) => checker true
  | _ => checker false
  end.

(* Extract Constant DepthFirst => "false".
QuickChick ({{is_syncing}} cpmm_contract_base_addr {{only_callbacks}}). *)
(* +++ Passed 10000 tests (0 discards) *)

(* Extract Constant DepthFirst => "true".
QuickChick ({{is_syncing}} cpmm_contract_base_addr {{only_callbacks}}). *)
(* +++ Passed 10000 tests (0 discards) *)


(** Finally we test that the token reserve invariant holds.
    That is the actual token balance should always be less
    than the token reserve.
*)
Definition token_reserve_safe (cs : ChainState) :=
  match get_contract_state Dexter2CPMM.State cs cpmm_contract_base_addr with
  | Some dexter_state =>
    match get_contract_state FA2Token.State cs token_contract_base_addr with
    | Some token_state =>
      let token_reserve := dexter_state.(tokenPool) in
      let token_balance := address_balance dexter_state.(tokenId) cpmm_contract_base_addr token_state in
        checker (token_reserve <=? token_balance)%N
    | None => checker true
    end
  | None => checker true
  end.

(* Extract Constant DepthFirst => "false".
QuickChick (forAllBlocks token_reserve_safe). *)
(* +++ Passed 10000 tests (0 discards) *)

(* Extract Constant DepthFirst => "true".
QuickChick (forAllBlocks token_reserve_safe). *)
(* +++ Passed 10000 tests (0 discards) *)
