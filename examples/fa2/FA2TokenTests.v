From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2LegacyInterface.
From ConCert.Examples.FA2 Require Import TestContracts.
From ConCert.Utils Require Import Extras.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

(** Example policies *)

(* The policy which allows only token owners to transfer their own tokens. *)
Definition policy_self_only : permissions_descriptor := {|
  descr_self := self_transfer_permitted;
  descr_operator := operator_transfer_denied;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* The policy which allows only operators to transfer tokens. *)
Definition policy_operators_only : permissions_descriptor := {|
  descr_self := self_transfer_denied;
  descr_operator := operator_transfer_permitted;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* Non-transferable token (neither token owner, nor operators can transfer tokens. *)
Definition policy_no_transfers : permissions_descriptor := {|
  descr_self := self_transfer_denied;
  descr_operator := operator_transfer_denied;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* The policy which allows both owners and operators to transfer tokens. *)
Definition policy_all : permissions_descriptor := {|
  descr_self := self_transfer_permitted;
  descr_operator := operator_transfer_permitted;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

Definition token_metadata_0 : token_metadata := {|
  metadata_token_id := 0%N;
  metadata_decimals := 8%N;
|}.

(* Contract setups and deployments *)

Definition token_setup (hook_addr : option Address): FA2Token.Setup := {|
  setup_total_supply := [];
  setup_tokens := FMap.add 0%N token_metadata_0 FMap.empty;
  initial_permission_policy := policy_all;
  transfer_hook_addr_ := hook_addr;
|}.

Definition token_contract_base_addr : Address := addr_of_Z 128.
Definition fa2hook_setup : HookSetup := {|
  hook_fa2_caddr_ := token_contract_base_addr;
  hook_policy_ := policy_self_only;
|}.

Definition fa2hook_contract_addr : Address := addr_of_Z 130.
Definition token_client_setup := build_clientsetup token_contract_base_addr.
Definition client_contract_addr : Address := addr_of_Z 129.

Definition chain_with_token_deployed_with_hook : ChainBuilder :=
  unpack_result (TraceGens.add_block empty_chain
  [
    TestUtils.build_transfer creator person_1 10;
    TestUtils.build_transfer creator person_2 10;
    TestUtils.build_transfer creator person_3 10;
    build_deploy creator 0 FA2Token.contract (token_setup (Some fa2hook_contract_addr));
    build_deploy creator 0 client_contract token_client_setup;
    build_deploy creator 0 hook_contract fa2hook_setup
  ]).

Definition chain_with_token_deployed_without_hook : ChainBuilder :=
  unpack_result (TraceGens.add_block empty_chain
  [
    TestUtils.build_transfer creator person_1 10;
    TestUtils.build_transfer creator person_2 10;
    TestUtils.build_transfer creator person_3 10;
    build_deploy creator 0 FA2Token.contract (token_setup None);
    build_deploy creator 0 client_contract token_client_setup
  ]).

Definition chain_without_transfer_hook' : result ChainBuilder AddBlockError :=
  (TraceGens.add_block chain_with_token_deployed_without_hook
  [
    build_call person_1 token_contract_base_addr 10%Z (msg_create_tokens 0%N) ;
    build_call person_2 token_contract_base_addr 10%Z (msg_create_tokens 0%N)
  ]).

Definition chain_with_transfer_hook' : result ChainBuilder AddBlockError :=
  (TraceGens.add_block chain_with_token_deployed_with_hook
  [
    build_call person_1 token_contract_base_addr 10%Z (msg_create_tokens 0%N) ;
    build_call person_2 token_contract_base_addr 10%Z (msg_create_tokens 0%N)
  ]).

Definition chain_without_transfer_hook := unpack_result chain_without_transfer_hook'.
Definition chain_with_transfer_hook := unpack_result chain_with_transfer_hook'.


Definition client_other_msg := @other_msg _ FA2ClientMsg.

Definition call_client_is_op_act :=
  let params := Build_is_operator_param
      (Build_operator_param zero_address zero_address all_tokens)
      (Build_callback is_operator_response None client_contract_addr) in
  let msg := client_other_msg (Call_fa2_is_operator params) in
  act_call client_contract_addr 0%Z (serialize msg).

Definition token_state (cs : Environment) := get_contract_state FA2Token.State cs token_contract_base_addr.
Definition client_state (cs : Environment) := get_contract_state ClientState cs client_contract_addr.

From ConCert.Examples.FA2 Require Import FA2Gens.
From ConCert.Examples.FA2 Require Export FA2Printers.

Module TestInfo <: FA2TestsInfo.
  Import Monads.
  Import MonadNotation. Open Scope monad_scope.

  Definition fa2_contract_addr := token_contract_base_addr.
  Definition fa2_client_addr := client_contract_addr.
  Definition fa2_hook_addr := fa2hook_contract_addr.
  Definition accounts := test_chain_addrs_5.
End TestInfo.
Module MG := FA2Gens.FA2Gens TestInfo. Import MG.

Module NotationInfo <: TestNotationParameters.
  Definition gAction := gFA2TokenAction.
  Definition init_cb := chain_with_transfer_hook.
End NotationInfo.
Module TN := TestNotations NotationInfo. Import TN.
Extract Constant max_acts_per_block => "1".
(* Sample gChain. *)

Local Open Scope Z_scope.
Definition transfer_state_update_correct prev_state next_state transfers :=
  let balance_diffs_map : FMap (Address * token_id) Z := fold_left (fun current_diff_map trx =>
    let from := trx.(from_) in
    let iter := (fun diff_map trx_dst =>
      (* subtract amount from sender *)
      let m1 :=
        let amount := Z.of_N (trx_dst.(amount)) in
        let from_key := (from, trx_dst.(dst_token_id)) in
        match FMap.find from_key current_diff_map with
        | Some current_diff => FMap.add from_key (current_diff - amount) current_diff_map
        | None => FMap.add from_key (-amount) current_diff_map
        end in
      (* add amount to receiver *)
      let m2 :=
        let amount := Z.of_N (trx_dst.(amount)) in
        let to_key := (trx_dst.(to_), trx_dst.(dst_token_id)) in
        match FMap.find to_key m1 with
        | Some current_diff => FMap.add to_key (current_diff + amount) m1
        | None => FMap.add to_key amount m1
        end in
      m2) in
      fold_left iter trx.(txs) current_diff_map
  ) transfers FMap.empty in
  let balance_update_correct p balance_diff :=
    let addr := fst p in
    let tokenid := snd p in
    let balance_before := Z.of_N (address_balance tokenid addr prev_state) in
    let balance_after := Z.of_N (address_balance tokenid addr next_state) in
    (* check that balance_diff is equal to the difference in recorded balance *)
    whenFail (
      "Failed predicate with owner: " ++ show addr ++ nl ++
      "Expected new balance: " ++ show balance_after ++ nl ++
      "But got: " ++ show balance_before ++ " + " ++
        show balance_diff ++ " = " ++ show (balance_before + balance_diff)
      )
    ((balance_before + balance_diff) =? balance_after) in
  forEachMapEntry balance_diffs_map balance_update_correct.
Local Close Scope Z_scope.

Definition msg_is_transfer (cstate : FA2Token.State)
                           (msg : FA2Token.Msg) :=
  match msg with
  | msg_transfer _ => true
  | _ => false
  end.

Definition post_transfer_correct (chain : Chain)
                                 (cctx : ContractCallContext)
                                 old_state
                                 msg
                                 (result_opt : option (FA2Token.State * list ActionBody)) :=
  match result_opt with
  | Some (new_state, _) =>
    let transfers :=
      match msg with
      | msg_transfer transfers => transfers
      | _ => []
      end in
    checker (transfer_state_update_correct old_state new_state transfers)
  | None => checker false
  end.

(* QuickChick (
  {{ msg_is_transfer }}
    token_contract_base_addr
  {{ post_transfer_correct }}
  chain_without_transfer_hook). *)
(* 14 seconds, max size 7, 1 act per block *)
(* +++ Passed 10000 tests (0 discards) *)

Definition get_transfer_from_act (act : Action)
                                 : option (list transfer) :=
  match act.(act_body) with
    | act_call _ _ msg =>
      match deserialize FA2Token.Msg _ msg with
      | Some (msg_transfer transfers) => Some transfers
      | _ => None
      end
    | _ => None
  end.

(* get the queued transfer actions in the old state, and check that the succeeding state
   has updated the balances correctly.
   Assumes that there is at most one transfer action per block *)
Definition transfer_balances_correct (old_cs new_cs : ChainState) :=
  let get_transfer_transfers (msgs : list Action) := fold_left (fun acc act =>
    if isSome acc
    then acc
    else match get_transfer_from_act act with
         | Some trxs => Some trxs
         | _ => acc
         end
  ) msgs None in
  match get_transfer_transfers old_cs.(chain_state_queue) with
  | Some transfers =>
     (* check that new_cs is updated correctly from old_cs according to the transfers *)
     let prev_state := token_state old_cs in
     let next_state := token_state new_cs in
     match (prev_state, next_state) with
     | (Some prev_state, Some next_state) =>
       whenFail (show prev_state ++ nl ++ show next_state)
       (checker (transfer_state_update_correct prev_state next_state transfers))
     | _ => checker false
     end
  | None => checker true
  end.

(* QuickChick (forAllChainStatePairs transfer_balances_correct). *)
(* +++ Passed 10000 tests (0 discards) *)


Definition get_transfers (acts : list Action)
                         : list (Address * list FA2LegacyInterface.transfer) :=
  fold_left (fun trxs act =>
    match act.(act_body) with
    | act_call _ _ msg =>
      match deserialize FA2Token.Msg _ msg with
      | Some (msg_transfer transfers) => (act.(act_from), transfers) :: trxs
      | _ => trxs
      end
    | _ => trxs
    end) acts [].

Definition transfer_satisfies_policy sender trx state : Checker :=
  (* check if sender is an operator, and permission to transfer the specified token_id *)
  let policy := state.(permission_policy) in
  let is_valid_operator_transfer : Checker :=
    match FMap.find trx.(from_) state.(operators) with
    | Some ops_map =>
      match FMap.find sender ops_map with
      | Some all_tokens => checker true
      | Some (some_tokens token_ids) =>
        whenFail "operator didn't have sufficient token_id permissions"
        (checker (fold_right ((fun (tx_dst : transfer_destination) (acc: bool) =>
            if acc then (existsb (N.eqb (tx_dst.(dst_token_id))) token_ids) else false
        )) true trx.(txs)))
      | None => checker false
      end
    | None => checker false
    end in
  whenFail
  ("failed with sender: " ++ show sender ++ nl)
  match (policy.(descr_self), policy.(descr_operator)) with
  (* no transfers allowed *)
  | (self_transfer_denied, operator_transfer_denied) => checker false
  (* only self transfer allowed - check sender is equal to 'from' *)
  | (self_transfer_permitted, operator_transfer_denied) =>
    whenFail "operator transfer was denied, but sender != from"
    (* Note: this case seems to not be hit during testing *)
    (address_eqb sender trx.(from_))
  | (self_transfer_denied, operator_transfer_permitted) =>
    if address_eqb sender trx.(from_)
    then whenFail "self transfer was denied but got transfer with sender = from" false
    else
      (* Note: this case seems to not be hit during testing *)
      is_valid_operator_transfer
  | (self_transfer_permitted, operator_transfer_permitted) =>
    if address_eqb sender trx.(from_)
    then checker true
    else
      (* Note: this case seems to not be hit during testing *)
      is_valid_operator_transfer
  end.

Definition transfer_satisfies_policy_P (old_cs new_cs : ChainState) : Checker :=
  let acts := old_cs.(chain_state_queue) in
  let transfers := get_transfers acts in
  match token_state new_cs with
  | Some state =>
      conjoin_map (fun sender_trxs_pair =>
        conjoin_map (fun trx =>
          transfer_satisfies_policy (fst sender_trxs_pair) trx state
          ) (snd sender_trxs_pair)
      ) transfers
  | None => checker false
  end.

(* QuickChick (forAllChainStatePairs transfer_satisfies_policy_P). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition single_update_op_correct (new_state : FA2Token.State) (op : update_operator) :=
  let (param, is_remove) := match op with
    | add_operator param => (param, false)
    | remove_operator param => (param, true)
    end in
  match FMap.find param.(op_param_owner) new_state.(operators) with
  | Some owners_map => if is_remove
                       then true
                       else isSome (FMap.find param.(op_param_operator) owners_map)
  | None => is_remove
  end.

(* This property asserts that if an update_operator action contains multiple updates for the same operator,
   the LAST operation in the list must take effect *)
Definition last_update_operator_occurrence_takes_effect (update_ops : list update_operator)
                                                        (new_state : FA2Token.State) :=
  let last_ops : FMap (Address * Address) update_operator :=
    fold_left (fun acc update_op =>
    let param := match update_op with
      | add_operator param => param
      | remove_operator param => param
      end in
      FMap.add (param.(op_param_owner), param.(op_param_operator)) update_op acc
  ) update_ops FMap.empty in
  whenFail (
    show last_ops ++ nl ++
    show new_state
  )
  (forallb (fun p => single_update_op_correct new_state (snd p)) (FMap.elements last_ops)).

Definition msg_is_update_operator (cstate : FA2Token.State) (msg : FA2Token.Msg) :=
  match msg with
  | msg_update_operators _ => true
  | _ => false
  end.

Definition post_last_update_operator_occurrence_takes_effect (chain : Chain)
                                                             (cctx : ContractCallContext)
                                                             (old_state : FA2Token.State)
                                                             msg
                                                             (result_opt : option (FA2Token.State * list ActionBody)) :=
  match result_opt with
  | Some (new_state, _) =>
    let update_ops :=
      match msg with
      | msg_update_operators ops => ops
      | _ => []
      end in
    last_update_operator_occurrence_takes_effect update_ops new_state
  | None => checker false
  end.

(* QuickChick (
  {{msg_is_update_operator}}
  token_contract_base_addr
  {{post_last_update_operator_occurrence_takes_effect}}
  chain_without_transfer_hook
). *)
(* 40 secs, max length 7: *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)
