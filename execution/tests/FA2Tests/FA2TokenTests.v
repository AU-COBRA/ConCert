From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface.
From ConCert Require Import Serializable.
From ConCert Require Import Extras.
From ConCert Require Import Containers.
From ConCert Require Import BoundedN.
Global Set Warnings "-extraction-logical-axiom".
Require Import ZArith Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters TraceGens FA2Printers TestContracts.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Import ListNotations.
Import RecordSetNotations.
(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
Close Scope address_scope.
(* Notation "f 'o' g" := (compose f g) (at level 50). *)

Definition LocalChainBase : ChainBase := TestUtils.LocalChainBase.

(** example policies *)

(* the policy which allows only token owners to transfer their own tokens. *)
Definition policy_self_only : permissions_descriptor := {|
  descr_self := self_transfer_permitted;
  descr_operator := operator_transfer_denied;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* the policy which allows only operators to transfer tokens. *)
Definition policy_operators_only : permissions_descriptor := {|
  descr_self := self_transfer_denied;
  descr_operator := operator_transfer_permitted;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* non-transferable token (neither token owner, nor operators can transfer tokens. *)
Definition policy_no_transfers : permissions_descriptor := {|
  descr_self := self_transfer_denied;
  descr_operator := operator_transfer_denied;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* the policy which allows both owners and operators to transfer tokens. *)
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

Definition token_contract_base_addr : Address := BoundedN.of_Z_const AddrSize 128%Z.
Definition fa2hook_setup : HookSetup := {|
  hook_fa2_caddr_ := token_contract_base_addr;
  hook_policy_ := policy_self_only;
|}.
Definition deploy_fa2hook := create_deployment 0 hook_contract fa2hook_setup.
Definition fa2hook_contract_addr : Address := BoundedN.of_Z_const AddrSize 130%Z.

Definition deploy_fa2token_with_transfer_hook : @ActionBody LocalChainBase :=
  create_deployment 0 FA2Token.contract (token_setup (Some fa2hook_contract_addr)) .
Definition deploy_fa2token_without_transfer_hook : @ActionBody LocalChainBase :=
  create_deployment 0 FA2Token.contract (token_setup None).

Definition token_client_setup := build_clientsetup token_contract_base_addr.
Definition deploy_fa2token_client : @ActionBody LocalChainBase := create_deployment 0 client_contract token_client_setup.
Definition client_contract_addr : Address := BoundedN.of_Z_const AddrSize 129%Z.



Definition chain_with_token_deployed_with_hook : LocalChain :=
  unpack_option (my_add_block lc_initial
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_fa2token_with_transfer_hook;
    build_act creator deploy_fa2token_client;
    build_act creator deploy_fa2hook
  ]).

Definition chain_with_token_deployed_without_hook : LocalChain :=
  unpack_option (my_add_block lc_initial
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_fa2token_without_transfer_hook;
    build_act creator deploy_fa2token_client
  ]).

Definition client_other_msg := @other_msg _ FA2ClientMsg _.

Definition call_client_is_op_act :=
  let params := Build_is_operator_param
      (Build_operator_param zero_address zero_address all_tokens)
      (Build_callback is_operator_response None) in
  let msg := client_other_msg (Call_fa2_is_operator params) in
  act_call client_contract_addr 0%Z (serialize ClientMsg _ msg).

Definition chain_with_transfer_hook :=
  unpack_option (my_add_block chain_with_token_deployed_with_hook
  [
    build_act person_1 (act_call token_contract_base_addr 10%Z (serialize _ _ (msg_create_tokens 0%N))) ;
    build_act person_2 (act_call token_contract_base_addr 10%Z (serialize _ _ (msg_create_tokens 0%N)))
  ]).

Definition chain_without_transfer_hook :=
  unpack_option (my_add_block chain_with_token_deployed_without_hook
  [
    build_act person_1 (act_call token_contract_base_addr 10%Z (serialize _ _ (msg_create_tokens 0%N))) ;
    build_act person_2 (act_call token_contract_base_addr 10%Z (serialize _ _ (msg_create_tokens 0%N)))
  ]).

Definition client_state lc :=
  match (FMap.find client_contract_addr lc.(lc_contract_state)) with
  | Some state => deserialize ClientState _ state
  | None => None
  end.
Definition token_state lc :=
  match (FMap.find token_contract_base_addr lc.(lc_contract_state)) with
  | Some state => deserialize FA2Token.State _ state
  | None => None
  end.


From ConCert.Execution.QCTests Require Import FA2Gens.

Module TestInfo <: FA2TestsInfo.
  Definition fa2_contract_addr := token_contract_base_addr.
  Definition fa2_client_addr := client_contract_addr.
  Definition fa2_hook_addr := fa2hook_contract_addr.
End TestInfo.
Module MG := FA2Gens.FA2Gens TestInfo. Import MG.

Definition chain_with_transfer_hook_token_state : FA2Token.State := unpack_option (token_state chain_with_transfer_hook).
(* Compute (show chain_with_transfer_hook_token_state). *)
Definition gFA2TokenActionChainTraceList max_acts_per_block lc length :=
  gLocalChainTraceList_fix lc (fun lc _ => gFA2TokenAction lc) length max_acts_per_block.
Definition gFA2ClientChainTraceList max_acts_per_block lc length :=
  gLocalChainTraceList_fix lc (fun lc _ => gClientAction lc) length max_acts_per_block.

(* Sample (gFA2TokenAction chain_with_transfer_hook). *)
(* Sample (gFA2TokenActionChainTraceList 1 chain_with_transfer_hook 10). *)

Definition forAllFA2Traces chain n := forAllTraces_stepProp n chain (gFA2TokenActionChainTraceList 1).
Notation "{{ P }} c {{ Q }} chain" := (pre_post_assertion 7 chain (gFA2ChainTraceList 1) c P Q)( at level 50).

Extract Constant defNumDiscards => "(10 * defNumTests)".

Local Open Scope Z_scope.
Definition transfer_state_update_correct prev_state next_state transfers :=
  let balance_diffs_map : FMap (Address * token_id) Z := fold_left (fun current_diff_map trx =>
    (* subtract amount from sender *)
    let m1 :=
      let amount := Z.of_N (trx.(amount)) in
      let from_key := (trx.(from_), trx.(transfer_token_id)) in
      match FMap.find from_key current_diff_map with
      | Some current_diff => FMap.add from_key (current_diff - amount) current_diff_map
      | None => FMap.add from_key (-amount) current_diff_map
      end in
    (* add amount to receiver *)
    let m2 :=
      let amount := Z.of_N (trx.(amount)) in
      let to_key := (trx.(to_), trx.(transfer_token_id)) in
      match FMap.find to_key m1 with
      | Some current_diff => FMap.add to_key (current_diff + amount) m1
      | None => FMap.add to_key amount m1
      end in
    m2
  ) transfers FMap.empty in
  let balance_update_correct p balance_diff :=
    let addr := fst p in
    let tokenid := snd p in
    let balance_before := Z.of_N (address_balance tokenid addr prev_state) in
    let balance_after := Z.of_N (address_balance tokenid addr next_state) in
    (* check that balance_diff is equal to the difference in recorded balance *)
    (balance_before + balance_diff) =? balance_after in
  forEachMapEntry balance_diffs_map balance_update_correct.
Local Close Scope Z_scope.

Definition msg_is_transfer (cstate : FA2Token.State) (msg : FA2Token.Msg) :=
  match msg with
  | msg_transfer _ => true
  | _ => false
  end.

Definition post_transfer_correct (cctx : ContractCallContext) old_state msg (result_opt : option (FA2Token.State * list ActionBody)) :=
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
    FA2Token.contract
  {{ post_transfer_correct }}
  chain_without_transfer_hook). *)
(* 14 seconds, max size 7, 1 act per block *)
(* coqtop-stdout:+++ Passed 10000 tests (12283 discards) *)

Definition transfer_balances_correct (step : @LocalChainStep AddrSize) :=
  match step with
  | step_add_block _ _ _ => false ==> true
  | step_action prev_lc _ next_lc [act] =>
    match act.(act_body) with
    | act_call _ _ msg =>
      match deserialize FA2Token.Msg _ msg with
      | Some (msg_transfer transfers) =>
        (* check that next_lc is updated correctly from prev_lc according to the transfers *)
        let prev_state := token_state prev_lc in
        let next_state := token_state next_lc in
        match (prev_state, next_state) with
        | (Some prev_state, Some next_state) =>
          whenFail (show prev_state ++ nl ++ show next_state)
          (checker (transfer_state_update_correct prev_state next_state transfers))
        | _ => false ==> true
        end
      | _ => false ==> true
      end
    | _ => false ==> true
    end
  | _ => false ==> true
  end.

(* QuickChick (forAllFA2Traces chain_with_transfer_hook 1 transfer_balances_correct). *)


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
        (checker (existsb (N.eqb trx.(transfer_token_id)) token_ids))
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
      (address_eqb sender trx.(from_))
    | (self_transfer_denied, operator_transfer_permitted) =>
      if address_eqb sender trx.(from_)
      then whenFail "self transfer was denied but got transfer with sender = from" false
      else is_valid_operator_transfer
    | (self_transfer_permitted, operator_transfer_permitted) =>
    if address_eqb sender trx.(from_)
    then checker true
    else is_valid_operator_transfer
  end.

Definition get_transfers (acts : list Action) : list (Address * list FA2Interface.transfer) :=
  fold_left (fun trxs act =>
    match act.(act_body) with
    | act_call _ _ msg =>
      match deserialize FA2Token.Msg _ msg with
      | Some (msg_transfer transfers) => (act.(act_from), transfers) :: trxs
      | _ => trxs
      end
    | _ => trxs
    end) acts [].

Definition transfer_satisfies_policy_P (step : @LocalChainStep AddrSize) : Checker :=
  let acts := acts_of_lcstep step in
  let lc := prev_lc_of_lcstep step in
  let transfers := get_transfers acts in
  match token_state lc with
  | Some state =>
      conjoin_map (fun sender_trxs_pair =>
        conjoin_map (fun trx =>
          transfer_satisfies_policy (fst sender_trxs_pair) trx state
          ) (snd sender_trxs_pair)
      ) transfers
  | None => checker false
  end.

Definition showStateWhenFail (step : @LocalChainStep AddrSize) :=
  let prev_lc := prev_lc_of_lcstep step in
  let next_lc := next_lc_of_lcstep step in
  whenFail
  ("Failed on step: " ++ nl ++ show step ++ nl ++
  match (token_state prev_lc, token_state next_lc) with
  | (Some prev_state, Some next_state) =>
    "state before execution: " ++ nl ++ show prev_state ++ nl ++
    "state after execution: " ++ nl ++ show next_state ++ nl
  | (Some prev_state, None) =>
    "state before execution: " ++ nl ++ show prev_state ++ nl
  | _ => ""
  end).

(* QuickChick (forAllFA2Traces chain_with_transfer_hook 7 transfer_satisfies_policy_P). *)
(* coqtop-stdout:+++ Passed 10000 tests (2432 discards) *)


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

Definition post_last_update_operator_occurrence_takes_effect (cctx : ContractCallContext)
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
  FA2Token.contract
  {{post_last_update_operator_occurrence_takes_effect}}
  (gFA2ChainTraceList 1)
). *)
(* 40 secs, max length 7: *)
(* coqtop-stdout:+++ Passed 10000 tests (65772 discards) *)

(* Sanity check that generating two actions in a row will always succeed *)
(* QuickChick (
  forAll2 (gFA2TokenAction chain_with_token_deployed)
  (fun act_opt =>
  match act_opt with
  | Some act =>
    match (my_add_block chain_with_token_deployed [act]) with
    | Some c => gFA2TokenAction c
    | None => returnGen None
    end
  | None => returnGen None
  end)
  (fun act1_opt act2_opt =>
    match (act1_opt, act2_opt) with
    | (Some act1, Some act2) =>
      whenFail
        ("execution failed:" ++ nl
        ++ show (my_add_block chain_with_token_deployed [act1]))
        (
          let c_opt := my_add_block chain_with_token_deployed [act1] in
          match c_opt with
          | Some c => checker (isSome (my_add_block c [act2]))
          | None => whenFail "empty chain" false
          end
        )
    | _ => whenFail "empty act" false
    end)
). *)
