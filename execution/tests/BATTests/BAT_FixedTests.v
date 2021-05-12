Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import Containers.
From ConCert Require Import BAT_Fixed.
From ConCert Require Import ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters BAT_FixedPrinters BAT_FixedGens TraceGens.

From Coq Require Import List.
Import ListNotations.
Import BoundedN.Stdpp.
Import LocalBlockchain.

(* -------------------------- Tests of the BAT_Fixed Implementation -------------------------- *)

Existing Instance BAT_FixedPrinters.showBATState.
Existing Instance BAT_FixedPrinters.showMsg.

Definition ethFund : Address := BoundedN.of_Z_const AddrSize 16%Z.
Definition batFund : Address := BoundedN.of_Z_const AddrSize 17%Z.

Definition bat_setup := BAT_Fixed.build_setup (20%N) ethFund batFund 1 5 (3%N) (101%N) (90%N).
Definition deploy_bat := create_deployment 0 BAT_Fixed.contract bat_setup.

Let contract_base_addr := BoundedN.of_Z_const AddrSize 128%Z.

(* In the initial chain we transfer some assets to a few accounts, just to make the addresses
   present in the chain state. The amount transferred is irrelevant. *)
Definition token_cb :=
  ResultMonad.unpack_result (TraceGens.add_block (lcb_initial AddrSize)
  [
    build_act creator (Blockchain.act_transfer person_1 10);
    build_act creator (Blockchain.act_transfer person_2 7);
    build_act creator (Blockchain.act_transfer person_3 6);
    build_act creator (Blockchain.act_transfer person_4 10);
    build_act creator deploy_bat
  ]).

Module TestInfo <: BATGensInfo.
  Definition contract_addr := contract_base_addr.
  Definition accounts := [batFund; ethFund; person_1; person_2; person_3; person_4; person_5].
  Definition gAccount (c : Chain) := elems [batFund; ethFund; person_1; person_2; person_3; person_4; person_5].
  Definition bat_addr := batFund.
  Definition fund_addr := ethFund.
End TestInfo.
Module MG := BATGens TestInfo. Import MG.

(* chain generator *)
Definition gTokenChain max_acts_per_block token_cb max_length :=
  let act_depth := 1 in
  gChain_full_sized token_cb
    (fun env act_depth => gBATAction env) max_length act_depth max_acts_per_block.

(* Checker for debugging Action generator *)
Definition chainDebug max_acts_per_block token_cb max_length g :=
  let act_depth := 1 in
  debug_gChain token_cb
    (fun env act_depth => g env) max_length act_depth max_acts_per_block.

Definition forAllTokenChainBuilders n :=
  let max_acts_per_block := 2 in
  forAllChainBuilder n token_cb (gTokenChain max_acts_per_block).

Definition pre_post_assertion_token P c Q :=
  let max_acts_per_block := 2 in
  let trace_length := 7 in
  pre_post_assertion trace_length token_cb (gTokenChain max_acts_per_block) BAT_Fixed.contract c P Q.

Notation "{{ P }} c {{ Q }}" := (pre_post_assertion_token P c Q) ( at level 50).
Notation "cb '~~>' pf" := (reachableFrom_chaintrace cb (gTokenChain 2) pf) (at level 45, no associativity).
Notation "'{' lc '~~~>' pf1 '===>' pf2 '}'" :=
  (reachableFrom_implies_chaintracePropSized 10 lc (gTokenChain 2) pf1 pf2) (at level 90, left associativity).



(* Test generators *)

(* Sample generator to see quality of generated chains *)
(* Sample (gTokenChain 2 token_cb 7). *)

(* Verify that gBATActionValid only produces valid actions *)
(* QuickChick (chainDebug 1 token_cb 7 gBATActionValid). *)
(* +++ Passed 10000 tests (0 discards) *)

(* Get value of isFinalized in last state of a chain *)
Definition get_chain_finalized (cb : ChainBuilder) : bool :=
  match get_contract_state BAT_Fixed.State cb.(builder_env) contract_base_addr with
  | Some state => state.(isFinalized)
  | None => true
  end.

(* Verify hardness of finalizing BAToken.
   Goal is ~ 2/3 of generated chains are finalized *)
(* QuickChick (forAllTokenChainBuilders 8 (fun cb => collect (get_chain_finalized cb) true)). *)
(*
  6693 : true
  3307 : false
  +++ Passed 10000 tests (0 discards)
*)

(* Check if an action is finalize *)
Definition action_is_finalize (action : Action) : bool :=
  match action.(act_body) with
  | act_transfer _ _ => false
  | act_deploy _ _ _ => false
  | act_call to _ msg =>
    if (address_eqb to contract_base_addr)
    then
      match @deserialize BAT_Fixed.Msg _ msg with
      | Some finalize => true
      | Some _ => false
      | None => false
      end
    else
      false
  end.

(* Check if an action is refund *)
Definition action_is_refund (action : Action) : bool :=
  match action.(act_body) with
  | act_transfer _ _ => false
  | act_deploy _ _ _ => false
  | act_call to _ msg =>
    if (address_eqb to contract_base_addr)
    then
      match @deserialize BAT_Fixed.Msg _ msg with
      | Some refund => true
      | Some _ => false
      | None => false
      end
    else
      false
  end.

(* Get last state before finalize/refund in a chain *)
Fixpoint get_last_funding_state {from to} (trace : ChainTrace from to) (default : ChainState) : ChainState :=
  match trace with
  | ChainedList.snoc trace' (Blockchain.step_action _ _ act _ _ _ _ _ as step) =>
    if action_is_finalize act
    then
      fst (chainstep_states step)
    else
      if action_is_refund act
      then
        get_last_funding_state trace' (fst (chainstep_states step))
      else
        get_last_funding_state trace' default
  | ChainedList.snoc trace' _ => get_last_funding_state trace' default
  | ChainedList.clnil => default
  end.

(* Get the number of tokens in last state before finalize/refund in a chain *)
Definition get_chain_tokens (cb : ChainBuilder) : TokenValue :=
  let cs := get_last_funding_state cb.(builder_trace) empty_state in
  match get_contract_state BAT_Fixed.State cs contract_base_addr with
  | Some state => (total_supply state)
  | None => 0%N
  end.

(* Verify spread of tokens after funding period is over.
   We do this to see it it possible to hit the funding cap. *)
(* QuickChick (forAllTokenChainBuilders 6 (fun cb => collect (get_chain_tokens cb) true)). *)
(*
  3290 : 101
  1522 : 98
  1194 : 95
  968 : 92
  855 : 89
  643 : 86
  490 : 83
  354 : 80
  247 : 77
  175 : 74
  111 : 71
  79 : 68
  32 : 65
  15 : 62
  12 : 59
  6 : 0
  5 : 56
  1 : 53
  1 : 47
  +++ Passed 10000 tests (0 discards)
*)



Local Open Scope N_scope.

Definition msg_is_transfer_and_finalized (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer _ _) => cstate.(isFinalized)
  | _ => false
  end.

Definition transfer_balance_update_correct old_state new_state from to tokens :=
  let get_balance addr state := with_default 0 (FMap.find addr (balances state)) in
  let from_balance_before := get_balance from old_state in
  let to_balance_before := get_balance to old_state in
  let from_balance_after := get_balance from new_state in
  let to_balance_after := get_balance to new_state in
  (* if the transfer is a self-transfer, balances should remain unchained *)
  if address_eqb from to
  then
    (from_balance_before =? from_balance_after) &&
    (to_balance_before =? to_balance_after)
  else
    (from_balance_before =? from_balance_after + tokens) &&
    (to_balance_before + tokens =? to_balance_after).

Definition post_transfer_correct cctx old_state msg (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer to tokens)) =>
    let from := cctx.(ctx_from) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (transfer_balance_update_correct old_state new_state from to tokens))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.

(* Check that old EIP20 test works on BAT *)
(* QuickChick (
  {{msg_is_transfer_and_finalized}}
  contract_base_addr
  {{post_transfer_correct}}
). *)

(* +++ Passed 10000 tests (0 discards) *)

Definition msg_is_refund (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | refund => true
  | _ => false
  end.

Definition refund_correct old_state new_state cctx to (amount : Amount) :=
  let from := cctx.(ctx_from) in
  let from_bal_old := with_default 0 (FMap.find from (balances old_state)) in
  let from_bal_new := with_default 0 (FMap.find from (balances new_state)) in
  let eth_to_refund := Z.of_N (from_bal_old / (tokenExchangeRate old_state)) in
  let contract_bal := (ctx_contract_balance cctx) in
    (address_eqb from to) &&
    (from_bal_new =? 0) &&
    (amount =? eth_to_refund)%Z &&
    (eth_to_refund <=? contract_bal)%Z.

Definition post_refund_correct cctx old_state (msg : BAT_Fixed.Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, [Blockchain.act_transfer to amount]), refund) =>
    whenFail (show cctx ++ nl ++ show old_state ++ nl ++ show result_opt)
    (checker (refund_correct old_state new_state cctx to amount))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.

(* User that funded BAT can always refund if funding fails *)
(* QuickChick (
  {{msg_is_refund}}
  contract_base_addr
  {{post_refund_correct}}
). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition is_finalized :=
  fun cs => 
    match get_contract_state State cs contract_base_addr with
    | Some state => state.(isFinalized)
    | None => false
    end.

(* Check that it is possible to finalize *)
(* QuickChick (token_cb ~~> is_finalized). *)
(*
Chain{|
Block 1 [
Action{act_from: 10%256, act_body: (act_transfer 11%256, 10)};
Action{act_from: 10%256, act_body: (act_transfer 12%256, 7)};
Action{act_from: 10%256, act_body: (act_transfer 13%256, 6)};
Action{act_from: 10%256, act_body: (act_transfer 14%256, 10)};
Action{act_from: 10%256, act_body: (act_deploy 0, transfer 19%256 17)}];
Block 2 [
Action{act_from: 13%256, act_body: (act_call 128%256, 5, create_tokens)};
Action{act_from: 14%256, act_body: (act_call 128%256, 10, create_tokens)}];
Block 3 [
Action{act_from: 13%256, act_body: (act_call 128%256, 1, create_tokens)}];
Block 4 [
Action{act_from: 16%256, act_body: (act_call 128%256, 0, finalize)}];
Block 5 [
Action{act_from: 17%256, act_body: (act_call 128%256, 0, approve 13%256 7)};
Action{act_from: 13%256, act_body: (act_call 128%256, 0, approve 17%256 13)}];
Block 6 [
Action{act_from: 13%256, act_body: (act_call 128%256, 0, transfer 15%256 8)};
Action{act_from: 14%256, act_body: (act_call 128%256, 0, approve 17%256 11)}];|}

Success - found witness satisfying the predicate!
+++ Failed (as expected) after 6 tests and 0 shrinks. (0 discards)
*)

Definition final_is_final :=
  {token_cb ~~~> (fun cs => if (is_finalized cs) then Some true else None) ===> 
    (fun _ _ post_trace => checker (fold_left (fun a (chainState : ChainState) => a && (is_finalized chainState) ) post_trace true))}.

(* Check that once finalized it cannot be undone *)
(* QuickChick final_is_final. *)
(* +++ Passed 10000 tests (7 discards) *)







