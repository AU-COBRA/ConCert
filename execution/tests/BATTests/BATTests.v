Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import Containers.
From ConCert Require Import BAT.
From ConCert Require Import ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters BATPrinters BATGens TraceGens.

From Coq Require Import List.
Import ListNotations.
Import BoundedN.Stdpp.
Import LocalBlockchain.

(* -------------------------- Tests of the BAT Implementation -------------------------- *)

Existing Instance showBATState.

Definition ethFund : Address := BoundedN.of_Z_const AddrSize 16%Z.
Definition batFund : Address := BoundedN.of_Z_const AddrSize 17%Z.

Definition bat_setup := BAT.build_setup (20%N) ethFund batFund 0 5 (3%N) (101%N) (63%N).
Definition deploy_bat := create_deployment 0 BAT.contract bat_setup.

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
  pre_post_assertion trace_length token_cb (gTokenChain max_acts_per_block) BAT.contract c P Q.

Notation "{{ P }} c {{ Q }}" := (pre_post_assertion_token P c Q) ( at level 50).
Notation "cb '~~>' pf" := (reachableFrom_chaintrace cb (gTokenChain 2) pf) (at level 45, no associativity).
Notation "'{' lc '~~~>' pf1 '===>' pf2 '}'" :=
  (reachableFrom_implies_chaintracePropSized 10 lc (gTokenChain 2) pf1 pf2) (at level 90, left associativity).



(* Test generators *)

(* Sample generator to see quality of generated chains *)
(* Sample (gTokenChain 2 token_cb 7). *)

(* Verify that gBATActionValid only produces valid actions *)
(* QuickChick (chainDebug 1 token_cb 7 gBATActionValid). *)

(* Get value of isFinalized in last state of a chain *)
Definition get_chain_finalized (cb : ChainBuilder) : bool :=
  match get_contract_state BAT.State cb.(builder_env) contract_base_addr with
  | Some state => state.(isFinalized)
  | None => true
  end.

(* Verify hardness of finalizing BAToken.
   Goal is ~ 2/3 of generated chains are finalized *)
(* QuickChick (forAllTokenChainBuilders 8 (fun cb => collect (get_chain_finalized cb) true)). *)
(*
  6386 : true
  3614 : false
  +++ Passed 10000 tests (0 discards)
*)

(* Check if an action is finalize *)
Definition action_is_finalize (action : Action) : bool :=
  match action.(act_body) with
  | Blockchain.act_transfer _ _ => false
  | Blockchain.act_deploy _ _ _ => false
  | Blockchain.act_call to _ msg =>
    if (address_eqb to contract_base_addr)
    then
      match @deserialize BAT.Msg _ msg with
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
  | Blockchain.act_transfer _ _ => false
  | Blockchain.act_deploy _ _ _ => false
  | Blockchain.act_call to _ msg =>
    if (address_eqb to contract_base_addr)
    then
      match @deserialize BAT.Msg _ msg with
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
  match get_contract_state BAT.State cs contract_base_addr with
  | Some state => (total_supply state)
  | None => 0%N
  end.

(* Verify spread of tokens after funding period is over.
   We do this to see it it possible to hit the funding cap. *)
(* QuickChick (forAllTokenChainBuilders 6 (fun cb => collect (get_chain_tokens cb) true)). *)
(*
  603 : 68
  590 : 65
  580 : 71
  555 : 74
  533 : 80
  530 : 59
  516 : 62
  493 : 77
  468 : 83
  452 : 56
  450 : 86
  424 : 89
  359 : 53
  346 : 101
  345 : 95
  343 : 50
  333 : 92
  312 : 98
  289 : 47
  243 : 44
  186 : 41
  165 : 38
  91 : 35
  64 : 32
  50 : 29
  33 : 26
  13 : 23
  5 : 20
  +++ Passed 10000 tests (0 discards)
*)



Local Open Scope N_scope.

Definition msg_is_transfer (cstate : BAT.State) (msg : BAT.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer _ _) => true
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
  {{msg_is_transfer}}
  contract_base_addr
  {{post_transfer_correct}}
). *)

(* +++ Passed 10000 tests (0 discards) *)

Definition msg_is_refund (cstate : BAT.State) (msg : BAT.Msg) :=
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

Definition post_refund_correct cctx old_state (msg : BAT.Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, [Blockchain.act_transfer to amount]), refund) =>
    whenFail (show cctx ++ nl ++ show old_state ++ nl ++ show result_opt)
    (checker (refund_correct old_state new_state cctx to amount))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.

(* False property: user that funded BAT can always refund if funding fails *)
(* QuickChick (
  {{msg_is_refund}}
  contract_base_addr
  {{post_refund_correct}}
). *)

(*
Chain{|
Block 1 [
Action{act_from: 10%256, act_body: (act_transfer 11%256, 10)};
Action{act_from: 10%256, act_body: (act_transfer 12%256, 7)};
Action{act_from: 10%256, act_body: (act_transfer 13%256, 6)};
Action{act_from: 10%256, act_body: (act_transfer 14%256, 10)};
Action{act_from: 10%256, act_body: (act_deploy 0, transfer 19%256 17)}];
Block 2 [
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer 12%256 20)};
Action{act_from: 13%256, act_body: (act_call 128%256, 2, create_tokens)}];
Block 3 [
Action{act_from: 13%256, act_body: (act_call 128%256, 0, approve 12%256 5)};
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer 15%256 0)}];
Block 4 [
Action{act_from: 12%256, act_body: (act_call 128%256, 0, approve 15%256 18)};
Action{act_from: 13%256, act_body: (act_call 128%256, 0, transfer 17%256 6)}];
Block 5 [
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer 11%256 5)};
Action{act_from: 17%256, act_body: (act_call 128%256, 0, approve 15%256 5)}];
Block 6 [
Action{act_from: 11%256, act_body: (act_call 128%256, 0, transfer 17%256 5)};
Action{act_from: 11%256, act_body: (act_call 128%256, 0, transfer 16%256 0)}];
Block 7 [
Action{act_from: 12%256, act_body: (act_call 128%256, 0, transfer 11%256 19)};
Action{act_from: 12%256, act_body: (act_call 128%256, 0, refund)}];|}

ChainState{env: Environment{chain: Chain{height: 7, current slot: 7, final height: 0}, contract states:...}, queue: Action{act_from: 12%256, act_body: (act_call 128%256, 0, transfer 11%256 19)};
Action{act_from: 12%256, act_body: (act_call 128%256, 0, refund)}}
On Msg: refund
ContractCallContext{ctx_from: 12%256, ctx_contract_addr: 128%256, ctx_contract_balance: 2, ctx_amount: 0}
State{token_state: State{total_supply: 26, balances: [15%256-->0; 11%256-->0; 17%256-->6; 13%256-->0; 16%256-->0; 12%256-->20], allowances: [17%256-->[15%256-->5]; 13%256-->[12%256-->5]; 12%256-->[15%256-->18]]}, isFinalized: false, fundDeposit: 16%256, batFundDeposit: 17%256, fundingStart: 0, fundingEnd: 5, tokenExchangeRate: 3, tokenCreationCap: 100, tokenCreationMin: 70}
Some (State{token_state: State{total_supply: 6, balances: [15%256-->0; 11%256-->0; 17%256-->6; 13%256-->0; 16%256-->0; 12%256-->0], allowances: [17%256-->[15%256-->5]; 13%256-->[12%256-->5]; 12%256-->[15%256-->18]]}, isFinalized: false, fundDeposit: 16%256, batFundDeposit: 17%256, fundingStart: 0, fundingEnd: 5, tokenExchangeRate: 3, tokenCreationCap: 100, tokenCreationMin: 70},[(act_transfer 12%256, 6)])
*)
(* *** Failed after 44 tests and 0 shrinks. (0 discards) *)

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
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer 15%256 1)};
Action{act_from: 12%256, act_body: (act_call 128%256, 6, create_tokens)}];
Block 3 [
Action{act_from: 11%256, act_body: (act_call 128%256, 8, create_tokens)};
Action{act_from: 15%256, act_body: (act_call 128%256, 0, transfer 15%256 1)}];
Block 4 [
Action{act_from: 11%256, act_body: (act_call 128%256, 0, approve 17%256 12)};
Action{act_from: 12%256, act_body: (act_call 128%256, 1, create_tokens)}];
Block 5 [
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer_from 11%256 12%256 4)};
Action{act_from: 14%256, act_body: (act_call 128%256, 3, create_tokens)}];
Block 6 [
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer_from 11%256 14%256 2)};
Action{act_from: 15%256, act_body: (act_call 128%256, 0, transfer 17%256 0)}];
Block 7 [
Action{act_from: 12%256, act_body: (act_call 128%256, 0, transfer 14%256 0)};
Action{act_from: 16%256, act_body: (act_call 128%256, 0, finalize)}];|}

Success - found witness satisfying the predicate!
+++ Failed (as expected) after 126 tests and 0 shrinks. (0 discards)
*)

Definition final_is_final :=
  {token_cb ~~~> (fun cs => if (is_finalized cs) then Some true else None) ===> 
    (fun _ _ post_trace => checker (fold_left (fun a (chainState : ChainState) => a && (is_finalized chainState) ) post_trace true))}.

(* Check that once finalized it cannot be undone *)
(* QuickChick final_is_final. *)
(* +++ Passed 10000 tests (5512 discards) *)










