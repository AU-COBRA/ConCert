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

Definition bat_setup := BAT.build_setup (20%N) ethFund batFund 0 5 (3%N) (100%N) (70%N).
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
  Definition gAccount (c : Chain) := elems [batFund; ethFund; person_1; person_2; person_3; person_4; person_5].
  Definition bat_addr := batFund.
  Definition fund_addr := ethFund.
End TestInfo.
Module MG := BATGens TestInfo. Import MG.

Definition gTokenChain max_acts_per_block token_cb max_length := 
  let act_depth := 1 in 
  gChain_full_sized token_cb
    (fun env act_depth => gBATAction env) max_length act_depth max_acts_per_block.
(* Sample (gTokenChain 2 token_cb 7). *)

Definition forAllTokenChainTraces n :=
  let max_acts_per_block := 2 in
  forAllChainState n token_cb (gTokenChain max_acts_per_block).

Definition pre_post_assertion_token P c Q :=
  let max_acts_per_block := 2 in
  let trace_length := 7 in
  pre_post_assertion trace_length token_cb (gTokenChain max_acts_per_block) BAT.contract c P Q.

Notation "{{ P }} c {{ Q }}" := (pre_post_assertion_token P c Q) ( at level 50).
Notation "cb '~~>' pf" := (reachableFrom_chaintrace cb (gTokenChain 2) pf) (at level 45, no associativity).
Notation "'{' lc '~~~>' pf1 '===>' pf2 '}'" :=
  (reachableFrom_implies_chaintracePropSized 10 lc (gTokenChain 2) pf1 pf2) (at level 90, left associativity).

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

(* BAT setup where it is easier to finalize to avoid discards *)
Definition bat_setup' := BAT.build_setup (20%N) ethFund batFund 0 8 (8%N) (2000%N) (50%N).
Definition deploy_bat' := create_deployment 0 BAT.contract bat_setup'.
Definition token_cb' :=
  ResultMonad.unpack_result (TraceGens.add_block (lcb_initial AddrSize)
  [
    build_act creator (Blockchain.act_transfer person_1 15);
    build_act creator (Blockchain.act_transfer person_2 15);
    build_act creator (Blockchain.act_transfer person_3 10);
    build_act creator (Blockchain.act_transfer person_4 10);
    build_act creator deploy_bat'
  ]).

Definition final_is_final :=
  {token_cb' ~~~> (fun cs => if (is_finalized cs) then Some true else None) ===> 
    (fun _ _ post_trace => checker (fold_left (fun a (chainState : ChainState) => a && (is_finalized chainState) ) post_trace true))}.

(* Check that once finalized it cannot be undone *)
(* QuickChick final_is_final. *)
(* +++ Passed 10000 tests (9493 discards) *)










