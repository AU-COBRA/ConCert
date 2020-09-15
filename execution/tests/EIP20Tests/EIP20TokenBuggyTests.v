Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.

From ConCert Require Import Blockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import Containers.
From ConCert Require Import EIP20Token EIP20Token_Buggy.
From ConCert Require Import ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters EIP20TokenPrinters EIP20TokenGens TraceGens.

From Coq Require Import List. 
Import ListNotations.
Import BoundedN.Stdpp.
Import LocalBlockchain.

(* -------------------------- Tests of the Buggy EIP20 Token Implementation -------------------------- *)

Existing Instance showTokenState.

Definition token_setup := EIP20Token.build_setup creator (100%N).
Definition deploy_eip20token := create_deployment 0 EIP20Token_Buggy.contract token_setup.

Definition token_caddr := BoundedN.of_Z_const AddrSize 128%Z.

(* In the initial chain we transfer some assets to a few accounts, just to make the addresses
   present in the chain state. The amount transferred is irrelevant. *)
Definition token_cb :=
  ResultMonad.unpack_result (TraceGens.add_block (lcb_initial AddrSize)
  [
    build_act creator (act_transfer person_1 0);
    build_act creator (act_transfer person_2 0);
    build_act creator (act_transfer person_3 0);
    build_act creator deploy_eip20token
  ]).

Module TestInfo <: EIP20GensInfo.
  Definition contract_addr := token_caddr.
  Definition gAccount (c : Chain) := elems [person_1; person_2; person_3; person_4; person_5].
End TestInfo.
Module MG := EIP20Gens TestInfo. Import MG.

Definition gTokenChain max_acts_per_block token_cb max_length := 
  let act_depth := 1 in 
  gChain token_cb
    (fun env act_depth => gEIP20TokenAction env) max_length act_depth max_acts_per_block.
(* Sample (gTokenChain 2 token_cb 7).  *)

Definition forAllTokenChainTraces n :=
  let max_acts_per_block := 2 in
  forAllChainState n token_cb (gTokenChain max_acts_per_block).

Instance genBuggyTokenChainSized : GenSized ChainBuilder := {
  arbitrarySized n := gTokenChain 2 token_cb n
}.

Definition pre_post_assertion_token P c Q :=
  let max_acts_per_block := 1 in
  let trace_length := 5 in
  pre_post_assertion trace_length token_cb (gTokenChain max_acts_per_block) EIP20Token_Buggy.contract c P Q.

Notation "{{ P }} c {{ Q }}" := (pre_post_assertion_token P c Q) ( at level 50).

Definition msg_is_transfer_from (cstate : EIP20Token.State) (msg : EIP20Token.Msg) :=
  match msg with
  | transfer_from _ _ _ => true
  | _ => false
  end.

Definition checker_get_state {prop} `{Checkable prop} (pf : State -> prop) (cs : ChainState) : Checker := 
  match get_contract_state EIP20Token.State cs token_caddr with
  | Some state => checker (pf state)
  | None => checker true (* trivially true case *) 
  end.

Definition get_state (pf : State -> bool) (cs : ChainState) : bool := 
  match get_contract_state EIP20Token.State cs token_caddr with
  | Some state => pf state
  | None => true (* trivially true case *) 
  end.


Open Scope N_scope.
Open Scope string_scope.
(* One key property: the sum of the balances is always equal to the initial supply *)
Definition sum_balances_eq_init_supply_checker (state : EIP20Token.State) :=
  let balances_list := (map snd o FMap.elements) state.(balances) in
  let balances_sum : N := fold_left N.add balances_list 0%N in
  whenFail (
    "balances_sum: " ++ show balances_sum ++ nl ++
    "total_supply: " ++ show state.(total_supply) ++ nl ++
    "balances: " ++ show state.(balances)
    )
  (balances_sum =? state.(total_supply))%N.
Close Scope string_scope.

Definition sum_balances_eq_init_supply (state : EIP20Token.State) : bool :=
  let balances_list := (map snd o FMap.elements) state.(balances) in
  let balances_sum : N := fold_left N.add balances_list 0%N in
  (balances_sum =? state.(total_supply))%N.

Conjecture token_supply_preserved : forall sig_to : {to | reachable to}, 
  let to := proj1_sig sig_to in
  get_state sum_balances_eq_init_supply to = true.

(* QuickChick token_supply_preserved. *)
(* *** Failed after 11 tests and 1000 shrinks. (0 discards)
       on transfer_from 10%256 10%256 4 *)
(* or alternatively: *)
(* QuickChick (forAllTokenChainTraces 4 (checker_get_state sum_balances_eq_init_supply)). *)

Definition transfer_balance_update_correct old_state new_state from to tokens :=
  let get_balance addr state := with_default 0 (FMap.find addr state.(balances)) in
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

Definition post_transfer_from_correct (cctx : ContractCallContext) 
                                      (old_state : State) 
                                      (msg : Msg) 
                                      (result_opt : option (State * list ActionBody)) 
                                      : Checker :=
  match (result_opt, msg) with
  | (Some (new_state, _), transfer_from from to tokens) =>
    whenFail (show msg ++ nl ++ show old_state ++ nl ++ show result_opt)
    (checker (transfer_balance_update_correct old_state new_state from to tokens))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.

(* QuickChick (
  {{msg_is_transfer_from}}
  token_caddr
  {{post_transfer_from_correct}}
). *)
