Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import Containers.
From ConCert Require Import EIP20Token.
From ConCert Require Import ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters EIP20TokenPrinters EIP20TokenGens TraceGens.

From Coq Require Import List.
Import ListNotations.
Import BoundedN.Stdpp.
Import LocalBlockchain.

(* -------------------------- Tests of the EIP20 Token Implementation -------------------------- *)

Existing Instance showTokenState.

Definition token_setup := EIP20Token.build_setup creator (100%N).
Definition deploy_eip20token := create_deployment 0 EIP20Token.contract token_setup.

Let contract_base_addr := BoundedN.of_Z_const AddrSize 128%Z.

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
  Definition contract_addr := contract_base_addr.
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

Definition pre_post_assertion_token P c Q :=
  let max_acts_per_block := 2 in
  let trace_length := 7 in
  pre_post_assertion trace_length token_cb (gTokenChain max_acts_per_block) EIP20Token.contract c P Q.

Notation "{{ P }} c {{ Q }}" := (pre_post_assertion_token P c Q) ( at level 50).

Local Open Scope N_scope.
Extract Constant defNumDiscards => "(3 * defNumTests)".

Definition msg_is_transfer (cstate : EIP20Token.State) (msg : EIP20Token.Msg) :=
  match msg with
  | transfer _ _ => true
  | _ => false
  end.

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

Definition post_transfer_correct cctx old_state msg (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), transfer to tokens) =>
    let from := cctx.(ctx_from) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (transfer_balance_update_correct old_state new_state from to tokens))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.

(* QuickChick (
  {{msg_is_transfer}}
  contract_base_addr
  {{post_transfer_correct}}
). *)

(* +++ Passed 10000 tests (0 discards) *)

(* One key property: the sum of the balances is always equal to the initial supply *)
Definition sum_balances_eq_init_supply (state : EIP20Token.State) :=
  let balances_list := (map snd o FMap.elements) state.(balances) in
  let balances_sum : N := fold_left N.add balances_list 0%N in
  balances_sum =? state.(total_supply).

Definition checker_get_state {prop} `{Checkable prop} (pf : State -> prop) (cs : ChainState) : Checker := 
  match get_contract_state EIP20Token.State cs contract_base_addr with
  | Some state => checker (pf state)
  | None => checker true (* trivially true case *) 
  end.

(* QuickChick (forAllTokenChainTraces 5 (checker_get_state sum_balances_eq_init_supply)). *)
(* coqtop-stdout:+++ Passed 10000 tests (1570 discards) *)
(* 8 seconds *)

(* INVALID PROPERTY: accounts may allow multiple other accounts to transfer tokens, but the actual transfer ensures that
   no more tokens are sent than the balance of the sender. *)
Definition sum_allowances_le_init_supply (state : EIP20Token.State) :=
  (* debug_gEIP20Checker lc None *)
  let allowances := map_values_FMap
    (fun allowance_map => fold_left N.add ((map snd o FMap.elements) allowance_map) 0)
      state.(allowances) in
  let allowances_list := (map snd o FMap.elements) allowances in
  let allowances_sum := fold_left N.add allowances_list 0%N in
  allowances_sum <=? state.(total_supply).

Definition sum_allowances_le_init_supply_P maxLength :=
  forAllChainState maxLength token_cb (gTokenChain 2)
    (checker_get_state sum_allowances_le_init_supply).

(* QuickChick (sum_allowances_le_init_supply_P 5). *)

Definition person_has_tokens person (n : N) :=
  fun cs => 
    match get_contract_state State cs contract_base_addr with
    | Some state => n =? (FMap_find_ person state.(balances) 0)
    | None => true (* trivial case *)
    end.
    
(* Notation "cb '~~>' pf" :=
  (reachableFrom_chaintrace cb (gTokenChain 2) pf)
  (at level 45, no associativity). *)

(* QuickChick (token_cb ~~> (person_has_tokens person_3 12)). *)

(* QuickChick (chain_with_token_deployed ~~> (fun lc => isSome (person_has_tokens person_3 12 lc))). *)
(* QuickChick (chain_with_token_deployed ~~> person_has_tokens creator 0). *)

(* QuickChick (token_reachableFrom_implies_reachable
  chain_with_token_deployed
  (person_has_tokens creator 10)
  (person_has_tokens creator 0)
). *)

Notation "'{' lc '~~>' pf1 '===>' pf2 '}'" :=
  (reachableFrom_implies_chaintracePropSized 3 lc (gTokenChain 2) pf1 pf2)
  (at level 90, left associativity).

(* This (false) property says that from the initial chain where the token contract has been deployed,
   if there is a reachable state where the creator has 5 tokens, then any trace afterwards
   will satisfy that the creator has 10 tokens. This is obviously not true, and QC will give us a counterexample. *)
(* QuickChick (
  {
    chain_with_token_deployed
    ~~> (person_has_tokens creator 5 o next_lc_of_lcstep)
    ===> (fun _ _ post_trace => isSome (person_has_tokens creator 10 (last_state post_trace)))
  }
). *)

Definition get_approve_act (act : Action) : option (Address * Address * EIP20Token.Msg) :=
  match act.(act_body) with
  | act_call caddr _ ser_msg =>
    match deserialize EIP20Token.Msg _ ser_msg with
    | Some (approve _ _ as msg) => Some (caddr, act.(act_from), msg)
    | _ => None
    end
  | _ => None
  end.

Definition get_transferFrom_act (act : Action) : option (Address * Address * EIP20Token.Msg) :=
  match act.(act_body) with
  | act_call caddr _ ser_msg =>
    match deserialize EIP20Token.Msg _ ser_msg with
    | Some (transfer_from _ _ _ as msg) => Some (caddr, act.(act_from), msg)
    | _ => None
    end
  | _ => None
  end.

Definition state_has_some_approve_act (cs : ChainState) :=
  match find (isSome o get_approve_act) cs.(chain_state_queue) with
  | Some x => get_approve_act x
  | None => None
  end.

Definition delegate_made_no_transferFroms (approve_act_p :  (Address * Address * EIP20Token.Msg))
                                          (cs : ChainState) :=
  let caddr := fst (fst approve_act_p) in
  let approver := snd (fst approve_act_p) in
  match (snd approve_act_p) with
  | approve delegate amount =>
    let acts := cs.(chain_state_queue) in
    let act_not_transferFrom_delegate act :=
        match get_transferFrom_act act with
        | Some (caddr', caller, (transfer_from from to _)) =>
          if (address_eqb caddr' caddr)
          then negb ((address_eqb caller delegate) || (address_eqb from approver))
          else true
        | _ => true
        end in
    forallb act_not_transferFrom_delegate acts
  | _ => false
  end.

Definition allower_addr (approve_act_p : (Address * Address * EIP20Token.Msg)) :=
  match snd approve_act_p with
  | (approve _ _ ) => snd (fst approve_act_p)
  | (transfer_from allower _ _) => allower
  | _ => zero_address
  end.
Definition delegate_addr (approve_act_p : (Address * Address * EIP20Token.Msg)) :=
  match (snd approve_act_p) with
  | (approve delegate _ ) => Some delegate
  | (transfer_from _ _ _) => Some (snd (fst approve_act_p))
  | _ => None
  end.

Definition approve_amount (approve_act_p : (Address * Address * EIP20Token.Msg)) :=
  match (snd approve_act_p) with
  | (approve _ amount ) => amount
  | _ => 0
  end.

Definition transfer_from_amount (transferFrom_act_p : (Address * Address * EIP20Token.Msg)) :=
  match (snd transferFrom_act_p) with
  | (transfer_from _ _ amount ) => amount
  | _ => 0
  end.

Definition allower_reapproves_delegate_step allower delegate (cs : ChainState) :=
  let acts := cs.(chain_state_queue) in
  match find isSome (map get_approve_act acts) with
  | Some (Some (caddr, caller, (approve delegate' amount)) as act)  =>
    if address_eqb caller allower && address_eqb delegate delegate'
    then Some amount
    else None
  | _ => None
  end.

Definition delegate_transferFrom_sum_of_approver approver delegate (trace : list ChainState) :=
  fold_left (fun acc step =>
    let transfer_from_acts := fold_left (fun acc act =>
      match get_transferFrom_act act with
      | Some x => x :: acc
      | None => acc
      end
    ) (step.(chain_state_queue)) [] in
    let filter_p p := if address_eqb (allower_addr p) approver
                      then match delegate_addr p with
                           | Some delegate' => address_eqb delegate delegate'
                           | None => false
                           end
                      else false in
    let relevant_transfer_from_acts := filter filter_p transfer_from_acts in
    let step_sum := fold_left (fun acc p => (transfer_from_amount p) + acc) relevant_transfer_from_acts 0 in
    step_sum + acc
  ) trace 0.

Definition allower_reapproves_transferFrom_correct (pre_trace post_trace : list ChainState) allower delegate (first_approval_amount : N) :=
  let trace := pre_trace ++ post_trace in
  let reapprove_correct cs :=
  (* Checks if a chainstate has a re-approval act, and if so, then checks that the spent amount inbetween
     the first approval and the re-approval is not greater than expected. *)
  let res := (allower_reapproves_delegate_step allower delegate cs) in
    isSomeCheck res (fun new_approval_amount =>
      let p := split_at_first_satisfying (isSome o (allower_reapproves_delegate_step allower delegate)) trace in
      match p with
      | Some (trace_until_reapproval, _) =>
        let delegate_spent_until_reapproval := delegate_transferFrom_sum_of_approver allower delegate trace_until_reapproval in
        let delegate_spent_incl_reapproval_act :=
          delegate_transferFrom_sum_of_approver allower delegate trace in
        let total_allowed := delegate_spent_until_reapproval + new_approval_amount in
        (new_approval_amount <? first_approval_amount) ==>
        whenFail (show delegate ++ " spent "
          ++ show delegate_spent_incl_reapproval_act
          ++ " on behalf of " ++ show allower
          ++ " when they were only allowed to spend at most "
          ++ show total_allowed  ++ nl)
        (delegate_spent_incl_reapproval_act <=? total_allowed)
      | None => checker false
      end) in
  conjoin_map reapprove_correct trace.

Definition reapprove_transfer_from_safe_P :=
  {token_cb ~~> state_has_some_approve_act ===>
  (fun approve_act_p pre_trace post_trace =>
    isSomeCheck (delegate_addr approve_act_p) (fun delegate =>
      allower_reapproves_transferFrom_correct pre_trace
                                              post_trace
                                              (allower_addr approve_act_p)
                                              delegate
                                              (approve_amount approve_act_p)))}.

(* QuickChick reapprove_transfer_from_safe_P. *)

(* 
Chain{| 
Block 1 [
Action{act_from: 10%256, act_body: (act_transfer 11%256, 0)};
Action{act_from: 10%256, act_body: (act_transfer 12%256, 0)};
Action{act_from: 10%256, act_body: (act_transfer 13%256, 0)};
Action{act_from: 10%256, act_body: (act_deploy 0, transfer 10%256 100)}];
Block 2 [
Action{act_from: 10%256, act_body: (act_call 128%256, 0, transfer 11%256 7)};
Action{act_from: 10%256, act_body: (act_call 128%256, 0, transfer 12%256 34)}];
Block 3 [
Action{act_from: 10%256, act_body: (act_call 128%256, 0, approve 12%256 32)};
Action{act_from: 10%256, act_body: (act_call 128%256, 0, approve 11%256 23)}];
Block 4 [
Action{act_from: 12%256, act_body: (act_call 128%256, 0, transfer_from 10%256 10%256 25)};
Action{act_from: 10%256, act_body: (act_call 128%256, 0, approve 12%256 8)}];|}

12%256 spent 25 on behalf of 10%256 when they were only allowed to spend at most 8

*** Failed after 1 tests and 0 shrinks. (216 discards)
*)

(* Definition transfer_from_reduces_balance_correctly_P := TODO... *)
