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
Existing Instance BATPrinters.showMsg.

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

Definition forAllTokenChainStates n :=
  let max_acts_per_block := 2 in
  forAllChainState n token_cb (gTokenChain max_acts_per_block).

Definition pre_post_assertion_token P c Q :=
  let max_acts_per_block := 2 in
  let trace_length := 7 in
  pre_post_assertion trace_length token_cb (gTokenChain max_acts_per_block) BAT.contract c P Q.

Definition pre_post_assertion_token_ P c Q :=
  let max_acts_per_block := 2 in
  let trace_length := 7 in
  pre_post_assertion_ trace_length token_cb (gTokenChain max_acts_per_block) BAT.contract c P Q.

Notation "{{ P }} c {{ Q }}" := (pre_post_assertion_token P c Q) ( at level 50).
Notation "{{ P }} c {{ Q }}_" := (pre_post_assertion_token_ P c Q) ( at level 50).
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

(* Get chain length *)
Definition get_chain_height (cb : ChainBuilder) : nat :=
  cb.(builder_env).(chain_height).
(* Check heigh chains produced by the chain generator
   We want the average chain height to be close to full length
   since this is a sign that the generator does not generate 
   invalid requests so often that it affects chain quality *)
(* QuickChick (forAllTokenChainBuilders 8 (fun cb => collect (get_chain_height cb) true)). *)
(*
  9270 : 9
  333 : 8
  234 : 7
  144 : 6
  18 : 5
  1 : 2
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

Definition fmap_subseteqb {A B} `{countable.Countable A}
                          (eqb : B -> B -> bool) (fmap : FMap A B) (fmap' : FMap A B) : bool :=
  let elements := FMap.elements fmap in
    fold_left (fun b elem => 
                match FMap.lookup (fst elem) fmap' with
                | Some v => andb b (eqb (snd elem) v)
                | None => false
                end) elements true.

Definition fmap_eqb {A B} `{countable.Countable A}
                    (eqb : B -> B -> bool) (fmap : FMap A B) (fmap' : FMap A B) : bool :=
  andb (fmap_subseteqb eqb fmap fmap') (fmap_subseteqb eqb fmap' fmap).

Definition fmap_filter_eqb {A B} `{countable.Countable A}
                           (excluded : list A) (eqb : B -> B -> bool) (fmap : FMap A B) (fmap' : FMap A B) : bool :=
  let map_filter m l := fold_left (fun map elem => FMap.remove elem map) l m in
  let fmap_filtered := map_filter fmap excluded in
  let fmap'_filtered := map_filter fmap' excluded in
    fmap_eqb eqb fmap_filtered fmap'_filtered.

Definition get_balance (state : BAT.State) (addr : Address) :=
  with_default 0 (FMap.find addr (balances state)).

Definition msg_is_eip_msg (cstate : BAT.State) (msg : BAT.Msg) :=
  match msg with
  | tokenMsg _ => true
  | _ => false
  end.

Definition msg_is_transfer (cstate : BAT.State) (msg : BAT.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer _ _) => true
  | _ => false
  end.

Definition msg_is_transfer_from (cstate : BAT.State) (msg : BAT.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer_from _ _ _) => true
  | _ => false
  end.

Definition msg_is_approve (cstate : BAT.State) (msg : BAT.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer _ _) => true
  | _ => false
  end.

Definition msg_is_create_tokens (cstate : BAT.State) (msg : BAT.Msg) :=
  match msg with
  | create_tokens => true
  | _ => false
  end.

Definition msg_is_finalize (cstate : BAT.State) (msg : BAT.Msg) :=
  match msg with
  | finalize => true
  | _ => false
  end.

Definition msg_is_refund (cstate : BAT.State) (msg : BAT.Msg) :=
  match msg with
  | refund => true
  | _ => false
  end.


(* Checker failing if amount in a contract call context is not zero *)
Definition amount_is_zero cctx (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  (checker (cctx.(ctx_amount) =? 0)%Z).

(* Checker failing if amount in a contract call context is 0 or negative *)
Definition amount_is_positive cctx (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  (checker (cctx.(ctx_amount) >? 0)%Z).

(* Checker failing if result_opt contains actions *)
Definition produces_no_actions (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (_, []), _) => checker true
  | _ => checker false
  end.

(* Checker failing if result_opt contains less than or more than one action *)
Definition produces_one_action (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (_, [a]), _) => checker true
  | _ => checker false
  end.


(* Only create_tokens should be payable *)
(* QuickChick (
  {{fun state msg => negb (msg_is_create_tokens state msg)}}
  contract_base_addr
  {{amount_is_zero}}
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
Action{act_from: 13%256, act_body: (act_call 128%256, 2, create_tokens)};
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer 11%256 5)}];
Block 3 [
Action{act_from: 11%256, act_body: (act_call 128%256, 0, approve 17%256 0)};
Action{act_from: 13%256, act_body: (act_call 128%256, 3, create_tokens)}];
Block 4 [
Action{act_from: 11%256, act_body: (act_call 128%256, 0, approve 13%256 2)};
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer_from 11%256 13%256 0)}];
Block 5 [
Action{act_from: 14%256, act_body: (act_call 128%256, 1, create_tokens)};
Action{act_from: 14%256, act_body: (act_call 128%256, 8, create_tokens)}];
Block 6 [
Action{act_from: 11%256, act_body: (act_call 128%256, 0, approve 14%256 5)};
Action{act_from: 13%256, act_body: (act_call 128%256, 0, refund)}];
Block 7 [
Action{act_from: 14%256, act_body: (act_call 128%256, 1, refund)};
Action{act_from: 11%256, act_body: (act_call 128%256, 0, refund)}];
Block 8 [
Action{act_from: 14%256, act_body: (act_call 128%256, 0, transfer 11%256 0)};
Action{act_from: 14%256, act_body: (act_call 128%256, 0, transfer 12%256 0)}];|}

ChainState{
  env: Environment{chain: Chain{height: 7, current slot: 7, final height: 0}, contract states:...},
  queue: Action{act_from: 14%256, act_body: (act_call 128%256, 1, refund)};
         Action{act_from: 11%256, act_body: (act_call 128%256, 0, refund)}}
On Msg: refund
*** Failed after 92 tests and 0 shrinks. (0 discards)
*)

(* Create_tokens should only accept calls with money in them *)
(* QuickChick (
  {{msg_is_create_tokens}}
  contract_base_addr
  {{amount_is_positive}}
). *)
(* +++ Passed 10000 tests (0 discards) *)

(* EIP messages and create_tokens should not produce any actions *)
(* QuickChick (
  {{fun state msg => orb (msg_is_eip_msg state msg) (msg_is_create_tokens state msg)}}
  contract_base_addr
  {{produces_no_actions}}
). *)
(* +++ Passed 10000 tests (0 discards) *)

(* refund and finalize should produce an actions *)
(* QuickChick (
  {{fun state msg => orb (msg_is_refund state msg) (msg_is_finalize state msg)}}
  contract_base_addr
  {{produces_one_action}}
). *)
(* +++ Passed 10000 tests (0 discards) *)

(* Chcker failing if any constants in BAT states are changed *)
Definition constants_unchanged (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), _) =>
    let fund_deposit_check := address_eqb old_state.(fundDeposit) new_state.(fundDeposit) in
    let bat_deposit_check := address_eqb old_state.(batFundDeposit) new_state.(batFundDeposit) in
    let funding_start_check := Nat.eqb old_state.(fundingStart) new_state.(fundingStart) in
    let funding_end_check := Nat.eqb old_state.(fundingEnd) new_state.(fundingEnd) in
    let exchange_rate_check := N.eqb old_state.(tokenExchangeRate) new_state.(tokenExchangeRate) in
    let creation_cap_check := N.eqb old_state.(tokenCreationCap) new_state.(tokenCreationCap) in
    let creation_min_check := N.eqb old_state.(tokenCreationMin) new_state.(tokenCreationMin) in
      checker (andb fund_deposit_check
              (andb bat_deposit_check
              (andb funding_start_check
              (andb funding_end_check
              (andb exchange_rate_check
              (andb creation_cap_check
                    creation_min_check))))))
  (* if 'receive' failed then just discard this test *)
  | _ => checker false
  end.
(* No contract calls modify constants *)
(* QuickChick (
  {{fun state msg => true}}
  contract_base_addr
  {{constants_unchanged}}
). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- create_tokens -------------------- *)
Definition post_create_tokens_update_correct (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, []), create_tokens) =>
    let amount := cctx.(ctx_amount) in
    let from := cctx.(ctx_from) in
    let balance_correct := N.eqb (get_balance new_state from) ((get_balance old_state from) + (Z.to_N amount * old_state.(tokenExchangeRate))) in
    let total_supply_correct := N.eqb (total_supply new_state) ((total_supply old_state) + (Z.to_N amount * old_state.(tokenExchangeRate))) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb balance_correct
                   total_supply_correct))
  (* if 'receive' failed, or msg is not a create_tokens
     then just discard this test *)
  | _ => checker false
  end.
(* Create_tokens updates output correct *)
(* QuickChick ({{msg_is_create_tokens}} contract_base_addr {{post_create_tokens_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition create_tokens_valid env (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), create_tokens) =>
    let amount := cctx.(ctx_amount) in
    let current_slot := env.(current_slot) in
    let amount_valid := Z.leb 0 amount in
    let is_finalized_valid := negb old_state.(isFinalized) in
    let slot_valid := andb (old_state.(fundingStart) <=? current_slot)%nat (current_slot <=? old_state.(fundingEnd))%nat in
    let new_token_amount_valid := (total_supply old_state) + (Z.to_N amount * old_state.(tokenExchangeRate)) <=? old_state.(tokenCreationCap) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb amount_valid
             (andb is_finalized_valid
             (andb slot_valid
                   new_token_amount_valid))))
  (* if 'receive' failed, or msg is not a create_tokens
     then just discard this test *)
  | _ => checker false
  end.
(* Create_tokens contract calls are valid *)
(* QuickChick ({{msg_is_create_tokens}} contract_base_addr {{create_tokens_valid}}_). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_create_tokens_safe (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), create_tokens) =>
    let from := cctx.(ctx_from) in
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    let allowances_unchanged := fmap_eqb (fun fmap fmap' => fmap_eqb N.eqb fmap fmap') (allowances old_state) (allowances new_state) in
    let other_balances_unchanged := fmap_filter_eqb [from] N.eqb (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb is_finalized_unchanged
             (andb allowances_unchanged
                   other_balances_unchanged)))
  (* if 'receive' failed, or msg is not a create_tokens
     then just discard this test *)
  | _ => checker false
  end.
(* Create_tokens contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_create_tokens}} contract_base_addr {{post_create_tokens_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- finalize -------------------- *)
Definition post_finalize_update_correct env (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, [Blockchain.act_transfer to amount]), finalize) =>
    let balance := cctx.(ctx_contract_balance) in
    let is_finalized_correct := Bool.eqb new_state.(isFinalized) true in
    let action_to_correct := address_eqb to ethFund in
    let action_amount_correct := Z.eqb amount balance in
    let action_to_valid := negb (address_is_contract to) in
    let action_amount_valid := Z.leb amount (env_account_balances env cctx.(ctx_contract_address)) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb is_finalized_correct
             (andb action_to_correct
             (andb action_amount_correct
             (andb action_to_valid
                   action_amount_valid)))))
  (* if 'receive' failed, or msg is not a finalize
     then just discard this test *)
  | _ => checker false
  end.
(* Finalize updates state correct and produces correct actions *)
(* QuickChick ({{msg_is_finalize}} contract_base_addr {{post_finalize_update_correct}}_). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition finalize_valid env (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), finalize) =>
    let from := cctx.(ctx_from) in
    let current_slot := env.(current_slot) in
    (* Only ethFund should be allowed to call finalize *)
    let from_valid := address_eqb from ethFund in
    (* Finalization should only be allowed if contract not already finalized *)
    let is_finalized_valid := negb old_state.(isFinalized) in
    (* Finalization should only be allowed if funding period is over or we hit the token cap *)
    let can_finalize_valid := orb (old_state.(fundingEnd) <? current_slot)%nat (N.eqb old_state.(tokenCreationCap) (total_supply old_state)) in
    (* Finalization should only be allowed if token amount is within valid (tokenCreationMin, tokenCreationCap) range *)
    let total_supply_valid := andb (N.leb old_state.(tokenCreationMin) (total_supply old_state)) (N.leb (total_supply old_state) old_state.(tokenCreationCap)) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb from_valid
             (andb is_finalized_valid
             (andb can_finalize_valid
                   total_supply_valid))))
  (* if 'receive' failed, or msg is not a finalize
     then just discard this test *)
  | _ => checker false
  end.
(* Finalize contract calls are valid *)
(* QuickChick ({{msg_is_finalize}} contract_base_addr {{finalize_valid}}_). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_finalize_safe (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), finalize) =>
    (* Finalize should not change allowances *)
    let allowances_unchanged := fmap_eqb (fun fmap fmap' => fmap_eqb N.eqb fmap fmap') (allowances old_state) (allowances new_state) in
    (* Finalize should not change balances *)
    let balances_unchanged := fmap_eqb N.eqb (balances old_state) (balances new_state) in
    (* Finalize should not change total_supply *)
    let total_supply_unchanged := N.eqb (total_supply old_state) (total_supply new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb allowances_unchanged
             (andb balances_unchanged
                   total_supply_unchanged)))
  (* if 'receive' failed, or msg is not a finalize
     then just discard this test *)
  | _ => checker false
  end.
(* Finalize contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_finalize}} contract_base_addr {{post_finalize_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- refund -------------------- *)
Definition post_refund_update_correct env (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, [Blockchain.act_transfer to amount]), refund) =>
    let from := cctx.(ctx_from) in
    let contract_balance := cctx.(ctx_contract_balance) in
    let from_bal_old := with_default 0 (FMap.find from (balances old_state)) in
    let from_bal_new := with_default 0 (FMap.find from (balances new_state)) in
    let eth_to_refund := Z.of_N (from_bal_old / (tokenExchangeRate old_state)) in
    (* Refund should subtract the refunded account balance from total_supply *)
    let total_supply_correct := N.eqb (total_supply old_state) ((total_supply new_state) + from_bal_old) in
    (* Refund should set the refunded account balance to 0 *)
    let from_balance_correct := N.eqb from_bal_new 0 in
    (* Refund shoul pay the refunded account *)
    let action_to_correct := address_eqb from to in
    (* Refund should pay account_balance / exchange_rate *)
    let action_amount_correct := Z.eqb amount eth_to_refund in
    let action_to_valid := negb (address_is_contract to) in
    (* Contract should have enough money to refund *)
    let action_amount_valid := Z.leb amount (env_account_balances env cctx.(ctx_contract_address)) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb total_supply_correct
             (andb from_balance_correct
             (andb action_to_correct
             (andb action_amount_correct
             (andb action_to_valid
                   action_amount_valid))))))
  (* if 'receive' failed, or msg is not a refund
     then just discard this test *)
  | _ => checker false
  end.
(* False property: Refund updates state correct and produces correct actions *)
(* QuickChick ({{msg_is_refund}} contract_base_addr {{post_refund_update_correct}}_). *)
(* Chain{|
Block 1 [
Action{act_from: 10%256, act_body: (act_transfer 11%256, 10)};
Action{act_from: 10%256, act_body: (act_transfer 12%256, 7)};
Action{act_from: 10%256, act_body: (act_transfer 13%256, 6)};
Action{act_from: 10%256, act_body: (act_transfer 14%256, 10)};
Action{act_from: 10%256, act_body: (act_deploy 0, transfer 19%256 17)}];
Block 2 [
Action{act_from: 11%256, act_body: (act_call 128%256, 4, create_tokens)};
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer 14%256 3)}];
Block 3 [
Action{act_from: 14%256, act_body: (act_call 128%256, 0, transfer 11%256 3)};
Action{act_from: 14%256, act_body: (act_call 128%256, 0, approve 17%256 3)}];
Block 4 [
Action{act_from: 13%256, act_body: (act_call 128%256, 4, create_tokens)};
Action{act_from: 17%256, act_body: (act_call 128%256, 0, transfer_from 14%256 17%256 0)}];
Block 5 [
Action{act_from: 14%256, act_body: (act_call 128%256, 0, transfer 16%256 0)};
Action{act_from: 13%256, act_body: (act_call 128%256, 1, create_tokens)}];
Block 6 [
Action{act_from: 13%256, act_body: (act_call 128%256, 0, refund)};
Action{act_from: 11%256, act_body: (act_call 128%256, 0, transfer 11%256 7)}];
Block 7 [
Action{act_from: 16%256, act_body: (act_call 128%256, 0, transfer 17%256 0)};
Action{act_from: 11%256, act_body: (act_call 128%256, 0, approve 17%256 10)}];
Block 8 [
Action{act_from: 11%256, act_body: (act_call 128%256, 0, transfer 15%256 12)};
Action{act_from: 11%256, act_body: (act_call 128%256, 0, refund)}];|}

ChainState{env: Environment{chain: Chain{height: 8, current slot: 8, final height: 0}, contract states:...}, queue: Action{act_from: 11%256, act_body: (act_call 128%256, 0, transfer 15%256 12)};
Action{act_from: 11%256, act_body: (act_call 128%256, 0, refund)}}
On Msg: refund
State{token_state: State{total_supply: 32, balances: [11%256-->15; 17%256-->17; 13%256-->0; 16%256-->0; 14%256-->0], allowances: [11%256-->[17%256-->10]; 14%256-->[17%256-->3]]}, isFinalized: false, fundDeposit: 16%256, batFundDeposit: 17%256, fundingStart: 0, fundingEnd: 5, tokenExchangeRate: 3, tokenCreationCap: 101, tokenCreationMin: 63}
Some (State{token_state: State{total_supply: 17, balances: [11%256-->0; 17%256-->17; 13%256-->0; 16%256-->0; 14%256-->0], allowances: [11%256-->[17%256-->10]; 14%256-->[17%256-->3]]}, isFinalized: false, fundDeposit: 16%256, batFundDeposit: 17%256, fundingStart: 0, fundingEnd: 5, tokenExchangeRate: 3, tokenCreationCap: 101, tokenCreationMin: 63},[(act_transfer 11%256, 5)])
*** Failed after 228 tests and 0 shrinks. (0 discards) *)

Definition refund_valid env (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), refund) =>
    let current_slot := env.(current_slot) in
    let from := cctx.(ctx_from) in
    let from_bal_old := with_default 0 (FMap.find from (balances old_state)) in
    (* Refund should only be allowed if contract not finalized *)
    let is_finalized_valid := negb old_state.(isFinalized) in
    (* Refund should only be allowed if funding period is over *)
    let current_slot_valid := (old_state.(fundingEnd) <? current_slot)%nat in
    (* Refund should only be allowed if contract did not hit minimum token goal *)
    let total_supply_valid := N.ltb (total_supply old_state) old_state.(tokenCreationMin) in
    (* Refund shoul only be allowed if sender has tokens *)
    let balance_valid := N.ltb 0 from_bal_old in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb is_finalized_valid
             (andb current_slot_valid
             (andb total_supply_valid
                   balance_valid))))
  (* if 'receive' failed, or msg is not a refund
     then just discard this test *)
  | _ => checker false
  end.
(* Refund contract calls are valid *)
(* QuickChick ({{msg_is_refund}} contract_base_addr {{refund_valid}}_). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_refund_safe (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), refund) =>
    let from := cctx.(ctx_from) in
    (* Refund should not change isFinalized *)
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    (* Refund should not change allowances *)
    let allowances_unchanged := fmap_eqb (fun fmap fmap' => fmap_eqb N.eqb fmap fmap') (allowances old_state) (allowances new_state) in
    (* Refund should not change other balances than the senders balance *)
    let other_balances_unchanged := fmap_filter_eqb [from] N.eqb (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb is_finalized_unchanged
             (andb allowances_unchanged
                   other_balances_unchanged)))
  (* if 'receive' failed, or msg is not a refund
     then just discard this test *)
  | _ => checker false
  end.
(* Refund contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_refund}} contract_base_addr {{post_refund_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- transfer -------------------- *)
Definition post_transfer_update_correct (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, []), tokenMsg (EIP20Token.transfer to tokens)) =>
    let from := cctx.(ctx_from) in
    let from_balance_before := with_default 0 (FMap.find from (balances old_state)) in
    let to_balance_before := with_default 0 (FMap.find to (balances old_state)) in
    let from_balance_after := with_default 0 (FMap.find from (balances new_state)) in
    let to_balance_after := with_default 0 (FMap.find to (balances new_state)) in
    let from_to_same := address_eqb from to in
    let from_balance_correct := if from_to_same
                                then (from_balance_before =? from_balance_after)
                                else (from_balance_before =? from_balance_after + tokens) in
    let to_balance_correct :=   if from_to_same
                                then (to_balance_before =? to_balance_after)
                                else (to_balance_before + tokens =? to_balance_after) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb from_balance_correct
                   to_balance_correct))
  (* if 'receive' failed, or msg is not a transfer
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer updates output correct *)
(* QuickChick ({{msg_is_transfer}} contract_base_addr {{post_transfer_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition transfer_valid (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer to tokens)) =>
    let from := cctx.(ctx_from) in
    let amount := cctx.(ctx_amount) in
    let from_balance_before := with_default 0 (FMap.find from (balances old_state)) in
    let from_balance_valid := N.leb tokens from_balance_before in
    let amount_valid := Z.eqb amount 0 in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb amount_valid
                   from_balance_valid))
  (* if 'receive' failed, or msg is not a transfer
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer contract calls are valid *)
(* QuickChick ({{msg_is_transfer}} contract_base_addr {{transfer_valid}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_transfer_safe (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer to tokens)) =>
    let from := cctx.(ctx_from) in
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    let total_supply_unchanged := N.eqb (total_supply old_state) (total_supply new_state) in
    let allowances_unchanged := fmap_eqb (fun fmap fmap' => fmap_eqb N.eqb fmap fmap') (allowances old_state) (allowances new_state) in
    let other_balances_unchanged := fmap_filter_eqb [from; to] N.eqb (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb is_finalized_unchanged
             (andb total_supply_unchanged
             (andb allowances_unchanged
                   other_balances_unchanged))))
  (* if 'receive' failed, or msg is not a transfer
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_transfer}} contract_base_addr {{post_transfer_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- transfer_from -------------------- *)
Definition post_transfer_from_update_correct (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, []), tokenMsg (EIP20Token.transfer_from from to tokens)) =>
    let delegate := cctx.(ctx_from) in
    let from_balance_before := with_default 0 (FMap.find from (balances old_state)) in
    let to_balance_before := with_default 0 (FMap.find to (balances old_state)) in
    let from_balance_after := with_default 0 (FMap.find from (balances new_state)) in
    let to_balance_after := with_default 0 (FMap.find to (balances new_state)) in
    let delegate_allowance_before := with_default 0 (FMap.find delegate (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances old_state)))) in
    let delegate_allowance_after := with_default 0 (FMap.find delegate (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances new_state)))) in
    let from_to_same := address_eqb from to in
    let from_balance_correct := if from_to_same
                                then (from_balance_before =? from_balance_after)
                                else (from_balance_before =? from_balance_after + tokens) in
    let to_balance_correct :=   if from_to_same
                                then (to_balance_before =? to_balance_after)
                                else (to_balance_before + tokens =? to_balance_after) in
    let delefate_allowance_correct := delegate_allowance_before =? delegate_allowance_after + tokens in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb from_balance_correct
             (andb to_balance_correct
                 delefate_allowance_correct)))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer_from updates output correct *)
(* QuickChick ({{msg_is_transfer_from}} contract_base_addr {{post_transfer_from_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition transfer_from_valid (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer_from from to tokens)) =>
    let delegate := cctx.(ctx_from) in
    let amount := cctx.(ctx_amount) in
    let from_balance_before := with_default 0 (FMap.find from (balances old_state)) in
    let delegate_allowance_before := with_default 0 (FMap.find delegate (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances old_state)))) in
    let from_balance_valid := N.leb tokens from_balance_before in
    let delegate_allowance_valid := N.leb tokens delegate_allowance_before in
    let amount_valid := Z.eqb amount 0 in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb amount_valid
                   from_balance_valid))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer_from contract calls are valid *)
(* QuickChick ({{msg_is_transfer_from}} contract_base_addr {{transfer_from_valid}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_transfer_from_safe (cctx : ContractCallContext) (old_state : State) (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer_from from to tokens)) =>
    let delegate := cctx.(ctx_from) in
    let from_allowances_before := with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances old_state)) in
    let from_allowances_after := with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances new_state)) in
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    let total_supply_unchanged := N.eqb (total_supply old_state) (total_supply new_state) in
    let other_allowances_unchanged := fmap_filter_eqb [from] (fun fmap fmap' => fmap_eqb N.eqb fmap fmap') (allowances old_state) (allowances new_state) in
    let other_allowance_unchanged := fmap_filter_eqb [delegate] N.eqb from_allowances_before from_allowances_after in
    let other_balances_unchanged := fmap_filter_eqb [from; to] N.eqb (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (andb is_finalized_unchanged
             (andb total_supply_unchanged
             (andb other_allowances_unchanged
             (andb other_allowance_unchanged
                   other_balances_unchanged)))))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer_from contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_transfer_from}} contract_base_addr {{post_transfer_from_safe}}). *)
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










