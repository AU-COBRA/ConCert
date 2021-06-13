Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith.
From QuickChick Require Import QuickChick. Import QcNotation.

From ConCert Require Import Blockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import Containers.
From ConCert Require Import BAT_Fixed.
Require Import Extras.

From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters BAT_FixedPrinters BAT_FixedGens TraceGens.

From Coq Require Import List.
Import ListNotations.
Import LocalBlockchain.

(* -------------------------- Tests of the BAT_Fixed Implementation -------------------------- *)

Existing Instance BAT_FixedPrinters.showBATState.
Existing Instance BAT_FixedPrinters.showMsg.
Existing Instance BAT_FixedPrinters.showBATSetup.

Definition ethFund : Address := BoundedN.of_Z_const AddrSize 16%Z.
Definition batFund : Address := BoundedN.of_Z_const AddrSize 17%Z.
Definition initSupply : N := 20%N.
Definition fundingStart_ := 1.
Definition fundingEnd_ := 4.
Definition exchangeRate_ := 3%N.
Definition tokenCap_ := 101%N.
Definition tokenMin_ := 78%N.

Definition bat_setup := BAT_Fixed.build_setup initSupply
                                        ethFund
                                        batFund
                                        fundingStart_
                                        fundingEnd_
                                        exchangeRate_
                                        tokenCap_
                                        tokenMin_.
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
    build_act creator (Blockchain.act_transfer ethFund 2);
    build_act creator (Blockchain.act_transfer batFund 2);
    build_act creator deploy_bat
  ]).

Module TestInfo <: BATGensInfo.
  Definition contract_addr := contract_base_addr.
  Definition accounts := [batFund; ethFund; person_1; person_2; person_3; person_4; person_5].
  Definition gAccount (c : Chain) := elems [batFund; ethFund; person_1; person_2;
                                            person_3; person_4; person_5].
  Definition bat_addr := batFund.
  Definition fund_addr := ethFund.
  Definition accounts_total_balance := 37%Z.
  Definition trace_length := 7.
End TestInfo.
Module MG := BATGens TestInfo. Import MG.

(* chain generator *)
Definition gTokenChain max_acts_per_block token_cb max_length :=
  let act_depth := 1 in
  gChain_full_sized token_cb
    (fun env act_depth => gBATAction env) max_length act_depth max_acts_per_block.

(* Generator for debugging Action generator *)
Definition gInvalidActions max_acts_per_block token_cb max_length g :=
  let act_depth := 1 in
  gInvalidAction token_cb
    (fun env act_depth => g env) max_length act_depth max_acts_per_block.

Definition forAllInvalidActions n g P :=
  let max_acts_per_block := 1 in
  forAll (gInvalidActions max_acts_per_block token_cb n g)
    (fun '(cb, acts) => if length acts =? 0
                        then checker true
                        else disjoin (map (fun act => P cb act) acts)).

Definition forAllTokenChainBuilders n :=
  let max_acts_per_block := 2 in
  forAllChainBuilder n token_cb (gTokenChain max_acts_per_block).

Definition forAllTokenBlocks n :=
  let max_acts_per_block := 2 in
  forAllChainState n token_cb (gTokenChain max_acts_per_block).

Definition forAllTokenChainStates n :=
  let max_acts_per_block := 2 in
  forAllChainState_ n token_cb (gTokenChain max_acts_per_block).

Definition pre_post_assertion_token P c Q :=
  let max_acts_per_block := 2 in
  let trace_length := 7 in
  pre_post_assertion_new trace_length token_cb (gTokenChain max_acts_per_block) BAT_Fixed.contract c P Q.

Definition reachableFrom_implication init_cb (P : ChainState -> bool) Q :=
  let P' := fun cs => if P cs then Some true else None in
  let Q' := fun _ pre_trace post_trace =>
    checker (fold_left (fun a (cs : ChainState) => a && (Q pre_trace cs) ) post_trace true) in
  let max_acts_per_block := 2%nat in
  let trace_length := 7%nat in
  reachableFrom_implies_chaintracePropSized trace_length init_cb
                                            (gTokenChain max_acts_per_block) P' Q'.

Notation "cb '~~>' pf" :=
  (reachableFrom_chaintrace cb (gTokenChain 2) pf) (at level 45, no associativity).
Notation "'{' lc '~~~>' pf1 '===>' pf2 '}'" :=
  (reachableFrom_implication lc pf1 pf2) (at level 90, left associativity).
Notation "'{{' P '}}'" := (forAllTokenChainStates 7 P) (at level 60, no associativity).
Notation "'{{' P '}}' '==>' '{{' Q '}}'" :=
  (forAllChainState_implication 7 token_cb (gTokenChain 2) P Q) (at level 60, left associativity).
Notation "'{{' P '}}' c '{{' Q '}}'" :=
  (pre_post_assertion_token P c Q) (at level 60, c at next level, no associativity).
Notation "f '|||' g" := (fun a b => (f a b) || (g a b)) (at level 10).
Notation "f '&&&' g" := (fun a => (f a) && (g a)) (at level 10).



(* Test generators *)

(* Sample generator to see quality of generated chains *)
(* Sample (gTokenChain 2 token_cb 7). *)

(* In BATTests.v we saw that there was a problem with refund actions
   sometimes not being valid even though they should be.
   We expect this problem to be fixed and therefore not get any invalid
   actions from the gBATActionValid generator *)
(* QuickChick (forAll (gInvalidActions 1 token_cb 7 gBATActionValid)
            (fun x => collect (snd x) true)). *)
(*
10000 :
+++ Passed 10000 tests (0 discards)
*)



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
  7023 : true
  2977 : false
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
  9954 : 9
  19 : 4
  11 : 5
  9 : 6
  3 : 7
  3 : 3
  1 : 1
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
  | Blockchain.act_transfer _ _ => false
  | Blockchain.act_deploy _ _ _ => false
  | Blockchain.act_call to _ msg =>
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
Fixpoint get_last_funding_state {from to} (trace : ChainTrace from to) 
                                (default : ChainState) : ChainState :=
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
   We do this to see it it possible to hit the funding cap
   and how easy it is to do. *)
(* QuickChick (forAllTokenChainBuilders 6 (fun cb => collect (get_chain_tokens cb) true)). *)
(*
  934 : 101
  887 : 86
  873 : 95
  852 : 83
  841 : 89
  802 : 92
  782 : 80
  751 : 98
  686 : 77
  559 : 71
  551 : 74
  451 : 68
  323 : 65
  283 : 62
  161 : 59
  99 : 56
  67 : 53
  50 : 50
  17 : 0
  15 : 47
  10 : 44
  4 : 41
  2 : 38
  +++ Passed 10000 tests (0 discards)
*)



Local Open Scope N_scope.

Definition fmap_subseteqb {A B} `{countable.Countable A}
                          (eqb : B -> B -> bool) (fmap : FMap A B) 
                          (fmap' : FMap A B) : bool :=
  let elements := FMap.elements fmap in
    fold_left (fun b elem => 
                match FMap.lookup (fst elem) fmap' with
                | Some v => b && (eqb (snd elem) v)
                | None => false
                end) elements true.

Definition fmap_eqb {A B} `{countable.Countable A}
                    (eqb : B -> B -> bool) (fmap : FMap A B) (fmap' : FMap A B) : bool :=
  (fmap_subseteqb eqb fmap fmap') || (fmap_subseteqb eqb fmap' fmap).

Definition fmap_filter_eqb {A B} `{countable.Countable A}
                           (excluded : list A) (eqb : B -> B -> bool) 
                           (fmap : FMap A B) (fmap' : FMap A B) : bool :=
  let map_filter m l := fold_left (fun map elem => FMap.remove elem map) l m in
  let fmap_filtered := map_filter fmap excluded in
  let fmap'_filtered := map_filter fmap' excluded in
    fmap_eqb eqb fmap_filtered fmap'_filtered.

Definition get_balance (state : BAT_Fixed.State) (addr : Address) :=
  with_default 0 (FMap.find addr (balances state)).

Definition msg_is_eip_msg (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | tokenMsg _ => true
  | _ => false
  end.

Definition msg_is_transfer (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer _ _) => true
  | _ => false
  end.

Definition msg_is_transfer_from (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer_from _ _ _) => true
  | _ => false
  end.

Definition msg_is_approve (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.approve _ _) => true
  | _ => false
  end.

Definition msg_is_create_tokens (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | create_tokens => true
  | _ => false
  end.

Definition msg_is_finalize (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | finalize => true
  | _ => false
  end.

Definition msg_is_refund (cstate : BAT_Fixed.State) (msg : BAT_Fixed.Msg) :=
  match msg with
  | refund => true
  | _ => false
  end.


(* Checker failing if amount in a contract call context is not zero *)
Definition amount_is_zero (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                          (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  (checker (cctx.(ctx_amount) =? 0)%Z).

(* Checker failing if amount in a contract call context is 0 or negative *)
Definition amount_is_positive (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                              (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  (checker (cctx.(ctx_amount) >? 0)%Z).

(* Checker failing if result_opt contains actions *)
Definition produces_no_actions (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                               (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (_, []), _) => checker true
  | _ => checker false
  end.

(* Checker failing if result_opt contains less than or more than one action *)
Definition produces_one_action (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                               (msg : Msg) (result_opt : option (State * list ActionBody)) :=
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
(* +++ Passed 10000 tests (0 discards) *)

(* Create_tokens should only accept calls with money in them *)
(* QuickChick (
  {{msg_is_create_tokens}}
  contract_base_addr
  {{amount_is_positive}}
). *)
(* +++ Passed 10000 tests (0 discards) *)

(* EIP messages and create_tokens should not produce any actions *)
(* QuickChick (
  {{msg_is_eip_msg ||| msg_is_create_tokens}}
  contract_base_addr
  {{produces_no_actions}}
). *)
(* +++ Passed 10000 tests (0 discards) *)

(* refund and finalize should produce an actions *)
(* QuickChick (
  {{msg_is_refund ||| msg_is_finalize}}
  contract_base_addr
  {{produces_one_action}}
). *)
(* +++ Passed 10000 tests (0 discards) *)

(* Chcker failing if any constants in BAT states are changed *)
Definition constants_unchanged (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                               (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), _) =>
    (* batFund and ethFund addresses should be constants *)
    let fund_deposit_check := address_eqb old_state.(fundDeposit) new_state.(fundDeposit) in
    let bat_deposit_check := address_eqb old_state.(batFundDeposit) new_state.(batFundDeposit) in
    (* Funding start block and end block should be constants *)
    let funding_start_check := Nat.eqb old_state.(fundingStart) new_state.(fundingStart) in
    let funding_end_check := Nat.eqb old_state.(fundingEnd) new_state.(fundingEnd) in
    (* Token exchange rate should be a constant *)
    let exchange_rate_check := N.eqb old_state.(tokenExchangeRate) new_state.(tokenExchangeRate) in
    (* Minimum and maximum token limits should be constants *)
    let creation_cap_check := N.eqb old_state.(tokenCreationCap) new_state.(tokenCreationCap) in
    let creation_min_check := N.eqb old_state.(tokenCreationMin) new_state.(tokenCreationMin) in
      checker (fund_deposit_check &&
               bat_deposit_check &&
               funding_start_check &&
               funding_end_check &&
               exchange_rate_check &&
               creation_cap_check &&
               creation_min_check)
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
Definition post_create_tokens_update_correct (chain : Chain) (cctx : ContractCallContext)
                                             (old_state : State) (msg : Msg)
                                             (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, []), create_tokens) =>
    let amount := cctx.(ctx_amount) in
    let from := cctx.(ctx_from) in
    (* The token balance of from should be increased by amount * exchangerate *)
    let balance_correct :=
      N.eqb (get_balance new_state from)
      ((get_balance old_state from) + (Z.to_N amount * old_state.(tokenExchangeRate))) in
    (* The total supply field should be increased by amount * exchangerate *)
    let total_supply_correct :=
      N.eqb (total_supply new_state)
      ((total_supply old_state) + (Z.to_N amount * old_state.(tokenExchangeRate))) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (balance_correct &&
              total_supply_correct))
  (* if 'receive' failed, or msg is not a create_tokens
     then just discard this test *)
  | _ => checker false
  end.
(* Create_tokens updates output correct *)
(* QuickChick ({{msg_is_create_tokens}} contract_base_addr {{post_create_tokens_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition create_tokens_valid (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                               (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), create_tokens) =>
    let from := cctx.(ctx_from) in
    let amount := cctx.(ctx_amount) in
    let current_slot := chain.(current_slot) in
    (* batFund should not be allowed to call create_tokens *)
    let from_valid := negb (address_eqb from batFund) in
    (* Create_tokens should only return some if amount is larger than zero *)
    let amount_valid := Z.leb 0 amount in
    (* Create_tokens should be callable if the token is not finalized *)
    let is_finalized_valid := negb old_state.(isFinalized) in
    (* Create_tokens should be callable if the current slot is in the funding period *)
    let slot_valid := (old_state.(fundingStart) <=? current_slot)%nat &&
                      (current_slot <=? old_state.(fundingEnd))%nat in
    (* Create_tokens should be callable with an amount that does not cause
        the total_supply to go over the max tokens cap *)
    let new_token_amount_valid := (total_supply old_state) + (Z.to_N amount * old_state.(tokenExchangeRate))
                                  <=? old_state.(tokenCreationCap) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (from_valid &&
              amount_valid &&
              is_finalized_valid &&
              slot_valid &&
              new_token_amount_valid))
  (* if 'receive' failed, or msg is not a create_tokens
     then just discard this test *)
  | _ => checker false
  end.
(* Create_tokens contract calls are valid *)
(* QuickChick ({{msg_is_create_tokens}} contract_base_addr {{create_tokens_valid}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_create_tokens_safe (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                                   (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), create_tokens) =>
    let from := cctx.(ctx_from) in
    (* Create_tokens should not change whether or not the token is finalized *)
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    (* Create_tokens should not change the allowances of any accounts *)
    let allowances_unchanged := fmap_eqb (fun fmap fmap' => fmap_eqb N.eqb fmap fmap')
                                (allowances old_state) (allowances new_state) in
    (* Create_tokens must only change the balance of the sender *)
    let other_balances_unchanged := fmap_filter_eqb [from] N.eqb
                                    (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (is_finalized_unchanged &&
              allowances_unchanged &&
              other_balances_unchanged))
  (* if 'receive' failed, or msg is not a create_tokens
     then just discard this test *)
  | _ => checker false
  end.
(* Create_tokens contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_create_tokens}} contract_base_addr {{post_create_tokens_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- finalize -------------------- *)
Definition post_finalize_update_correct (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                                        (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  (* finalize should produce a transfer action *)
  | (Some (new_state, [Blockchain.act_transfer to amount]), finalize) =>
    let contract_balance := cctx.(ctx_contract_balance) in
    (* If finalize returns some then if the token should be finalized *)
    let is_finalized_correct := Bool.eqb new_state.(isFinalized) true in
    (* The transfer action produced should transfer to the ethFund address *)
    let action_to_correct := address_eqb to ethFund in
    (* The transfer action produced should transfer the entire contract balance *)
    let action_amount_correct := Z.eqb amount contract_balance in
    let action_to_valid := negb (address_is_contract to) in
    let action_amount_valid := Z.leb amount contract_balance in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (is_finalized_correct &&
              action_to_correct &&
              action_amount_correct &&
              action_to_valid &&
              action_amount_valid))
  (* if 'receive' failed, or msg is not a finalize
     then just discard this test *)
  | _ => checker false
  end.
(* Finalize updates state correct and produces correct actions *)
(* QuickChick ({{msg_is_finalize}} contract_base_addr {{post_finalize_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition finalize_valid (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                          (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), finalize) =>
    let from := cctx.(ctx_from) in
    let amount := cctx.(ctx_amount) in
    let current_slot := chain.(current_slot) in
    (* Only ethFund should be allowed to call finalize *)
    let from_valid := address_eqb from ethFund in
    (* Finalization should only be allowed if contract not already finalized *)
    let is_finalized_valid := negb old_state.(isFinalized) in
    (* Finalization should only be allowed if funding period is over or we hit the token cap *)
    let can_finalize_valid := (old_state.(fundingEnd) <? current_slot)%nat ||
                              (N.eqb old_state.(tokenCreationCap) (total_supply old_state)) in
    (* Finalization should only be allowed if token amount
        is within valid (tokenCreationMin, tokenCreationCap) range *)
    let total_supply_valid := (N.leb old_state.(tokenCreationMin) (total_supply old_state)) &&
                              (N.leb (total_supply old_state) old_state.(tokenCreationCap)) in
    (* Finalize call must not be payable *)
    let amount_valid := Z.eqb amount 0 in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (from_valid &&
              is_finalized_valid &&
              can_finalize_valid &&
              total_supply_valid &&
              amount_valid))
  (* if 'receive' failed, or msg is not a finalize
     then just discard this test *)
  | _ => checker false
  end.
(* Finalize contract calls are valid *)
(* QuickChick ({{msg_is_finalize}} contract_base_addr {{finalize_valid}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_finalize_safe (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                              (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), finalize) =>
    (* Finalize should not change allowances *)
    let allowances_unchanged := fmap_eqb (fun fmap fmap' => fmap_eqb N.eqb fmap fmap')
                                (allowances old_state) (allowances new_state) in
    (* Finalize should not change balances *)
    let balances_unchanged := fmap_eqb N.eqb (balances old_state) (balances new_state) in
    (* Finalize should not change total_supply *)
    let total_supply_unchanged := N.eqb (total_supply old_state) (total_supply new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (allowances_unchanged &&
              balances_unchanged &&
              total_supply_unchanged))
  (* if 'receive' failed, or msg is not a finalize
     then just discard this test *)
  | _ => checker false
  end.
(* Finalize contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_finalize}} contract_base_addr {{post_finalize_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- refund -------------------- *)
Definition post_refund_update_correct (chain : Chain) (cctx : ContractCallContext)
                                      (old_state : State) (msg : Msg)
                                      (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, [Blockchain.act_transfer to amount]), refund) =>
    let from := cctx.(ctx_from) in
    let contract_balance := cctx.(ctx_contract_balance) in
    let from_bal_old := with_default 0 (FMap.find from (balances old_state)) in
    let from_bal_new := with_default 0 (FMap.find from (balances new_state)) in
    let eth_to_refund := Z.of_N (from_bal_old / (tokenExchangeRate old_state)) in
    (* Refund should subtract the refunded account balance from total_supply *)
    let total_supply_correct := N.eqb (total_supply old_state)
                                ((total_supply new_state) + from_bal_old) in
    (* Refund should set the refunded account balance to 0 *)
    let from_balance_correct := N.eqb from_bal_new 0 in
    (* Refund shoul pay the refunded account *)
    let action_to_correct := address_eqb from to in
    (* Refund should pay account_balance / exchange_rate *)
    let action_amount_correct := Z.eqb amount eth_to_refund in
    let action_to_valid := negb (address_is_contract to) in
    (* Contract should have enough money to refund *)
    let action_amount_valid := Z.leb amount contract_balance in
    whenFail (show old_state ++ nl ++ show cctx ++ nl ++ show result_opt)
    (checker (total_supply_correct &&
              from_balance_correct &&
              action_to_correct &&
              action_amount_correct &&
              action_to_valid &&
              action_amount_valid))
  (* if 'receive' failed, or msg is not a refund
     then just discard this test *)
  | _ => checker false
  end.
(* False property: Refund updates state correct and produces correct actions *)
(* QuickChick ({{msg_is_refund}} contract_base_addr {{post_refund_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition refund_valid (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                        (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), refund) =>
    let current_slot := chain.(current_slot) in
    let from := cctx.(ctx_from) in
    let amount := cctx.(ctx_amount) in
    let from_bal_old := with_default 0 (FMap.find from (balances old_state)) in
    (* Refund should only be allowed if contract not finalized *)
    let is_finalized_valid := negb old_state.(isFinalized) in
    (* Refund should only be allowed if funding period is over *)
    let current_slot_valid := (old_state.(fundingEnd) <? current_slot)%nat in
    (* Refund should only be allowed if contract did not hit minimum token goal *)
    let total_supply_valid := N.ltb (total_supply old_state) old_state.(tokenCreationMin) in
    (* Refund shoul only be allowed if sender has tokens *)
    let balance_valid := N.ltb 0 from_bal_old in
    (* Refund call must not be payable *)
    let amount_valid := Z.eqb amount 0 in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (is_finalized_valid &&
              current_slot_valid &&
              total_supply_valid &&
              balance_valid &&
              amount_valid))
  (* if 'receive' failed, or msg is not a refund
     then just discard this test *)
  | _ => checker false
  end.
(* Refund contract calls are valid *)
(* QuickChick ({{msg_is_refund}} contract_base_addr {{refund_valid}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_refund_safe (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                            (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), refund) =>
    let from := cctx.(ctx_from) in
    (* Refund should not change isFinalized *)
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    (* Refund should not change allowances *)
    let allowances_unchanged := fmap_eqb (fun fmap fmap' => fmap_eqb N.eqb fmap fmap')
                                  (allowances old_state) (allowances new_state) in
    (* Refund should not change other balances than the senders balance *)
    let other_balances_unchanged := fmap_filter_eqb [from] N.eqb
                                      (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (is_finalized_unchanged &&
              allowances_unchanged &&
              other_balances_unchanged))
  (* if 'receive' failed, or msg is not a refund
     then just discard this test *)
  | _ => checker false
  end.
(* Refund contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_refund}} contract_base_addr {{post_refund_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- transfer -------------------- *)
Definition post_transfer_update_correct (chain : Chain) (cctx : ContractCallContext)
                                        (old_state : State) (msg : Msg)
                                        (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, []), tokenMsg (EIP20Token.transfer to tokens)) =>
    let from := cctx.(ctx_from) in
    let from_balance_before := with_default 0 (FMap.find from (balances old_state)) in
    let to_balance_before := with_default 0 (FMap.find to (balances old_state)) in
    let from_balance_after := with_default 0 (FMap.find from (balances new_state)) in
    let to_balance_after := with_default 0 (FMap.find to (balances new_state)) in
    let from_to_same := address_eqb from to in
    (* Transfer must subtract the transfered tokens from the "from" address
        if the "from <> to" otherwise the balance should remain the same *)
    let from_balance_correct := if from_to_same
                                then (from_balance_before =? from_balance_after)
                                else (from_balance_before =? from_balance_after + tokens) in
    (* Transfer must add the transfered tokens from the "to" address
        if the "from <> to" otherwise the balance should remain the same *)
    let to_balance_correct :=   if from_to_same
                                then (to_balance_before =? to_balance_after)
                                else (to_balance_before + tokens =? to_balance_after) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (from_balance_correct &&
              to_balance_correct))
  (* if 'receive' failed, or msg is not a transfer
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer updates output correct *)
(* QuickChick ({{msg_is_transfer}} contract_base_addr {{post_transfer_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition transfer_valid (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                          (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer to tokens)) =>
    let from := cctx.(ctx_from) in
    let amount := cctx.(ctx_amount) in
    let from_balance_before := with_default 0 (FMap.find from (balances old_state)) in
    (* Transfer should only return some if "from" has enough tokens *)
    let from_balance_valid := N.leb tokens from_balance_before in
    (* Transfer call must not be payable *)
    let amount_valid := Z.eqb amount 0 in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (amount_valid &&
              from_balance_valid))
  (* if 'receive' failed, or msg is not a transfer
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer contract calls are valid *)
(* QuickChick ({{msg_is_transfer}} contract_base_addr {{transfer_valid}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_transfer_safe (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                              (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer to tokens)) =>
    let from := cctx.(ctx_from) in
    (* Transfer should not change the finalization state of the token *)
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    (* Transfer should not change the total supply of tokens *)
    let total_supply_unchanged := N.eqb (total_supply old_state) (total_supply new_state) in
    (* Transfer must not change the allowances of any account *)
    let allowances_unchanged := fmap_eqb (fun fmap fmap' => fmap_eqb N.eqb fmap fmap')
                                  (allowances old_state) (allowances new_state) in
    (* Transfer must only change the balance of from and to *)
    let other_balances_unchanged := fmap_filter_eqb [from; to] N.eqb
                                      (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (is_finalized_unchanged &&
              total_supply_unchanged &&
              allowances_unchanged &&
              other_balances_unchanged))
  (* if 'receive' failed, or msg is not a transfer
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_transfer}} contract_base_addr {{post_transfer_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- transfer_from -------------------- *)
Definition post_transfer_from_update_correct (chain : Chain) (cctx : ContractCallContext)
                                             (old_state : State) (msg : Msg)
                                             (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, []), tokenMsg (EIP20Token.transfer_from from to tokens)) =>
    let delegate := cctx.(ctx_from) in
    let from_balance_before := with_default 0 (FMap.find from (balances old_state)) in
    let to_balance_before := with_default 0 (FMap.find to (balances old_state)) in
    let from_balance_after := with_default 0 (FMap.find from (balances new_state)) in
    let to_balance_after := with_default 0 (FMap.find to (balances new_state)) in
    let delegate_allowance_before := with_default 0 (FMap.find delegate
      (with_default (@FMap.empty (FMap Address TokenValue) _)
                    (FMap.find from (allowances old_state)))) in
    let delegate_allowance_after := with_default 0 (FMap.find delegate
      (with_default (@FMap.empty (FMap Address TokenValue) _)
                    (FMap.find from (allowances new_state)))) in
    let from_to_same := address_eqb from to in
    (* Transfer_from must subtract the transfered tokens from the "from" address
        if the "from <> to" otherwise the balance should remain the same *)
    let from_balance_correct := if from_to_same
                                then (from_balance_before =? from_balance_after)
                                else (from_balance_before =? from_balance_after + tokens) in
    (* Transfer_from must add the transfered tokens to the "to" address
        if the "from <> to" otherwise the balance should remain the same *)
    let to_balance_correct :=   if from_to_same
                                then (to_balance_before =? to_balance_after)
                                else (to_balance_before + tokens =? to_balance_after) in
    (* Transfer_from must subtract the number of transfered tokens from the delegates allowance *)
    let delefate_allowance_correct := delegate_allowance_before =?
                                      delegate_allowance_after + tokens in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (from_balance_correct &&
              to_balance_correct &&
              delefate_allowance_correct))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer_from updates output correct *)
(* QuickChick ({{msg_is_transfer_from}} contract_base_addr {{post_transfer_from_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition transfer_from_valid (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                               (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer_from from to tokens)) =>
    let delegate := cctx.(ctx_from) in
    let amount := cctx.(ctx_amount) in
    let from_balance_before := with_default 0 (FMap.find from (balances old_state)) in
    let delegate_allowance_before := with_default 0 (FMap.find delegate
      (with_default (@FMap.empty (FMap Address TokenValue) _)
                    (FMap.find from (allowances old_state)))) in
    (* Transfer_from must only succeed if "from" has enough tokens *)
    let from_balance_valid := N.leb tokens from_balance_before in
    (* Transfer_from must only succeed if "delegate" is allowed
        to transfer the requested amount of tokens on behalf of "from" *)
    let delegate_allowance_valid := N.leb tokens delegate_allowance_before in
    (* Tranfer_from must not be payable*)
    let amount_valid := Z.eqb amount 0 in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (amount_valid &&
              from_balance_valid))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer_from contract calls are valid *)
(* QuickChick ({{msg_is_transfer_from}} contract_base_addr {{transfer_from_valid}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_transfer_from_safe (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                                   (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.transfer_from from to tokens)) =>
    let delegate := cctx.(ctx_from) in
    let from_allowances_before := with_default (@FMap.empty (FMap Address TokenValue) _)
                                               (FMap.find from (allowances old_state)) in
    let from_allowances_after := with_default (@FMap.empty (FMap Address TokenValue) _)
                                              (FMap.find from (allowances new_state)) in
    (* Transfer_from must not change the finalization state of the token *)
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    (* Transfer_from must not change the total supply of tokens *)
    let total_supply_unchanged := N.eqb (total_supply old_state) (total_supply new_state) in
    (* Transfer_from must not change the allowances of other accounts than from *)
    let other_allowances_unchanged := fmap_filter_eqb [from]
                                        (fun fmap fmap' => fmap_eqb N.eqb fmap fmap')
                                        (allowances old_state) (allowances new_state) in
    let other_allowance_unchanged := fmap_filter_eqb [delegate] N.eqb
                                      from_allowances_before from_allowances_after in
    (* Transfer_from must not change the balances of other accounts than from and to *)
    let other_balances_unchanged := fmap_filter_eqb [from; to] N.eqb
                                      (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (is_finalized_unchanged &&
              total_supply_unchanged &&
              other_allowances_unchanged &&
              other_allowance_unchanged &&
              other_balances_unchanged))
  (* if 'receive' failed, or msg is not a transfer_from
     then just discard this test *)
  | _ => checker false
  end.
(* Transfer_from contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_transfer_from}} contract_base_addr {{post_transfer_from_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- approve -------------------- *)
Definition post_approve_update_correct (chain : Chain) (cctx : ContractCallContext)
                                       (old_state : State) (msg : Msg)
                                       (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, []), tokenMsg (EIP20Token.approve delegate tokens)) =>
    let from := cctx.(ctx_from) in
    let delegate_allowance_after := with_default 0 (FMap.find delegate
      (with_default (@FMap.empty (FMap Address TokenValue) _)
                    (FMap.find from (allowances new_state)))) in
    (* Approve should update the allowance of "delegate" correctly *)
    let delefate_allowance_correct := delegate_allowance_after =? tokens in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker delefate_allowance_correct)
  (* if 'receive' failed, or msg is not a approve
     then just discard this test *)
  | _ => checker false
  end.
(* Approve updates output correct *)
(* QuickChick ({{msg_is_approve}} contract_base_addr {{post_approve_update_correct}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition approve_valid (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                         (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.approve delegate tokens)) =>
    let amount := cctx.(ctx_amount) in
    (* Approve must not be payable *)
    let amount_valid := Z.eqb amount 0 in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker amount_valid)
  (* if 'receive' failed, or msg is not a approve
     then just discard this test *)
  | _ => checker false
  end.
(* Approve contract calls are valid *)
(* QuickChick ({{msg_is_approve}} contract_base_addr {{approve_valid}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition post_approve_safe (chain : Chain) (cctx : ContractCallContext) (old_state : State)
                             (msg : Msg) (result_opt : option (State * list ActionBody)) :=
  match (result_opt, msg) with
  | (Some (new_state, _), tokenMsg (EIP20Token.approve delegate tokens)) =>
    let from := cctx.(ctx_from) in
    let from_allowances_before := with_default (@FMap.empty (FMap Address TokenValue) _)
                                               (FMap.find from (allowances old_state)) in
    let from_allowances_after := with_default (@FMap.empty (FMap Address TokenValue) _)
                                              (FMap.find from (allowances new_state)) in
    (* Approve must not change the finalization state of the token *)
    let is_finalized_unchanged := Bool.eqb old_state.(isFinalized) new_state.(isFinalized) in
    (* Transfer_from must not change the total supply of tokens *)
    let total_supply_unchanged := N.eqb (total_supply old_state) (total_supply new_state) in
    (* Transfer_from must not change the allowances of other accounts than "delegate" *)
    let other_allowances_unchanged := fmap_filter_eqb [from]
                                      (fun fmap fmap' => fmap_eqb N.eqb fmap fmap')
                                      (allowances old_state) (allowances new_state) in
    let other_allowance_unchanged := fmap_filter_eqb [delegate] N.eqb
                                      from_allowances_before from_allowances_after in
    (* Transfer_from must not change the balances of any accounts *)
    let balances_unchanged := fmap_eqb N.eqb (balances old_state) (balances new_state) in
    whenFail (show old_state ++ nl ++ show result_opt)
    (checker (is_finalized_unchanged &&
              total_supply_unchanged &&
              other_allowances_unchanged &&
              other_allowance_unchanged &&
              balances_unchanged))
  (* if 'receive' failed, or msg is not a approve
     then just discard this test *)
  | _ => checker false
  end.
(* Approve contract calls does not change anything they shouldnt *)
(* QuickChick ({{msg_is_approve}} contract_base_addr {{post_approve_safe}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- contract balance tests -------------------- *)
Definition contract_balance_lower_bound (cs : ChainState) :=
  let contract_balance := env_account_balances cs contract_base_addr in
  match get_contract_state State cs contract_base_addr with
  | Some cstate =>
    let is_finalized := cstate.(isFinalized) in
    let contract_balance_correct := Z.geb contract_balance
      (Z.of_N (((total_supply cstate) - initSupply) / cstate.(tokenExchangeRate))) in
      if is_finalized
      then checker true
      else checker contract_balance_correct
  | None => checker true
  end.
(* Contract balance should always be at least as big as the number of refundable tokens
    divided by the exhange rate unless the token was successfully funded.
   If this property does not hold then it implies that there can be cases where a user
    will not be able to get a refund should the funding fail.
   The number of refundable tokens is the total_supply - init_supply, i.e. all tokens created
    by users funding the project.
*)
(* QuickChick ({{contract_balance_lower_bound}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition contract_balance_lower_bound' (cs : ChainState) :=
  let contract_balance := env_account_balances cs contract_base_addr in
  match get_contract_state State cs contract_base_addr with
  | Some cstate =>
    let is_finalized := cstate.(isFinalized) in
    let bat_fund_balance := with_default 0 (FMap.find batFund (balances cstate)) in
    let contract_balance_correct := Z.geb contract_balance
      (Z.of_N (((total_supply cstate) - bat_fund_balance) / cstate.(tokenExchangeRate))) in
      if is_finalized
      then checker true
      else checker contract_balance_correct
  | None => checker true
  end.
(* Since the initial supply belonging to the batFund address is not supposed to be refundable
    we should have a stronger lower bound saying that the contract balance should always be
    at least as big as the (total_supply - batFund_balance) / exhange_rate
    unless the token was successfully funded.
   If this property does not hold but the previous property holds then it implies that
    there is a way that some of the initial supply can be refunded, which then it implies
    that there can be cases where a real user will not be able to get a refund should the funding fail.
*)
(* QuickChick ({{contract_balance_lower_bound'}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition partially_funded_cb :=
  ResultMonad.unpack_result (TraceGens.add_block (lcb_initial AddrSize)
  [
    build_act creator (Blockchain.act_transfer person_1 10);
    build_act creator (Blockchain.act_transfer person_2 7);
    build_act creator (Blockchain.act_transfer person_3 6);
    build_act creator (Blockchain.act_transfer person_4 10);
    build_act creator deploy_bat;
    build_act person_1 (Blockchain.act_call contract_base_addr 1
                                            ((@serialize BAT_Fixed.Msg _) create_tokens))
  ]).
Definition is_fully_refunded :=
  fun cs =>
    let contract_balance := env_account_balances cs contract_base_addr in
      match get_contract_state State cs contract_base_addr with
      | Some state => (negb state.(isFinalized)) &&
                      (state.(fundingEnd) <? cs.(current_slot))%nat &&
                      Z.eqb contract_balance 0
      | None => false
      end.
(* Check that it is possible to fully refund from a state
    where at least one token was created
    i.e. contract balance = 0 and token not funded.
   Note that this does not mean that the correct people got refunds
   the tests only states that all money put into the contract was
   refunded, i.e. no money get stuck in the contract *)
(* QuickChick (partially_funded_cb ~~> is_fully_refunded). *)
(*
Chain{|
Block 1 [
Action{act_from: 10%256, act_body: (act_transfer 11%256, 10)};
Action{act_from: 10%256, act_body: (act_transfer 12%256, 7)};
Action{act_from: 10%256, act_body: (act_transfer 13%256, 6)};
Action{act_from: 10%256, act_body: (act_transfer 14%256, 10)};
Action{act_from: 10%256, act_body: (act_deploy 0, transfer 19%256 17)};
Action{act_from: 11%256, act_body: (act_call 128%256, 1, create_tokens)}];
Block 2 [
Action{act_from: 13%256, act_body: (act_call 128%256, 1, create_tokens)};
Action{act_from: 11%256, act_body: (act_call 128%256, 4, create_tokens)}];
Block 3 [
Action{act_from: 14%256, act_body: (act_call 128%256, 5, create_tokens)};
Action{act_from: 14%256, act_body: (act_call 128%256, 1, create_tokens)}];
Block 4 [
Action{act_from: 11%256, act_body: (act_call 128%256, 2, create_tokens)};
Action{act_from: 12%256, act_body: (act_call 128%256, 6, create_tokens)}];
Block 5 [
Action{act_from: 11%256, act_body: (act_call 128%256, 1, create_tokens)};
Action{act_from: 11%256, act_body: (act_call 128%256, 2, create_tokens)}];
Block 6 [
Action{act_from: 13%256, act_body: (act_call 128%256, 0, refund)};
Action{act_from: 12%256, act_body: (act_call 128%256, 0, refund)}];
Block 7 [
Action{act_from: 14%256, act_body: (act_call 128%256, 0, refund)};
Action{act_from: 11%256, act_body: (act_call 128%256, 0, refund)}];|}

Success - found witness satisfying the predicate!
+++ Failed (as expected) after 42 tests and 0 shrinks. (0 discards)
*)

Definition can_always_fully_refund (cs : ChainState) :=
  let no_actions_from_contract :=
    fold_left (fun b action => b && (negb (address_is_contract (act_from action))))
              (chain_state_queue cs) true in
  let contract_balance := env_account_balances cs contract_base_addr in
  match get_contract_state State cs contract_base_addr with
  | Some cstate =>
    let bat_fund_balance := with_default 0 (FMap.find batFund (balances cstate)) in
    let contract_balance_correct := Z.leb (contract_balance * Z.of_N cstate.(tokenExchangeRate))
                                          (Z.of_N ((total_supply cstate) - bat_fund_balance)) in
      if no_actions_from_contract
      then
        if cstate.(isFinalized)
        then checker true
        else checker contract_balance_correct
      else checker true
  | None => checker true
  end.
(* Above we showed that it is possible to completely empty the contract balance,
    however the ideally it should always be possible to empty the contract balance.
   If not then it would mean that money could get stuck contract implying that some
    funded money may not be refundable.
   We know that all accounts except batFund should be able to refund so the amount of balance
    that we should be able to withdraw is the total number of tokens held by all accounts except
    for those held by batFund (initial supply).
   Thus if "contract_balance * exchange_rate <= total_supply - batFund_tokens" then it should be
    possible to withdraw the entire contract balance.
*)
(* QuickChick ({{can_always_fully_refund}}). *)
(* +++ Passed 10000 tests (0 discards) *)



(* -------------------- finalization tests -------------------- *)
Definition is_finalized cs :=
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
Action{act_from: 12%256, act_body: (act_call 128%256, 3, create_tokens)};
Action{act_from: 14%256, act_body: (act_call 128%256, 3, create_tokens)}];
Block 3 [
Action{act_from: 13%256, act_body: (act_call 128%256, 2, create_tokens)};
Action{act_from: 13%256, act_body: (act_call 128%256, 2, create_tokens)}];
Block 4 [
Action{act_from: 11%256, act_body: (act_call 128%256, 8, create_tokens)};
Action{act_from: 13%256, act_body: (act_call 128%256, 2, create_tokens)}];
Block 5 [
Action{act_from: 12%256, act_body: (act_call 128%256, 2, create_tokens)};
Action{act_from: 11%256, act_body: (act_call 128%256, 2, create_tokens)}];
Block 6 [
Action{act_from: 16%256, act_body: (act_call 128%256, 0, finalize)}];|}

Success - found witness satisfying the predicate!
+++ Failed (as expected) after 6 tests and 0 shrinks. (0 discards)
*)

Definition can_always_finalize check_setup :=
  let build_init_cb setup :=
    TraceGens.add_block (lcb_initial AddrSize)
    [
      build_act creator (Blockchain.act_transfer person_1 10);
      build_act creator (Blockchain.act_transfer person_2 7);
      build_act creator (Blockchain.act_transfer person_3 6);
      build_act creator (Blockchain.act_transfer person_4 10);
      build_act creator (create_deployment 0 BAT_Fixed.contract setup)
    ] in
  forAll gBATSetup
         (fun setup =>
            match (build_init_cb setup) with
            | ResultMonad.Ok init_cb => check_setup setup init_cb ==> (init_cb ~~> is_finalized)
            | ResultMonad.Err _ => false ==> true
            end).
(* We would like that BAToken has the property that it is
    always possible to successfully fund the token for any
    setup used when deploying the token *)
(*
Extract Constant defNumTests    => "100".
QuickChick (expectFailure (can_always_finalize (fun _ _ => true))).
Extract Constant defNumTests    => "10000".
*)

Definition final_is_final :=
  {token_cb ~~~> is_finalized ===> (fun _ cs => is_finalized cs)}.
(* Check that once finalized it cannot be undone *)
(* QuickChick final_is_final. *)
(* +++ Passed 10000 tests (4377 discards) *)

Definition can_only_finalize_once :=
  let chain_gen := (gTokenChain 2) token_cb 7%nat in
  let blocks cb := trace_states_step_block cb.(builder_trace) in
  let is_finalize action :=
    match action.(act_body) with
    | Blockchain.act_call _ _ ser_msg =>
      match @deserialize Msg _ ser_msg with
      | Some finalize => 1
      | _ => 0
      end
    | _ => 0
    end in
  let finalize_calls' block := fold_left (fun count action => count + is_finalize action)
                                         (chain_state_queue block) 0 in
  let finalize_calls blocks := fold_left (fun count block => count + finalize_calls' block)
                                         blocks 0 in
    forAll chain_gen (fun cb => checker (finalize_calls (blocks cb) <=? 1)).
(* Check that it is not possible to finalize more than once *)
(* QuickChick can_only_finalize_once. *)
(* +++ Passed 10000 tests (0 discards) *)


Definition final_implies_total_supply_in_range :=
  let total_supply_in_range cs :=
    match get_contract_state State cs contract_base_addr with
    | Some state => (tokenMin_ <=? (total_supply state)) &&
                    ((total_supply state) <=? tokenCap_)
    | None => false
    end in
  {token_cb ~~~> is_finalized ===> (fun _ cs => total_supply_in_range cs)}.
(* Check that once finalized then total supply of tokens is:
    1) at least _tokenMin
    2) no bigger than _tokenCap *)
(* QuickChick final_implies_total_supply_in_range. *)
(* +++ Passed 10000 tests (4234 discards) *)

Definition final_implies_total_supply_constant :=
  let get_satisfying_state trace := last trace empty_state in
  let get_total_supply cs :=
    match get_contract_state State cs contract_base_addr with
    | Some state => total_supply state
    | None => 0
    end in
  let finalized_total_supply trace := get_total_supply (get_satisfying_state trace) in
  {token_cb ~~~> is_finalized
            ===> (fun pre_trace cs => get_total_supply cs =? finalized_total_supply pre_trace)}.
(* Check that once finalized then total supply of tokens does not change *)
(* QuickChick final_implies_total_supply_constant. *)
(* +++ Passed 10000 tests (4092 discards) *)

Definition final_implies_contract_balance_is_zero :=
  let contract_balance_empty trace cs := Z.eqb (env_account_balances cs contract_base_addr) 0 in
  {token_cb ~~~> is_finalized ===> contract_balance_empty}.
(* Check that once finalized then the contract balance is 0 *)
(* QuickChick final_implies_contract_balance_is_zero. *)
(* +++ Passed 10000 tests (4147 discards) *)



(* -------------------- total_supply tests -------------------- *)
Definition total_supply_bounds (cs : ChainState) :=
  match get_contract_state State cs contract_base_addr with
  | Some cstate => checker ((initSupply <=? (total_supply cstate)) &&
                            ((total_supply cstate) <=? tokenCap_))
  | None => checker true
  end.
(* Check that total supply of tokens is always
    1) larger than or equal to the inital supply
    2) less than or equal to the funding cap
*)
(* QuickChick ({{total_supply_bounds}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition total_supply_eq_sum_balances (cs : ChainState) :=
  match get_contract_state State cs contract_base_addr with
  | Some cstate =>
    let balances_list := (map snd o FMap.elements) (balances cstate) in
    let balances_sum : N := fold_left N.add balances_list 0%N in
      checker ((total_supply cstate) =? balances_sum)
  | None => checker true
  end.
(* Check that total supply of tokens is always equal
    to the sum of all token balances *)
(* QuickChick ({{total_supply_eq_sum_balances}}). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition paid_tokens_modulo_exchange_rate (cs : ChainState) :=
  match get_contract_state State cs contract_base_addr with
  | Some cstate =>
      let paid_tokens := (total_supply cstate) - initSupply in
      if Nat.leb cs.(current_slot) fundingEnd_
      then checker (0 =? N.modulo paid_tokens exchangeRate_)
      else checker true
  | None => checker true
  end.
(* We check that the total supply of tokens minus the inital supply
    is a multiple of exchange rate. We have seen that this isn't the
    case when refunding is allowed, thus we only test this property
    in the funding period *)
(* QuickChick ({{paid_tokens_modulo_exchange_rate}}). *)
(* +++ Passed 10000 tests (0 discards) *)


