From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.BAT Require Import BATCommon.
From ConCert.Examples.BAT Require Import BATGens.
From ConCert.Examples.BAT Require Import BATPrinters.
From Coq Require Import List.
From Coq Require Import ZArith_base.
Import ListNotations.

Definition contract_base_addr := addr_of_Z 128%Z.
Definition ethFund : Address := addr_of_Z 16%Z.
Definition batFund : Address := addr_of_Z 17%Z.
Definition initSupply_ : N := 20%N.
Definition exchangeRate_ := 3%N.

Notation "f '|||' g" := (fun a b => (f a b) || (g a b)) (at level 10).
Notation "f '&&&' g" := (fun a => (f a) && (g a)) (at level 10).

(* Get value of isFinalized in last state of a chain *)
Definition get_chain_finalized (cb : ChainBuilder) : bool :=
  match get_contract_state BATCommon.State (builder_env cb) contract_base_addr with
  | Some state => state.(isFinalized)
  | None => true
  end.

(* Get chain length *)
Definition get_chain_height (cb : ChainBuilder) : nat :=
  (builder_env cb).(chain_height).

(* Check if an action is finalize *)
Definition action_is_finalize (action : Action) : bool :=
  match action.(act_body) with
  | Blockchain.act_transfer _ _ => false
  | Blockchain.act_deploy _ _ _ => false
  | Blockchain.act_call to _ msg =>
    if (address_eqb to contract_base_addr)
    then
      match @deserialize BATCommon.Msg _ msg with
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
      match @deserialize BATCommon.Msg _ msg with
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
  let cs := get_last_funding_state (builder_trace cb) empty_state in
  match get_contract_state BATCommon.State cs contract_base_addr with
  | Some state => (total_supply state)
  | None => 0%N
  end.

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
  (fmap_subseteqb eqb fmap fmap') && (fmap_subseteqb eqb fmap' fmap).

Definition fmap_filter_eqb {A B} `{countable.Countable A}
                           (excluded : list A) (eqb : B -> B -> bool)
                           (fmap : FMap A B) (fmap' : FMap A B) : bool :=
  let map_filter m l := fold_left (fun map elem => FMap.remove elem map) l m in
  let fmap_filtered := map_filter fmap excluded in
  let fmap'_filtered := map_filter fmap' excluded in
    fmap_eqb eqb fmap_filtered fmap'_filtered.

Definition get_balance (state : BATCommon.State) (addr : Address) :=
  with_default 0%N (FMap.find addr (balances state)).

Definition msg_is_eip_msg (cstate : BATCommon.State) (msg : BATCommon.Msg) :=
  match msg with
  | tokenMsg _ => true
  | _ => false
  end.

Definition msg_is_transfer (cstate : BATCommon.State) (msg : BATCommon.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer _ _) => true
  | _ => false
  end.

Definition msg_is_transfer_from (cstate : BATCommon.State) (msg : BATCommon.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.transfer_from _ _ _) => true
  | _ => false
  end.

Definition msg_is_approve (cstate : BATCommon.State) (msg : BATCommon.Msg) :=
  match msg with
  | tokenMsg (EIP20Token.approve _ _) => true
  | _ => false
  end.

Definition msg_is_create_tokens (cstate : BATCommon.State) (msg : BATCommon.Msg) :=
  match msg with
  | create_tokens => true
  | _ => false
  end.

Definition msg_is_finalize (cstate : BATCommon.State) (msg : BATCommon.Msg) :=
  match msg with
  | finalize => true
  | _ => false
  end.

Definition msg_is_refund (cstate : BATCommon.State) (msg : BATCommon.Msg) :=
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

Definition no_transfers_from_bat_fund (cs : ChainState) : bool :=
  match (chain_state_queue cs) with
  | [] => true
  | act :: _ =>
    match act.(act_body) with
    | Blockchain.act_call _ _ ser_msg =>
      match @deserialize Msg _ ser_msg with
      | Some (tokenMsg (EIP20Token.transfer _ _)) => address_neqb act.(act_from) batFund
      | Some (tokenMsg (EIP20Token.transfer_from from _ _)) => address_neqb from batFund
      | _ => true
      end
    | _ => true
    end
  end.

Definition no_batfund_create_tokens (cs : ChainState) : bool :=
  match (chain_state_queue cs) with
  | [] => true
  | act :: _ =>
    match act.(act_body) with
    | Blockchain.act_call _ _ ser_msg =>
      match @deserialize Msg _ ser_msg with
      | Some (create_tokens) => address_neqb act.(act_from) batFund
      | _ => true
      end
    | _ => true
    end
  end.

Definition no_transfers_to_batfund (cs : ChainState) : bool :=
  match (chain_state_queue cs) with
  | [] => true
  | act :: _ =>
    match act.(act_body) with
    | Blockchain.act_call _ _ ser_msg =>
      match @deserialize Msg _ ser_msg with
      | Some (tokenMsg (EIP20Token.transfer to _)) =>
          address_neqb to batFund
      | Some (tokenMsg (EIP20Token.transfer_from _ to _)) =>
          address_neqb to batFund
      | _ => true
      end
    | _ => true
    end
  end.

Definition is_fully_refunded :=
  fun cs =>
    let contract_balance := env_account_balances cs contract_base_addr in
      match get_contract_state State cs contract_base_addr with
      | Some state => (negb state.(isFinalized)) &&
                      (state.(fundingEnd) <? cs.(current_slot))%nat &&
                      Z.eqb contract_balance 0
      | None => false
      end.

Definition only_transfers_modulo_exhange_rate (cs : ChainState) : bool :=
  match (chain_state_queue cs) with
  | [] => true
  | act :: _ =>
    match act.(act_body) with
    | Blockchain.act_call _ _ ser_msg =>
      match @deserialize Msg _ ser_msg with
      | Some (tokenMsg (EIP20Token.transfer _ amount)) =>
          N.eqb 0 (N.modulo amount exchangeRate_)
      | Some (tokenMsg (EIP20Token.transfer_from _ _ amount)) =>
          N.eqb 0 (N.modulo amount exchangeRate_)
      | _ => true
      end
    | _ => true
    end
  end.

Definition funding_period_not_over (setup : Setup) cb :=
  let current_slot := S (current_slot (env_chain cb)) in
    Nat.leb current_slot setup.(_fundingEnd).

Definition funding_period_non_empty (setup : Setup) :=
  Nat.leb setup.(_fundingStart) setup.(_fundingEnd).

Definition initial_supply_le_cap (setup : Setup) :=
  N.leb setup.(_batFund) setup.(_tokenCreationCap).

Definition exchange_rate_non_zero (setup : Setup) :=
  N.ltb 0 setup.(_tokenExchangeRate).

Definition is_finalized cs :=
  match get_contract_state State cs contract_base_addr with
  | Some state => state.(isFinalized)
  | None => false
  end.
