(** * Dexter 2 FA1.2 Liquidity token contract *)
(** This file contains an implementation of Dexter2 liquidity contract
    https://gitlab.com/dexter2tz/dexter2tz/-/blob/1cec9d9333eba756603d6cd90ea9c70d482a5d3d/lqt_fa12.mligo
    In addition this file contains proof of functional correctness w.r.t the
    informal specification https://gitlab.com/dexter2tz/dexter2tz/-/blob/1cec9d9333eba756603d6cd90ea9c70d482a5d3d/docs/informal-spec/dexter2-lqt-fa12.md

    This contract is an extension of a basic FA1.2 token contract with
    an extra entrypoint that allows an admin to mint and burn tokens.
    It is used in the Dexter2 exchange paired with an instance of the
    Dexter2 CPMM contract. The purpose of this contract is to keep track
    of ownership of the exchanges funds. A user who owns x% of the supply
    of liquidity tokens owns x% of the exchanges trading reserve.
*)
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import InterContractCommunication.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.

Definition non_zero_amount (amt : Z) : bool := (0 <? amt)%Z.

(** * Contract types *)

Section LQTFA12Types.
  Context {BaseTypes : ChainBase}.
  Open Scope N_scope.
  Set Nonrecursive Elimination Schemes.

  (* Dummy implementation of callbacks. *)
  Record callback := {
    return_addr : Address;
  }.

  Definition callback_addr (c : callback)
                           : Address :=
    c.(return_addr).
  Coercion callback_addr : callback >-> Address.

  Record transfer_param :=
    build_transfer_param {
      from : Address;
      to : Address;
      value : N
  }.

  Record approve_param :=
    build_approve_param {
      spender : Address;
      value_ : N
  }.

  Record mintOrBurn_param :=
    build_mintOrBurn_param {
      quantity : Z;
      target : Address
  }.

  Record getAllowance_param :=
    build_getAllowance_param {
      request : (Address * Address);
      allowance_callback : callback
  }.

  Record getBalance_param :=
    build_getBalance_param {
      owner_ : Address;
      balance_callback : callback
  }.

  Record getTotalSupply_param :=
    build_getTotalSupply_param {
      request_ : unit;
      supply_callback : callback
  }.

  Record State :=
    build_state {
      tokens : FMap Address N;
      allowances : FMap (Address * Address) N;
      admin : Address;
      total_supply : N
  }.

  Record Setup :=
    build_setup {
      admin_ : Address;
      lqt_provider : Address;
      initial_pool : N
  }.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (* Any contract that wants to receive callback messages from the FA1.2 liquidity contract
    should have this type as its Msg type. The contract may have other endpoints,
    as composed in the 'other_msg' constructor. *)
  Inductive FA12ReceiverMsg {Msg' : Type} :=
  | receive_allowance : N -> FA12ReceiverMsg
  | receive_balance_of : N -> FA12ReceiverMsg
  | receive_total_supply : N -> FA12ReceiverMsg
  | other_msg : Msg' -> FA12ReceiverMsg.

  (* Liquidity FA1.2 Endpoints. *)
  Inductive Msg :=
  | msg_transfer : transfer_param -> Msg
  | msg_approve : approve_param -> Msg
  | msg_mint_or_burn : mintOrBurn_param -> Msg
  | msg_get_allowance : getAllowance_param -> Msg
  | msg_get_balance : getBalance_param -> Msg
  | msg_get_total_supply : getTotalSupply_param -> Msg.

  (* begin hide *)
  MetaCoq Run (make_setters transfer_param).
  MetaCoq Run (make_setters approve_param).
  MetaCoq Run (make_setters mintOrBurn_param).
  MetaCoq Run (make_setters getAllowance_param).
  MetaCoq Run (make_setters getBalance_param).
  MetaCoq Run (make_setters getTotalSupply_param).
  MetaCoq Run (make_setters State).
  MetaCoq Run (make_setters Setup).
  (* end hide *)

  Definition mintedOrBurnedTokens (msg : option Msg) : Z :=
    match msg with
    | Some (msg_mint_or_burn param) => param.(quantity)
    | _ => 0
    end.

  Class LqtTokenInterface
        `{Serializable State}
        `{Serializable Msg}
        `{Serializable Setup} :=
    { lqt_contract : Contract Setup Msg State Error;

      lqt_total_supply_correct :
      forall (bstate : ChainState) (caddr : Address)
        (trace : ChainTrace empty_state bstate),
        env_contracts bstate caddr = Some (lqt_contract : WeakContract) ->
        exists (cstate : State) (depinfo : DeploymentInfo Setup)
          (inc_calls : list (ContractCallInfo Msg)),
            contract_state bstate caddr = Some cstate /\
            deployment_info Setup trace caddr = Some depinfo /\
            incoming_calls Msg trace caddr = Some inc_calls /\
            (let initial_tokens := initial_pool (deployment_setup depinfo) in
            Z.of_N (total_supply cstate) =
              (Z.of_N initial_tokens +
                  sumZ (fun callInfo => mintedOrBurnedTokens (call_msg callInfo))
                      (filter (callFrom (admin cstate)) inc_calls))%Z) }.

End LQTFA12Types.

Module Type Dexter2LqtSerializable.
  Section D2LqtSerializable.

    Context `{ChainBase}.

    Axiom callback_serializable : Serializable callback.

    Axiom transfer_param_serializable : Serializable transfer_param.

    Axiom approve_param_serializable : Serializable approve_param.

    Axiom mintOrBurn_param_serializable : Serializable mintOrBurn_param.

    Axiom getAllowance_param_serializable : Serializable getAllowance_param.

    Axiom getBalance_param_serializable : Serializable getBalance_param.

    Axiom getTotalSupply_param_serializable : Serializable getTotalSupply_param.

    Axiom FA12ReceiverMsg_serializable : forall {Msg : Type} `{Serializable Msg}, Serializable (@FA12ReceiverMsg Msg).

    Axiom msg_serializable : Serializable Msg.

    Axiom state_serializable : Serializable State.

    Axiom setup_serializable : Serializable Setup.

  End D2LqtSerializable.
End Dexter2LqtSerializable.

Module D2LqtSInstances <: Dexter2LqtSerializable.
  Section Serialization.
    Context `{ChainBase}.

    Instance callback_serializable : Serializable callback :=
    Derive Serializable callback_rect <Build_callback>.

    Instance transfer_param_serializable : Serializable transfer_param :=
      Derive Serializable transfer_param_rect <build_transfer_param>.

    Instance approve_param_serializable : Serializable approve_param :=
      Derive Serializable approve_param_rect <build_approve_param>.

    Instance mintOrBurn_param_serializable : Serializable mintOrBurn_param :=
      Derive Serializable mintOrBurn_param_rect <build_mintOrBurn_param>.

    Instance getAllowance_param_serializable : Serializable getAllowance_param :=
      Derive Serializable getAllowance_param_rect <build_getAllowance_param>.

    Instance getBalance_param_serializable : Serializable getBalance_param :=
      Derive Serializable getBalance_param_rect <build_getBalance_param>.

    Instance getTotalSupply_param_serializable : Serializable getTotalSupply_param :=
      Derive Serializable getTotalSupply_param_rect <build_getTotalSupply_param>.

    Instance FA12ReceiverMsg_serializable {Msg : Type}
                                         `{Serializable Msg}
                                          : Serializable (@FA12ReceiverMsg Msg) :=
      Derive Serializable (@FA12ReceiverMsg_rect Msg) <
        (@receive_allowance Msg),
        (@receive_balance_of Msg),
        (@receive_total_supply Msg),
        (@other_msg Msg)>.

    Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <msg_transfer,
                                  msg_approve,
                                  msg_mint_or_burn,
                                  msg_get_allowance,
                                  msg_get_balance,
                                  msg_get_total_supply>.

    Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

    Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.
  End Serialization.
End D2LqtSInstances.



(** * Contract functions *)
Module Dexter2Lqt (SI : Dexter2LqtSerializable).
  Import SI.

  (* begin hide *)
  #[global] Existing Instance callback_serializable.
  #[global] Existing Instance transfer_param_serializable.
  #[global] Existing Instance approve_param_serializable.
  #[global] Existing Instance mintOrBurn_param_serializable.
  #[global] Existing Instance getAllowance_param_serializable.
  #[global] Existing Instance getBalance_param_serializable.
  #[global] Existing Instance getTotalSupply_param_serializable.
  #[global] Existing Instance FA12ReceiverMsg_serializable.
  #[global] Existing Instance msg_serializable.
  #[global] Existing Instance state_serializable.
  #[global] Existing Instance setup_serializable.
  (* end hide *)

  Section DexterLqtDefs.
    Context `{BaseTypes : ChainBase}.
    Open Scope N_scope.

    Definition find_allowance (k : Address * Address)
                              (m : FMap (Address * Address) N)
                              : option N :=
      FMap.find k m.

    Definition update_allowance (k : Address * Address)
                                (val : option N)
                                (m : FMap (Address * Address) N)
                                : FMap (Address * Address) N :=
      FMap.update k val m.

    Definition empty_allowance : FMap (Address * Address) N :=
      FMap.empty.

    (** ** Transfer *)
    (** Transfers [amount] tokens, if [from] has enough tokens to transfer
        and [sender] is allowed to send that much on behalf of [from] *)
    Definition try_transfer (sender : Address)
                            (param : transfer_param)
                            (state : State)
                            : result State Error :=
      let allowances_ := state.(allowances) in
      let tokens_ := state.(tokens) in
      do allowances_ <- (* Update allowances *)
        (if address_eqb sender param.(from)
        then Ok allowances_
        else
          let allowance_key := (param.(from), sender) in
          let authorized_value := with_default 0 (find_allowance allowance_key allowances_) in
            do _ <- throwIf (authorized_value <? param.(value)) default_error; (* NotEnoughAllowance *)
            Ok (update_allowance allowance_key (maybe (authorized_value - param.(value))) allowances_)
        ) ;
      do tokens_ <- (* Update from balance *)
        (let from_balance := with_default 0 (AddressMap.find param.(from) tokens_) in
          do _ <- throwIf (from_balance <? param.(value)) default_error; (* NotEnoughBalance *)
          Ok (AddressMap.update param.(from) (maybe (from_balance - param.(value))) tokens_)
        ) ;
      let tokens_ :=
        let to_balance := with_default 0 (AddressMap.find param.(to) tokens_) in
          AddressMap.update param.(to) (maybe (to_balance + param.(value))) tokens_ in
        Ok (state<|tokens := tokens_|>
                  <|allowances := allowances_|>).

    (** ** Approve *)
    (** The caller approves the [spender] to transfer up to [amount] tokens on behalf of the [sender] *)
    Definition try_approve (sender : Address)
                           (param : approve_param)
                           (state : State)
                           : result State Error :=
      let allowances_ := state.(allowances) in
      let allowance_key := (sender, param.(spender)) in
      let previous_value := with_default 0 (find_allowance allowance_key allowances_) in
      do _ <- throwIf (andb (0 <? previous_value) (0 <? param.(value_))) default_error; (* UnsafeAllowanceChange *)
      let allowances_ := update_allowance allowance_key (maybe param.(value_)) allowances_ in
        Ok (state<|allowances := allowances_|>).

    (** ** Mint or burn *)
    (** If [quantity] is positive
        then creates [quantity] tokens and gives them to [target]
        else removes [quantity] tokens from [target].
        Can only be called by [admin] *)
    Definition try_mint_or_burn (sender : Address)
                                (param : mintOrBurn_param)
                                (state : State)
                                : result State Error :=
      do _ <- throwIf (address_neqb sender state.(admin)) default_error;
      let tokens_ := state.(tokens) in
      let old_balance := with_default 0 (AddressMap.find param.(target) tokens_) in
      let new_balance := (Z.of_N old_balance + param.(quantity))%Z in
      do _ <- throwIf (new_balance <? 0)%Z default_error; (* Cannot burn more than the target's balance. *)
      let tokens_ := AddressMap.update param.(target) (maybe (Z.to_N new_balance)) tokens_ in
      let total_supply_ := Z.abs_N (Z.of_N state.(total_supply) + param.(quantity))%Z in
        Ok (state<|tokens := tokens_|>
                  <|total_supply := total_supply_|>).

    Definition mk_callback (to_addr : Address)
                           (msg : @FA12ReceiverMsg unit)
                           : ActionBody :=
      act_call to_addr 0 (serialize msg).

    Definition receive_allowance_ n := @receive_allowance unit n.
    Definition receive_balance_of_ n := @receive_balance_of unit n.
    Definition receive_total_supply_ n := @receive_total_supply unit n.

    (** ** Get allowance *)
    (** Get the quantity that [snd request] is allowed to spend on behalf of [fst request] *)
    Definition try_get_allowance (sender : Address)
                                 (param : getAllowance_param)
                                 (state : State)
                                 : list ActionBody :=
      let value := with_default 0 (find_allowance param.(request) state.(allowances)) in
        [mk_callback param.(allowance_callback) (receive_allowance_ value)].

    (** ** Get balance *)
    (** Get the quantity of tokens belonging to [owner] *)
    Definition try_get_balance (sender : Address)
                               (param : getBalance_param)
                               (state : State)
                               : list ActionBody :=
      let value := with_default 0 (AddressMap.find param.(owner_) state.(tokens)) in
        [mk_callback param.(balance_callback) (receive_balance_of_ value)].

    (** ** Get total supply *)
    (** Get the total supply of tokens *)
    Definition try_get_total_supply (sender : Address)
                                    (param : getTotalSupply_param)
                                    (state : State)
                                    : list ActionBody :=
      let value := state.(total_supply) in
        [mk_callback param.(supply_callback) (receive_total_supply_ value)].

    (** ** Init *)
    (** Initalize contract storage *)
    Definition init_lqt (chain : Chain)
                        (ctx : ContractCallContext)
                        (setup : Setup)
                        : result State Error :=
      Ok {|
        tokens := AddressMap.add setup.(lqt_provider)
                                 setup.(initial_pool)
                                 AddressMap.empty;
        allowances := empty_allowance;
        admin := setup.(admin_);
        total_supply := setup.(initial_pool);
      |}.

    (** ** Receive *)
    (** Contract main entrypoint *)
    Open Scope Z_scope.
    Definition receive_lqt (chain : Chain)
                          (ctx : ContractCallContext)
                          (state : State)
                          (maybe_msg : option Msg)
                          : result (State * list ActionBody) Error :=
      let sender := ctx.(ctx_from) in
      let without_statechange acts := Ok (state, acts) in
      do _ <- throwIf (non_zero_amount ctx.(ctx_amount)) default_error; (* DontSendTez *)
      match maybe_msg with
      | Some (msg_transfer param) =>
          without_actions (try_transfer sender param state)
      | Some (msg_approve param) =>
          without_actions (try_approve sender param state)
      | Some (msg_mint_or_burn param) =>
          without_actions (try_mint_or_burn sender param state)
      | Some (msg_get_allowance param) =>
          without_statechange (try_get_allowance sender param state)
      | Some (msg_get_balance param) =>
          without_statechange (try_get_balance sender param state)
      | Some (msg_get_total_supply param) =>
          without_statechange (try_get_total_supply sender param state)
      (* Transfer actions to this contract are not allowed *)
      | None => Err default_error
      end.
    Close Scope Z_scope.

    Definition contract : Contract Setup Msg State Error :=
      build_contract init_lqt receive_lqt.

  End DexterLqtDefs.
End Dexter2Lqt.

Module DEX2LQT := Dexter2Lqt D2LqtSInstances.
