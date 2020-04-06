Module FA2ClientContract.
From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface.
From ConCert Require Import Serializable.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import ZArith.
Import ListNotations.
Import RecordSetNotations.

Section FA2Client.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Inductive FA2ClientMsg :=
  | Call_fa2_is_operator : is_operator_param -> FA2ClientMsg 
  | Call_fa2_balance_of_param : list balance_of_response -> FA2ClientMsg
  | Call_fa2_total_supply_param : list total_supply_response -> FA2ClientMsg
  | Call_fa2_metadata_callback : list token_metadata -> FA2ClientMsg
  | Call_fa2_permissions_descriptor : permissions_descriptor -> FA2ClientMsg.

Global Instance FA2ClientMsg_serializable : Serializable FA2ClientMsg :=
  Derive Serializable FA2ClientMsg_rect <
    Call_fa2_is_operator, 
    Call_fa2_balance_of_param, 
    Call_fa2_total_supply_param,
    Call_fa2_metadata_callback,
    Call_fa2_permissions_descriptor>.

Definition ClientMsg := @FA2ReceiverMsg BaseTypes FA2ClientMsg _.

Record State := 
  build_state {
  fa2_caddr : Address;
  bit : N;
}.

Record Setup := 
  build_setup {
  fa2_caddr_ : Address
}.

Instance state_settable : Settable _ :=
  settable! build_state <fa2_caddr; bit>.
Instance setup_settable : Settable _ :=
  settable! build_setup <fa2_caddr_>.

Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance state_serializable : Serializable State :=
	Derive Serializable State_rect <build_state>.

Global Instance ClientMsg_serializable : Serializable ClientMsg := FA2Token.FA2ReceiverMsg_serializable.

End Serialization.
  
Definition init (chain : Chain)
								(ctx : ContractCallContext)
								(setup : Setup) : option State := 
  Some {|
    fa2_caddr := setup.(fa2_caddr_);
    bit := 0;
	|}.

Definition receive (chain : Chain)
						 			 (ctx : ContractCallContext)
									 (state : State)
									 (maybe_msg : option ClientMsg)
									 : option (State * list ActionBody) :=
	match maybe_msg with
  | Some (receive_is_operator is_op_response) => Some (state<| bit:= 42|>, [])
  | Some (other_msg (Call_fa2_is_operator is_op_param)) => 
      Some (state<| bit := 2|>, [act_call state.(fa2_caddr) 0%Z (@serialize FA2Token.Msg _ (FA2Token.msg_is_operator is_op_param))])
  | _ => None 
	end.

Ltac solve_contract_proper :=
  repeat
    match goal with
    | [|- ?x _  = ?x _] => unfold x
    | [|- ?x _ _ = ?x _ _] => unfold x
    | [|- ?x _ _ _ = ?x _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ _ = ?x _ _ _ _ _] => unfold x
    | [|- Some _ = Some _] => f_equal
    | [|- pair _ _ = pair _ _] => f_equal
    | [|- (if ?x then _ else _) = (if ?x then _ else _)] => destruct x
    | [|- match ?x with | _ => _ end = match ?x with | _ => _ end ] => destruct x
    | [H: ChainEquiv _ _ |- _] => rewrite H in *
    | _ => subst; auto
    end.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) FA2Client.init.
Proof. repeat intro; solve_contract_proper.	Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) FA2Client.receive.
Proof. repeat intro; solve_contract_proper. Qed.

Definition contract : Contract FA2Client.Setup ClientMsg FA2Client.State :=
  build_contract FA2Client.init init_proper FA2Client.receive receive_proper.

End FA2Client.
End FA2ClientContract.

Module FA2TransferHookContract.
(* A contract which implements the transfer hook endpoint of FA2 *)
(* Behavior is driven by a permission policy *)

From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface.
From ConCert Require Import Serializable.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import ZArith.
Import ListNotations.
Import RecordSetNotations.

Section FA2TransferHook.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Inductive FA2TransferHookMsg :=
  | set_permission_policy : permissions_descriptor -> FA2TransferHookMsg.

Global Instance FA2TransferHookMsg_serializable : Serializable FA2TransferHookMsg :=
  Derive Serializable FA2TransferHookMsg_rect <
    set_permission_policy>.

Definition Msg := @FA2TransferHook BaseTypes FA2TransferHookMsg _.

Record State := 
  build_state {
    owner : Address;
    fa2_caddr : Address;
    policy : permissions_descriptor;
}.

Record Setup := 
  build_setup {
    fa2_caddr_ : Address;
    policy_ : permissions_descriptor;
}.

Instance state_settable : Settable _ :=
  settable! build_state <owner; fa2_caddr; policy>.
Instance setup_settable : Settable _ :=
  settable! build_setup <fa2_caddr_; policy_>.

Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance state_serializable : Serializable State :=
	Derive Serializable State_rect <build_state>.

End Serialization.
  
Definition init (chain : Chain)
								(ctx : ContractCallContext)
								(setup : Setup) : option State := 
  Some {|
    owner := ctx.(ctx_from);
    fa2_caddr := setup.(fa2_caddr_);
    policy := setup.(policy_);
	|}.

Definition returnIf (cond : bool) := if cond then None else Some tt.

Definition check_transfer_permissions (tr : transfer_descriptor)
                                      (operator : Address)
                                      (state : State) 
                                      : option unit :=
  if (address_eqb tr.(transfer_descr_from_) operator)
  then if (FA2Token.policy_disallows_self_transfer state.(policy))
    then None 
    else Some tt
  else if (FA2Token.policy_disallows_operator_transfer state.(policy))
    then None
    else Some tt.

(* called whenever this hook receives a transfer from the FA2 contract *)
(* checks the permission policy, and if all transfers are valid, 
   forwards the transfers to the 'msg_receive_hook_transfer' endpoint of the FA2 Contract *)
Definition on_hook_receive_transfer (caller : Address)
                                    (param : transfer_descriptor_param)
                                    (state : State)
                                    : option (list ActionBody) :=
  do _ <- returnIf (negb (address_eqb caller state.(fa2_caddr))) ;
  do _ <- returnIf (negb (address_eqb param.(transfer_descr_fa2) state.(fa2_caddr))) ;
  let operator := param.(transfer_descr_operator) in
  let check_transfer_iterator tr acc :=
    do _ <- check_transfer_permissions tr operator state ;
    Some tt in
  (* check if all transfers satisfy the permission policy. If at least one does not, the whole operation fails *)
  do _ <- fold_right check_transfer_iterator (Some tt) param.(transfer_descr_batch) ;
  (* send out transfer action *)
  let msg := serialize (msg_receive_hook_transfer param) in
  ret [(act_call caller 0%Z msg)].

Definition try_update_permission_policy (caller : Address)
                                    (new_policy : permissions_descriptor)
                                    (state : State)
                                    : (option State) :=
  do _ <- returnIf (negb (address_eqb caller state.(owner))) ;
  ret (state<| policy := new_policy |>).

Definition receive (chain : Chain)
						 			 (ctx : ContractCallContext)
									 (state : State)
									 (maybe_msg : option Msg)
                   : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
	let without_statechange := option_map (fun acts => (state, acts)) in
  match maybe_msg with
  | Some (transfer_hook param) => without_statechange (on_hook_receive_transfer sender param state)
  | Some (hook_other_msg (set_permission_policy policy)) => without_actions (try_update_permission_policy sender policy state)
  | _ => None 
	end.

Ltac solve_contract_proper :=
  repeat
    match goal with
    | [|- ?x _  = ?x _] => unfold x
    | [|- ?x _ _ = ?x _ _] => unfold x
    | [|- ?x _ _ _ = ?x _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ _ = ?x _ _ _ _ _] => unfold x
    | [|- Some _ = Some _] => f_equal
    | [|- pair _ _ = pair _ _] => f_equal
    | [|- (if ?x then _ else _) = (if ?x then _ else _)] => destruct x
    | [|- match ?x with | _ => _ end = match ?x with | _ => _ end ] => destruct x
    | [H: ChainEquiv _ _ |- _] => rewrite H in *
    | _ => subst; auto
    end.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) FA2TransferHook.init.
Proof. repeat intro; solve_contract_proper.	Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) FA2TransferHook.receive.
Proof. repeat intro; solve_contract_proper. Qed.

Definition contract : Contract Setup Msg State :=
  build_contract FA2TransferHook.init init_proper FA2TransferHook.receive receive_proper.

End FA2TransferHook.
End FA2TransferHookContract.

Global Set Warnings "-extraction-logical-axiom".
Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import Containers.
From ConCert Require Import FA2Token FA2Interface.
From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Require Import Extras.

From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters TraceGens FA2Printers SerializablePrinters.
(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List Int.
Import BoundedN.Stdpp.
Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.


Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.
Let BaseTypes := ChainGens.LocalChainBase.
Import FA2ClientContract.
Import FA2TransferHookContract.
(* Section Printers. *)
Local Open Scope string_scope.

Instance showFA2ClientMsg : Show FA2ClientContract.FA2ClientMsg :=
{|
	show m := match m with
            | FA2ClientContract.Call_fa2_is_operator param => "Call_fa2_is_operator " ++ show param 
            | FA2ClientContract.Call_fa2_balance_of_param param => "Call_fa2_balance_of_param " ++ show param 
            | FA2ClientContract.Call_fa2_total_supply_param param => "Call_fa2_total_supply_param param " ++ show param
            | FA2ClientContract.Call_fa2_metadata_callback param => "Call_fa2_metadata_callback param " ++ show param
            | FA2ClientContract.Call_fa2_permissions_descriptor param => "Call_fa2_permissions_descriptor param " ++ show param
						end
|}.

Instance showFA2ClientContractMsg : Show FA2ClientContract.ClientMsg :=
{|
	show m := show m
|}.

Instance showFA2ClientState : Show FA2ClientContract.State :=
{|
  show t := "FA2ClientState{" 
            ++ "fa2_caddr: " ++ show t.(FA2ClientContract.fa2_caddr) ++ sep 
            ++ "bit: " ++ show t.(FA2ClientContract.bit) 
            ++ "}"
|}.

Instance showFA2Setup : Show FA2ClientContract.Setup :=
{|
  show t := "FA2ClientSetup{" 
            ++ "fa2_caddr_: " ++ show t.(FA2ClientContract.fa2_caddr_) 
            ++ "}"
|}.

Instance showFA2TransferHookMsg : Show FA2TransferHookContract.FA2TransferHookMsg :=
{|
	show m := match m with
            | FA2TransferHookContract.set_permission_policy param => "set_permission_policy " ++ show param 
						end
|}.

Instance showFA2TransferHookContractState : Show FA2TransferHookContract.State :=
{|
  show t := "FA2TransferHookState{" 
            ++ "fa2_caddr: " ++ show t.(FA2TransferHookContract.fa2_caddr) ++ sep 
            ++ "policy: " ++ show t.(FA2TransferHookContract.policy) ++ sep 
            ++ "owner: " ++ show t.(FA2TransferHookContract.owner) 
            ++ "}"
|}.

Instance showFA2TransferHookContractSetup : Show FA2TransferHookContract.Setup :=
{|
  show t := "FA2TransferHookSetup{" 
            ++ "fa2_caddr_: " ++ show t.(FA2TransferHookContract.fa2_caddr_) ++ sep 
            ++ "policy_: " ++ show t.(FA2TransferHookContract.policy_) ++ sep 
            ++ "}"
|}.

Close Scope string_scope.
(* End Printers. *)

(* Notation "f 'o' g" := (compose f g) (at level 50). *)


(* Instance BaseTypes : ChainBase := ChainGens.LocalChainBase. *)
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

Definition token_setup : FA2Token.Setup := {|
  setup_total_supply := [];
  setup_tokens := FMap.add 0%N token_metadata_0 FMap.empty; 
  initial_permission_policy := policy_all;
|}.
Definition deploy_fa2token : @ActionBody Base := create_deployment 0 FA2Token.contract token_setup.
Definition token_contract_base_addr : Address := BoundedN.of_Z_const AddrSize 128%Z.

Definition token_client_setup := FA2ClientContract.build_setup token_contract_base_addr.
Definition deploy_fa2token_client : @ActionBody Base := create_deployment 0 FA2ClientContract.contract token_client_setup.
Definition client_contract_addr : Address := BoundedN.of_Z_const AddrSize 129%Z.

Definition fa2hook_setup : FA2TransferHookContract.Setup := {|
  FA2TransferHookContract.fa2_caddr_ := token_contract_base_addr;
  FA2TransferHookContract.policy_ := policy_self_only; 
|}.
Definition deploy_fa2hook := create_deployment 0 FA2TransferHookContract.contract fa2hook_setup.
Definition fa2hook_contract_addr : Address := BoundedN.of_Z_const AddrSize 130%Z.

Definition chain_with_token_deployed : LocalChain :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_fa2token;
    build_act creator deploy_fa2token_client;
    build_act creator deploy_fa2hook
  ]).

Definition client_other_msg := @other_msg _ FA2ClientContract.FA2ClientMsg _.

Definition call_client_is_op_act :=
  let params := Build_is_operator_param 
      (Build_operator_param zero_address zero_address all_tokens)
      (Build_callback is_operator_response) in 
  let msg := client_other_msg (FA2ClientContract.Call_fa2_is_operator params) in
  act_call client_contract_addr 0%Z (serialize FA2ClientContract.ClientMsg _ msg).

Definition chain1 : LocalChain :=
  unpack_option (my_add_block chain_with_token_deployed 
  [
    build_act person_1 call_client_is_op_act
  ]).

Definition client_state lc := 
  match (FMap.find client_contract_addr lc.(lc_contract_state)) with
  | Some state => deserialize FA2ClientContract.State _ state
  | None => None
  end.
Definition token_state lc := 
  match (FMap.find token_contract_base_addr lc.(lc_contract_state)) with
  | Some state => deserialize FA2Token.State _ state
  | None => None
  end.
Compute (client_state chain1).
(* Compute (show (token_state chain1)). *)

Definition gClientMsg : G FA2ClientContract.ClientMsg := 
  let params := Build_is_operator_param 
    (Build_operator_param zero_address zero_address all_tokens)
    (Build_callback is_operator_response) in
  returnGen (client_other_msg (FA2ClientContract.Call_fa2_is_operator params)).

Definition gClientMsg' := 
  let params := Build_is_operator_param 
    (Build_operator_param zero_address zero_address all_tokens)
    (Build_callback is_operator_response) in
  returnGen params.

Sample gClientMsg'.
Sample (
  msg <- gClientMsg';;
  returnGen 1
).

Definition gClientAction := liftM (fun msg => 
  Some (
    build_act person_1 (
      act_call token_contract_base_addr 0%Z (serialize FA2ClientContract.ClientMsg _ msg)
    )
  )) gClientMsg.

Definition gFA2ChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun _ _=> 
    gClientAction) length max_acts_per_block.

Definition token_reachableFrom (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc (gFA2ChainTraceList 1) pf.

Definition token_reachableFrom_implies_reachable (lc : LocalChain) pf1 pf2 : Checker := 
  reachableFrom_implies_reachable lc (gFA2ChainTraceList 1) pf1 pf2.

Sample gClientMsg.
Sample (
        msg <- gClientMsg;;
        returnGen msg
        ).
Sample gClientAction.

Sample (gFA2ChainTraceList 1 chain_with_token_deployed 4).






