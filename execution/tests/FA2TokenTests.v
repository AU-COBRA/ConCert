



Module FA2ClientContract.
From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface.
From ConCert Require Import Serializable.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import BoundedN.
Require Import Extras.

From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Require Import ZArith.
Import ListNotations.
Import RecordSetNotations.

Section FA2Client.
Context {BaseTypes : ChainBase}.
(* Context {FA2ContractAddr : Address}. *)
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Inductive FA2ClientMsg :=
  | Call_fa2_is_operator : is_operator_param -> FA2ClientMsg. 

Global Instance FA2ClientMsg_serializable : Serializable FA2ClientMsg :=
  Derive Serializable FA2ClientMsg_rect <Call_fa2_is_operator>.
Definition Msg := @FA2ReceiverMsg BaseTypes FA2ClientMsg _.

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

(* Global Instance Msg_serializable' : Serializable (@FA2ReceiverMsg BaseTypes FA2ClientMsg) :=
Derive Serializable (@FA2ReceiverMsg_rect BaseTypes FA2ClientMsg) <
  (@receive_balance_of_param BaseTypes FA2ClientMsg), 
  (@receive_total_supply_param BaseTypes FA2ClientMsg), 
  (@receive_metadata_callback BaseTypes FA2ClientMsg), 
  (@receive_is_operator BaseTypes FA2ClientMsg), 
  (@transfer_hook  BaseTypes FA2ClientMsg), 
  (@other_msg BaseTypes FA2ClientMsg)>. *)

(* Global Instance Msg_serializable : Serializable FA2Client.Msg :=  @FA2Interface.FA2ReceiverMsg_serializable. *)
(* Import Serializable.
Ltac make_serializable eliminator ctors :=
  let ser := make_serializer eliminator in
  let elim_ty := type of eliminator in
  let ty := get_ty_from_elim_ty elim_ty in
  let deser := make_deserializer ctors ty in
  exact
    {| serialize := ser;
       deserialize := deser;
       deserialize_serialize :=
         ltac:(intros []; repeat (cbn in *; try rewrite deserialize_serialize; auto)) |}.
Global Program Instance msg_serializable : Serializable FA2CallerMsg :=
{| serialize := serialize_sum;
   deserialize := deserialize_sum
|}.
Next Obligation.
intros. rewrite deserialize_serialize_sum. 
reflexivity. Qed. *)

Global Instance state_serializable : Serializable State :=
	Derive Serializable State_rect <build_state>.

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
									 (maybe_msg : option FA2Client.Msg)
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

Definition contract : Contract Setup Msg State :=
  build_contract FA2Client.init init_proper FA2Client.receive receive_proper.

End FA2Client.

End FA2ClientContract.

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
	ChainGens TestUtils ChainPrinters SerializablePrinters TraceGens FA2Printers.
(* For monad notations *)
(* From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope. *)
From Coq Require Import List Int.
Import BoundedN.Stdpp.
Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.

Section Printers.
Local Open Scope string_scope.

Instance showFA2ClientMsg : Show FA2ClientContract.FA2ClientMsg :=
{|
	show m := match m with
						| FA2ClientContract.Call_fa2_is_operator param => "call_fa2_is_operator " ++ show param 
						end
|}.

Instance showFA2ClientContractMsg : Show FA2ClientContract.Msg :=
{|
	show m := show m
|}.

Instance showFA2ClientState : Show FA2ClientContract.State :=
{|
  show t := "FA2ClientContractState{" 
            ++ "fa2_caddr: " ++ show t.(FA2ClientContract.fa2_caddr) ++ sep 
            ++ "bit: " ++ show t.(FA2ClientContract.bit) 
            ++ "}"
|}.

Instance showFA2Setup : Show FA2ClientContract.Setup :=
{|
  show t := "FA2ClientContractSetup{" 
            ++ "fa2_caddr_: " ++ show t.(FA2ClientContract.fa2_caddr_) 
            ++ "}"
|}.
       
Close Scope string_scope.
End Printers.

(* Notation "f 'o' g" := (compose f g) (at level 50). *)

(* Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase. *)
(* Let BaseTypes := ChainGens.LocalChainBase. *)
(* Instance BaseTypes : ChainBase := ChainGens.LocalChainBase. *)
(** example policies *)

(* the policy which allows only token owners to transfer their own tokens. *)
Definition own_policy : permissions_descriptor := {|
  descr_self := self_transfer_permitted;
  descr_operator := operator_transfer_denied;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

(* non-transferable token (neither token owner, nor operators can transfer tokens. *)
Definition own_policy1 : permissions_descriptor := {|
  descr_self := self_transfer_denied;
  descr_operator := operator_transfer_denied;
  descr_sender := owner_no_op;
  descr_receiver := owner_no_op;
  descr_custom := None;
|}.

Definition token_setup := FA2Token.build_setup [] own_policy .
Definition deploy_fa2token : @ActionBody Base := create_deployment 0 FA2Token.contract token_setup.

Definition token_contract_base_addr : Address := BoundedN.of_Z_const AddrSize 128%Z.

Definition token_client_setup := FA2ClientContract.build_setup token_contract_base_addr.
Definition deploy_fa2token_client : @ActionBody Base := create_deployment 0 FA2ClientContract.contract token_client_setup.
Definition client_contract_addr : Address := BoundedN.of_Z_const AddrSize 129%Z.


Definition chain_with_token_deployed : LocalChain :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_fa2token;
    build_act creator deploy_fa2token_client
  ]).

Definition call_client_is_op_act :=
  let params := Build_is_operator_param 
      (Build_operator_param zero_address zero_address all_tokens)
      (Build_callback is_operator_response) in 
  let msg := other_msg (FA2ClientContract.Call_fa2_is_operator params) in
  act_call client_contract_addr 0%Z (serialize FA2ClientContract.Msg _ msg).

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
Compute (show (token_state chain1)).

Definition gClientMsg : G FA2ClientContract.Msg := 
  let params := Build_is_operator_param 
    (Build_operator_param zero_address zero_address all_tokens)
    (Build_callback is_operator_response) in
  returnGen (other_msg (FA2ClientContract.Call_fa2_is_operator params)).
Definition gClientAction := liftM (fun msg => 
  Some (
    build_act person_1 (
      act_call token_contract_base_addr 0%Z (serialize FA2ClientContract.Msg _ msg)
    )
  )) gClientMsg.

Definition gFA2ChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun _ _=> 
    gClientAction) length max_acts_per_block.

Definition token_reachableFrom (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc (gFA2ChainTraceList 1) pf.

Definition token_reachableFrom_implies_reachable (lc : LocalChain) pf1 pf2 : Checker := 
  reachableFrom_implies_reachable lc (gFA2ChainTraceList 1) pf1 pf2.






