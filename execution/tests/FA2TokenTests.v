From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface.
From ConCert Require Import Serializable.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import BoundedN.
Require Import Extras.




Module FA2CallerContract.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Import ListNotations.
Import RecordSetNotations.

Section FA2Caller.
Context {BaseTypes : ChainBase}.
(* Context {FA2ContractAddr : Address}. *)
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
(* Open Scope N_scope. *)

Inductive Msg' :=
  | Call_fa2_is_operator : is_operator_param -> Msg'
. 

Definition FA2CallerMsg : Type := is_operator_response + Msg'.

Record State := 
  build_state {
  fa2_caddr : Address
}.

Record Setup := 
  build_setup {
  fa2_caddr_ : Address
}.

Instance state_settable : Settable _ :=
  settable! build_state <fa2_caddr>.
Instance setup_settable : Settable _ :=
  settable! build_setup <fa2_caddr_>.

Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance msg'_serializable : Serializable Msg' :=
  Derive Serializable Msg'_rect <Call_fa2_is_operator>.

About FA2CallerMsg.
Import Serializable.
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
reflexivity. Qed.

Global Instance state_serializable : Serializable State :=
	Derive Serializable State_rect <build_state>.

End Serialization.
  

End FA2Caller.
End FA2CallerContract.



From ConCert.Execution.QCTests Require Import 
  ChainGens TestUtils ChainPrinters SerializablePrinters TraceGens.

Require Import ZArith Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Require Import Containers.

Import LocalBlockchain.
Import ListNotations.

Notation "f 'o' g" := (compose f g) (at level 50).

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.
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
Definition deploy_fa2token := create_deployment 0 FA2Token.contract token_setup.

Let contract_base_addr := BoundedN.of_Z_const AddrSize 128%Z.

Definition chain_with_token_deployed :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_fa2token
  ]).






