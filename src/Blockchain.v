From Coq Require Import String.

From Coq Require OrderedTypeEx.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.

Definition Address := nat.
Delimit Scope address_scope with address.
Bind Scope address_scope with Address.

Module Address.
  Definition eqb := Nat.eqb.
End Address.

Infix "=?" := Address.eqb (at level 70) : address_scope.

Definition Amount := nat.
Definition BlockId := nat.
Definition BlockHash := string.
Definition Version := nat.

Record ContractDeployment :=
  {
    deployment_version : Version;
    deployment_msg_ty : OakType;
    deployment_state_ty : OakType;
    deployment_setup : OakValue;
  }.

Inductive TxBody :=
  | tx_empty
  | tx_deploy (deployment : ContractDeployment)
  | tx_call (message : OakValue).

Record Tx :=
  build_tx {
    tx_from : Address;
    tx_to : Address;
    tx_amount : Amount;
    tx_body : TxBody;
  }.

Record BlockHeader :=
  build_block_header {
    block_number : BlockId;
  }.

Record Block :=
  build_block {
    block_header : BlockHeader;
    block_txs : list Tx;
  }.

(* This needs to be polymorphic because ... for reasons. LocalChain does not
   work if not. A smaller repro is:
Class interface :=
  { ty : Type;
    func : ty -> ty;
  }.

(* the problem is that the implementation contains functions taking the
   interface *)
Record impl :=
  {
    callback : interface -> nat;
  }.

Definition func_concrete (i : impl) : impl := i.

Instance impl_interface : interface :=
  {| ty := impl; func := func_concrete |}.

   todo: come back to this and understand universe polymorphism in depth. *)
Polymorphic Record ChainInterface :=
  build_chain_interface {
    (* Would be nice to encapsulate ChainInterface somewhat here
       and avoid these ugly prefixed names *)
    ci_chain_type : Type;
    ci_chain_at : ci_chain_type -> BlockId -> option ci_chain_type;
    ci_head_block : ci_chain_type -> Block;
    ci_incoming_txs : ci_chain_type -> Address -> list Tx;
    ci_outgoing_txs :  ci_chain_type -> Address -> list Tx;
    ci_contract_deployment :  ci_chain_type -> Address -> option ContractDeployment;
    ci_contract_state : ci_chain_type -> Address -> option OakValue;
  }.

Record Chain :=
  build_chain {
    chain_ci : ChainInterface;
    chain_val : chain_ci.(ci_chain_type);
  }.

Definition chain_at (c : Chain) (bid : BlockId) : option Chain :=
  do x <- c.(chain_ci).(ci_chain_at) c.(chain_val) bid;
    Some {| chain_val := x |}.

Definition head_block (c : Chain) :=
  c.(chain_ci).(ci_head_block) c.(chain_val).

Definition block_at (c : Chain) (bid : BlockId) : option Block :=
  do c <- chain_at c bid; Some (head_block c).

Definition incoming_txs (c : Chain) :=
  c.(chain_ci).(ci_incoming_txs) c.(chain_val).

Definition outgoing_txs (c : Chain) :=
  c.(chain_ci).(ci_outgoing_txs) c.(chain_val).

Definition contract_deployment (c : Chain) :=
  c.(chain_ci).(ci_contract_deployment) c.(chain_val).

Definition contract_state (c : Chain) :=
  c.(chain_ci).(ci_contract_state) c.(chain_val).

Inductive ContractCallContext :=
  build_contract_call_ctx {
    (* Chain *)
    ctx_chain : Chain;
    (* Address sending the funds *)
    ctx_from : Address;
    (* Address of the contract being called *)
    ctx_contract_address : Address;
    (* Amount of GTU passed in call *)
    ctx_amount : Amount;
  }.

Inductive ChainAction :=
  | act_transfer (to : Address) (amount : Amount)
  | act_call (to : Address) (amount : Amount) (msg : OakValue)
  | act_deploy
      {setup_ty msg_ty state_ty : Type}
      (version : Version)
      (init : ContractCallContext -> setup_ty -> option state_ty)
      (receive : ContractCallContext -> state_ty ->
                 option msg_ty -> option (state_ty * list ChainAction)).

(*
Record ContractInterface (setup_ty msg_ty state_ty : Type) :=
  build_contract_interface {
    (* The address of the contract being interfaced with *)
    contract_address : Address;
    (* The setup that was passed when the contract was deployed *)
    setup : setup_ty;
    (* Obtain the state at some point of time *)
    get_state : Chain -> option state_ty;
    (* Make an action transferring money to the contract without
       a message *)
    transfer : Amount -> ContractAction;
    (* Make an action calling the contract *)
    call : Amount -> msg_ty -> ContractAction;
  }.
*)

(*
(* todo: this should be easier -- we want actual strong typed
   interface by equivalence of oak type (iterated product, for instance)
   to types in contracts. Right now the interface received allows you
   only to interact with a contract using interpreted types. *)
Definition get_contract_interface
           (setup_oty msg_oty state_oty : OakType)
           (chain : Chain)
           (addr : Address)
  : option (ContractInterface
              (interp_type setup_oty)
              (interp_type msg_oty)
              (interp_type state_oty)) :=
  do deployment <- chain.(get_contract_deployment) addr;
  let (deploy_setup_oty, deploy_setup) := deployment.(deployment_setup) in
  match eq_oak_type_dec setup_oty deploy_setup_oty,
        eq_oak_type_dec msg_oty deployment.(deployment_msg_ty),
        eq_oak_type_dec state_oty deployment.(deployment_state_ty)
  with
  | left _, left _, left _ =>
    Some {|
        contract_address := addr;
        setup := let x : interp_type setup_oty := ltac:(subst; exact deploy_setup) in x;
        get_state futureChain :=
          do val <- futureChain.(get_contract_state) addr;
          extract_oak_value state_oty val;
        transfer := act_transfer addr;
        call amt msg := act_call addr amt (build_oak_value msg_oty msg) |}
  | _, _, _ => None
  end.
*)
