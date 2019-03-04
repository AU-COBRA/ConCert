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
    block_hash : BlockHash;
  }.

Record Block :=
  build_block {
    block_header : BlockHeader;
    block_txs : list Tx;
  }.

Inductive Chain :=
  build_chain {
    get_chain_at : BlockId -> option Chain;
    get_block_at : BlockId -> option Block;
    head_block : Block;
    get_incoming_txs : Address -> list unit;
    get_outgoing_txs : Address -> list unit;
    get_contract_deployment : Address -> option ContractDeployment;
    get_contract_state : Address -> option OakValue;
  }.

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

Inductive Contract : Type -> Type -> Type -> Type :=
  | build_contract :
      forall (setup_ty msg_ty state_ty : Type),
        Version ->
        (setup_ty -> ContractCallContext -> option state_ty) -> (* init *)
        (state_ty -> ContractCallContext ->
         option msg_ty -> option (state_ty * list ChainAction)) -> (* receive *)
        Contract setup_ty msg_ty state_ty
with ChainAction :=
  | act_transfer (to : Address) (amount : Amount)
  | act_deploy :
      forall setup_ty msg_ty state_ty,
        Contract setup_ty msg_ty state_ty ->
        setup_ty ->
        ChainAction
  | act_call (to : Address) (amount : Amount) (msg : OakValue).

Definition contract_version {A B C : Type} (c : Contract A B C) :=
  let 'build_contract _ _ _ ver _ _ := c in ver.

Definition contract_init {A B C : Type} (c : Contract A B C) :=
  let 'build_contract _ _ _ _ init _ := c in init.

Definition contract_receive {A B C : Type} (c : Contract A B C) :=
  let 'build_contract _ _ _ _ _ recv := c in recv.

Record ContractInterface (setup_ty msg_ty state_ty : Type) :=
  build_contract_interface {
    contract_address : Address;
    setup : setup_ty;
    get_state : Chain -> option state_ty;
    transfer : Amount -> ChainAction;
    call : Amount -> msg_ty -> ChainAction;
  }.

(* todo: this should be easier -- we want actual strong typed
   interface by equivalence of oak type (iterated product, for instance)
   to types in contracts. Right now the interface received allows you
   only to interact with a contrat using interpreted types. *)
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