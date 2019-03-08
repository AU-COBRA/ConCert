From Coq Require Import String.
From Coq Require OrderedTypeEx.
From Coq Require Import List.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Extras.

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
    (* todo: model any type/constraints so we can have this. Right now the
       problem is that Congress messages can contain _any_ oak value (for
       the congress to send out), so there is no bijection from its message type
       to oak type.
    deployment_msg_ty : OakType;
    deployment_state_ty : OakType; *)
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

Record ChainInterface :=
  build_chain_interface {
    (* Would be nice to encapsulate ChainInterface somewhat here
       and avoid these ugly prefixed names *)
    ci_chain_type : Type;
    ci_chain_at : ci_chain_type -> BlockId -> option ci_chain_type;
    (* Last finished block. During contract execution, this is the previous
       block, i.e. this block does _not_ contain the transaction that caused
       the contract to be called *)
    ci_head_block : ci_chain_type -> Block;
    ci_incoming_txs : ci_chain_type -> Address -> list Tx;
    ci_outgoing_txs :  ci_chain_type -> Address -> list Tx;
    ci_contract_state : ci_chain_type -> Address -> option OakValue;
  }.

Record Chain :=
  build_chain {
    chain_ci : ChainInterface;
    chain_val : chain_ci.(ci_chain_type);
  }.

Section ChainAccessors.
  Context (chain : Chain).

  Let g {A : Type} (p : forall chain : ChainInterface, ci_chain_type chain -> A)
      := p chain.(chain_ci) chain.(chain_val).

  Definition chain_at (bid : BlockId) : option Chain :=
    do x <- chain.(chain_ci).(ci_chain_at) chain.(chain_val) bid;
      Some {| chain_val := x |}.

  Definition head_block := g ci_head_block.
  Definition incoming_txs := g ci_incoming_txs.
  Definition outgoing_txs := g ci_outgoing_txs.
  Definition contract_state := g ci_contract_state.
  Definition account_balance (addr : Address) : Amount :=
    let sum := fold_right Nat.add 0 in
    let sum_amounts txs := sum (map tx_amount txs) in
    sum_amounts (incoming_txs addr) - sum_amounts (outgoing_txs addr).
  Definition contract_deployment (addr : Address) : option ContractDeployment :=
    let to_dep tx := match tx.(tx_body) with
                     | tx_deploy dep => Some dep
                     | _ => None
                     end in
    find_first to_dep (incoming_txs addr).
End ChainAccessors.

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
  | act_deploy (amount : Amount) (c : WeakContract) (setup : OakValue)
with WeakContract :=
     | build_weak_contract
         (version : Version)
         (init : ContractCallContext -> OakValue -> option OakValue)
         (receive : ContractCallContext -> OakValue (* state *) ->
                    option OakValue (* message *) ->
                    option (OakValue * list ChainAction)).

Record Contract
       (setup_ty msg_ty state_ty : Type)
       {eq_setup : OakTypeEquivalence setup_ty}
       {eq_msg : OakTypeEquivalence msg_ty}
       {eq_state : OakTypeEquivalence state_ty} :=
  build_contract {
    version : Version;
    init : ContractCallContext -> setup_ty -> option state_ty;
    receive :
      ContractCallContext -> state_ty ->
      option msg_ty -> option (state_ty * list ChainAction);
  }.

Arguments version {_ _ _ _ _ _} contract : rename.
Arguments init {_ _ _ _ _ _} contract ctx setup : rename.
Arguments receive {_ _ _ _ _ _} contract ctx state msg : rename.
Arguments build_contract {_ _ _ _ _ _}.

Definition contract_to_weak_contract
           {A B C : Type}
           {eq_a : OakTypeEquivalence A}
           {eq_b : OakTypeEquivalence B}
           {eq_c : OakTypeEquivalence C}
           (c : Contract A B C) : WeakContract :=
  let weak_init ctx oak_setup :=
      do setup <- deserialize oak_setup;
      do state <- c.(init) ctx setup;
      Some (serialize state) in
  let weak_recv ctx oak_state oak_msg_opt :=
      do state <- deserialize oak_state;
      match oak_msg_opt with
      | Some oak_msg =>
        do msg <- deserialize oak_msg;
        do '(new_state, acts) <- c.(receive) ctx state (Some msg);
        Some (serialize new_state, acts)
      | None =>
        do '(new_state, acts) <- c.(receive)  ctx state None;
        Some (serialize new_state, acts)
      end in
  build_weak_contract c.(version) weak_init weak_recv.

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
