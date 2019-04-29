From Coq Require Import Arith ZArith.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import Permutation.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Extras.
From SmartContracts Require Import Automation.
From SmartContracts Require Import CursorList.
From RecordUpdate Require Import RecordUpdate.
From stdpp Require countable.

Import ListNotations.

Definition Version := nat.

Definition Amount := Z.

Bind Scope Z_scope with Amount.

Class ChainBaseTypes :=
  build_chain_base_types {
    Address : Type;
    address_eqb : Address -> Address -> bool;
    address_eqb_spec : forall (a b : Address), Bool.reflect (a = b) (address_eqb a b);
    address_eqdec :> stdpp.base.EqDecision Address;
    address_countable :> countable.Countable Address;
    address_ote :> OakTypeEquivalence Address;
    address_is_contract : Address -> bool;
    compute_block_reward : nat -> Amount;
  }.

Global Opaque Address address_eqb address_eqb_spec
       address_eqdec address_countable
       address_ote compute_block_reward.

Delimit Scope address_scope with address.
Bind Scope address_scope with Address.
Infix "=?" := address_eqb (at level 70) : address_scope.

Global Ltac destruct_address_eq :=
  repeat
    match goal with
    | [H: context[address_eqb ?a ?b] |- _] => destruct (address_eqb_spec a b)
    | [|- context[address_eqb ?a ?b]] => destruct (address_eqb_spec a b)
    end.

Section Blockchain.
Context {BaseTypes : ChainBaseTypes}.

Record ContractDeployment :=
  build_contract_deployment {
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
    block_height : nat;
    slot_number : nat;
    finalized_height : nat;
  }.

(* This represents the view of the blockchain that a contract
can access and interact with. *)
Record Chain :=
  build_chain {
    block_header : BlockHeader;
    incoming_txs : Address -> list Tx;
    outgoing_txs : Address -> list Tx;
    blocks_baked : Address -> list nat;
    contract_state : Address -> option OakValue;
  }.

(* Two chains are said to be equivalent if they are extensionally equal.
We will later require that all deployed contracts respect this relation.
This equivalence is equality if univalence is assumed. *)
Record ChainEquiv (c1 c2 : Chain) : Prop :=
  build_chain_equiv {
    header_eq : block_header c1 = block_header c2;
    incoming_txs_eq : forall addr, incoming_txs c1 addr = incoming_txs c2 addr;
    outgoing_txs_eq : forall addr, outgoing_txs c1 addr = outgoing_txs c2 addr;
    blocks_baked_eq : forall addr, blocks_baked c1 addr = blocks_baked c2 addr;
    contract_state_eq : forall addr, contract_state c1 addr = contract_state c2 addr;
  }.

Global Program Instance chain_equiv_equivalence : Equivalence ChainEquiv.
Next Obligation.
  repeat intro; apply build_chain_equiv; reflexivity.
Qed.
Next Obligation.
  intros x y []; apply build_chain_equiv; congruence.
Qed.
Next Obligation.
  intros x y z [] []; apply build_chain_equiv; congruence.
Qed.

Section Accessors.
Local Open Scope Z.

Definition account_balance (chain : Chain) (addr : Address) : Amount :=
  let sum_amounts txs := sumZ tx_amount txs in
  sum_amounts (incoming_txs chain addr) - sum_amounts (outgoing_txs chain addr) +
  sumZ compute_block_reward (blocks_baked chain addr).

Definition contract_deployment (chain : Chain) (addr : Address)
  : option ContractDeployment :=
  let to_dep tx := match tx.(tx_body) with
                  | tx_deploy dep => Some dep
                  | _ => None
                  end in
  find_first to_dep (incoming_txs chain addr).
End Accessors.

Section Theories.
Ltac rewrite_chain_equiv :=
  match goal with
  | [H: ChainEquiv _ _ |- _] => rewrite H
  end.

Global Instance chain_equiv_header_proper :
  Proper (ChainEquiv ==> eq) block_header.
Proof. repeat intro; auto using header_eq. Qed.
Global Instance chain_equiv_incoming_txs_proper :
  Proper (ChainEquiv ==> eq ==> eq) incoming_txs.
Proof. repeat intro; subst; auto using incoming_txs_eq. Qed.
Global Instance chain_equiv_outgoing_txs_proper :
  Proper (ChainEquiv ==> eq ==> eq) outgoing_txs.
Proof. repeat intro; subst; auto using outgoing_txs_eq. Qed.
Global Instance chain_equiv_blocks_backes_proper :
  Proper (ChainEquiv ==> eq ==> eq) blocks_baked.
Proof. repeat intro; subst; auto using blocks_baked_eq. Qed.
Global Instance chain_equiv_contract_state_proper :
  Proper (ChainEquiv ==> eq ==> eq) contract_state.
Proof. repeat intro; subst; auto using contract_state_eq. Qed.
Global Instance chain_equiv_account_balance_proper :
  Proper (ChainEquiv ==> eq ==> eq) account_balance.
Proof. repeat intro; subst; unfold account_balance; now rewrite_chain_equiv. Qed.
Global Instance chain_equiv_contract_deployment :
  Proper (ChainEquiv ==> eq ==> eq) contract_deployment.
Proof. repeat intro; subst; unfold contract_deployment; now rewrite_chain_equiv. Qed.
End Theories.

Record ContractCallContext :=
  build_ctx {
    (* Address sending the funds *)
    ctx_from : Address;
    (* Address of the contract being called *)
    ctx_contract_address : Address;
    (* Amount of GTU passed in call *)
    ctx_amount : Amount;
  }.

(* Operations that a contract can return or that a user can use
to interact with a chain. *)
Inductive ActionBody :=
  | act_transfer (to : Address) (amount : Amount)
  | act_call (to : Address) (amount : Amount) (msg : OakValue)
  | act_deploy (amount : Amount) (c : WeakContract) (setup : OakValue)

(* Since one operation is the possibility to deploy a new contract,
this represents an instance of a contract. Note that the act of deploying
a contract has to be a separate thing to the contract deployment a contract
can access during its execution due to positivity constraints. That is,
we would like to allow contracts to obtain information about what another
contract was deployed with (its setup, version and amount transferred). An obvious
way to model this would be to simply store a WeakContract in the chain.
But this is already a non-strict positive occurence, since we dumbed down then
end up with
Record WeakContract := { receive : (Address -> WeakContract) -> State -> State }.
where Address -> WeakContract would be some operation that the chain provides
to allow access to contracts in deployments.
*)
with WeakContract :=
    | build_weak_contract
        (version : Version)
        (init : Chain ->
             ContractCallContext ->
             OakValue ->
             option OakValue)
        (* Init respects chain equivalence *)
        (init_proper :
           Proper (ChainEquiv ==> eq ==> eq ==> eq) init)
        (receive :
           Chain ->
             ContractCallContext ->
             OakValue (* state *) ->
             option OakValue (* message *) ->
             option (OakValue * list ActionBody))
        (* And so does receive *)
        (receive_proper :
           Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive).

Definition wc_version (wc : WeakContract) : Version :=
  let (v, _, _, _, _) := wc in v.

Definition wc_init (wc : WeakContract) :=
  let (_, i, _, _, _) := wc in i.

Global Instance wc_init_proper :
  Proper (eq ==> ChainEquiv ==> eq ==> eq ==> eq) wc_init.
Proof.
  intros wc wc' eq; subst wc'.
  exact (
      match wc return
            Proper (ChainEquiv ==> eq ==> eq ==> eq) (wc_init wc) with
      | build_weak_contract _ _ ip _ _ => ip
      end).
Qed.

Definition wc_receive (wc : WeakContract) :=
  let (_, _, _, r, _) := wc in r.

Global Instance wc_receive_proper :
  Proper (eq ==> ChainEquiv ==> eq ==> eq ==> eq ==> eq) wc_receive.
Proof.
  intros wc wc' eq; subst wc'.
  exact (
      match wc return
            Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) (wc_receive wc) with
      | build_weak_contract _ _ _ _ rp => rp
      end).
Qed.

Record Action :=
  build_act {
    act_from : Address;
    act_body : ActionBody;
  }.

(* Represents a strongly-typed contract. This is what user's will primarily
use and interact with when they want deployment. We keep the weak contract
only "internally" for blockchains, while any strongly-typed contract can
be converted to and from *)
Record Contract
      (setup_ty msg_ty state_ty : Type)
      `{setup_eq : OakTypeEquivalence setup_ty}
      `{msg_eq : OakTypeEquivalence msg_ty}
      `{state_eq : OakTypeEquivalence state_ty} :=
  build_contract {
    version : Version;
    init :
      Chain ->
      ContractCallContext ->
      setup_ty ->
      option state_ty;
    init_proper :
      Proper (ChainEquiv ==> eq ==> eq ==> eq) init;
    receive :
      Chain ->
      ContractCallContext ->
      state_ty ->
      option msg_ty ->
      option (state_ty * list ActionBody);
    receive_proper :
      Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive;
  }.

Arguments version {_ _ _ _ _ _}.
Arguments init {_ _ _ _ _ _}.
Arguments receive {_ _ _ _ _ _}.
Arguments build_contract {_ _ _ _ _ _}.

Program Definition contract_to_weak_contract
          {setup_ty msg_ty state_ty : Type}
          `{setup_eq : OakTypeEquivalence setup_ty}
          `{msg_eq : OakTypeEquivalence msg_ty}
          `{state_eq : OakTypeEquivalence state_ty}
          (c : Contract setup_ty msg_ty state_ty) : WeakContract :=
      let weak_init chain ctx oak_setup :=
          do setup <- deserialize oak_setup;
          do state <- c.(init) chain ctx setup;
          Some (serialize state) in
      let weak_recv chain ctx oak_state oak_msg_opt :=
          do state <- deserialize oak_state;
          match oak_msg_opt with
          | Some oak_msg =>
            do msg <- deserialize oak_msg;
            do '(new_state, acts) <- c.(receive) chain ctx state (Some msg);
            Some (serialize new_state, acts)
          | None =>
            do '(new_state, acts) <- c.(receive) chain ctx state None;
            Some (serialize new_state, acts)
          end in
      build_weak_contract c.(version) weak_init _ weak_recv _.
Next Obligation.
  intros.
  intros c1 c2 eq_chains ctx1 ctx2 eq_ctx setup1 setup2 eq_setups.
  subst ctx2 setup2.
  subst weak_init.
  simpl.
  destruct (deserialize setup1); auto; simpl.
  now rewrite init_proper.
Qed.
Next Obligation.
  intros.
  intros c1 c2 eq_chains ctx1 ctx2 eq_ctx state1 state2 eq_states msg1 msg2 eq_msgs.
  subst ctx2 state2 msg2.
  subst weak_recv.
  simpl.
  destruct (deserialize state1); auto; simpl.
  destruct msg1.
  + destruct (deserialize o); auto; simpl.
    now rewrite receive_proper.
  + now rewrite receive_proper.
Qed.

Coercion contract_to_weak_contract : Contract >-> WeakContract.

(* Deploy a strongly typed contract with some amount and setup *)
Definition create_deployment
          {setup_ty msg_ty state_ty : Type}
          `{OakTypeEquivalence setup_ty}
          `{OakTypeEquivalence msg_ty}
          `{OakTypeEquivalence state_ty}
          (amount : Amount)
          (contract : Contract setup_ty msg_ty state_ty)
          (setup : setup_ty) : ActionBody :=
  act_deploy amount contract (serialize setup).

(* The contract interface is the main mechanism allowing a deployed
contract to interact with another deployed contract. This hides
the ugly details of everything being OakValue away from contracts. *)
Record ContractInterface {setup_ty msg_ty state_ty : Type} :=
  build_contract_interface {
    (* The address of the contract being interfaced with *)
    contract_address : Address;
    (* Version of the contract *)
    contract_version : Version;
    (* The setup that was passed when the contract was deployed *)
    contract_setup : setup_ty;
    (* Obtain the state at some point of time *)
    get_state : Chain -> option state_ty;
    (* Make an action transferring money to the contract without
      a message *)
    transfer : Amount -> ActionBody;
    (* Make an action calling the contract *)
    call : Amount -> msg_ty -> ActionBody;
  }.

Arguments ContractInterface _ _ _ : clear implicits.

Definition get_contract_interface
          (chain : Chain)
          (addr : Address)
          (setup_ty msg_ty state_ty : Type)
          `{OakTypeEquivalence setup_ty}
          `{OakTypeEquivalence msg_ty}
          `{OakTypeEquivalence state_ty}
  : option (ContractInterface setup_ty msg_ty state_ty) :=
  do 'build_contract_deployment ver ov_setup <- contract_deployment chain addr;
  do setup <- deserialize ov_setup;
  let ifc_get_state chain := deserialize =<< (contract_state chain addr) in
  let ifc_transfer := act_transfer addr in
  let ifc_call amount msg := act_call addr amount (serialize msg) in
  Some {| contract_address := addr;
          contract_version := ver;
          contract_setup := setup;
          get_state := ifc_get_state;
          transfer := ifc_transfer;
          call := ifc_call; |}.

Section Semantics.
Instance chain_settable : Settable _ :=
  settable! build_chain
  < block_header;
    incoming_txs;
    outgoing_txs;
    blocks_baked;
    contract_state >.

Definition add_tx_to_map (addr : Address) (tx : Tx) (map : Address -> list Tx)
  : Address -> list Tx :=
  fun a => if address_eqb a addr
           then tx :: map a
           else map a.

Definition set_chain_contract_state
           (addr : Address) (state : OakValue) (map : Address -> option OakValue)
  : Address -> option OakValue :=
  fun a => if address_eqb a addr
           then Some state
           else map a.

Record Environment :=
  build_env {
    env_chain :> Chain;
    env_contracts : Address -> option WeakContract;
  }.

(* Furthermore we define extensional equality for such environments. *)
Record EnvironmentEquiv (e1 e2 : Environment) : Prop :=
  build_env_equiv {
    chain_equiv : ChainEquiv e1 e2;
    contracts_eq : forall a, env_contracts e1 a = env_contracts e2 a;
  }.

Global Program Instance environment_equiv_equivalence : Equivalence EnvironmentEquiv.
Next Obligation.
  intros x; apply build_env_equiv; reflexivity.
Qed.
Next Obligation.
  intros x y []; apply build_env_equiv; now symmetry.
Qed.
Next Obligation.
  intros x y z [] []; apply build_env_equiv; try congruence.
  apply (@transitivity Chain _ _ _ y _); auto.
Qed.

Global Instance environment_equiv_contracts_proper :
  Proper (EnvironmentEquiv ==> eq ==> eq) env_contracts.
Proof. repeat intro; subst; apply contracts_eq; assumption. Qed.

Global Instance environment_equiv_chain_equiv_proper :
  Proper (EnvironmentEquiv ==> ChainEquiv) env_chain.
Proof. repeat intro; apply chain_equiv; assumption. Qed.

Instance env_settable : Settable _ :=
  settable! build_env <env_chain; env_contracts>.

Definition update_chain (upd : Chain -> Chain) (e : Environment)
  : Environment :=
  let chain := env_chain e in
  let chain := upd chain in
  e <|env_chain := chain|>.

Definition add_tx (tx : Tx) :=
  update_chain (fun c =>
                  c <|incoming_txs ::= add_tx_to_map (tx_to tx) tx|>
                    <|outgoing_txs ::= add_tx_to_map (tx_from tx) tx|>).

Definition add_contract (addr : Address) (contract : WeakContract) (e : Environment)
  : Environment :=
  e <| env_contracts ::=
    fun f a =>
      if address_eqb a addr
      then Some contract
      else f a |>.

Definition set_contract_state (addr : Address) (state : OakValue) :=
  update_chain
    (fun c => c <|contract_state ::= set_chain_contract_state addr state|>).

Section Theories.
Ltac solve_proper :=
  apply build_env_equiv;
  [apply build_chain_equiv|];
  cbn;
  repeat intro;
  repeat
    match goal with
    | [H: EnvironmentEquiv _ _|- _] => rewrite H
    end;
  auto.

Global Instance add_tx_proper :
  Proper (eq ==> EnvironmentEquiv ==> EnvironmentEquiv) add_tx.
Proof.
  repeat intro; subst.
  unfold add_tx, add_tx_to_map.
  solve_proper.
Qed.

Global Instance add_contract_proper :
  Proper (eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) add_contract.
Proof.
  repeat intro; subst.
  unfold add_contract.
  solve_proper.
Qed.

Global Instance set_contract_state_proper :
  Proper (eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) set_contract_state.
Proof.
  repeat intro; subst.
  unfold set_contract_state, update_chain, set_chain_contract_state.
  solve_proper.
Qed.
End Theories.

Section Step.
Local Open Scope Z.
(* Next we define a single step. It specifies how an external action
changes an environment and which external actions to execute after it. *)
(* todo: handle deploy/call failures. We should still transfer gas and allow this
to be recorded. *)
Inductive ChainStep :
  Environment -> Action ->
  Environment -> list Action -> Type :=
  | step_empty :
      forall {pre : Environment}
             {act : Action}
             {new_env : Environment}
             (from to : Address)
             (amount : Amount),
        amount <= account_balance pre from ->
        address_is_contract to = false ->
        act = build_act from (act_transfer to amount) ->
        let tx := build_tx from to amount tx_empty in
        EnvironmentEquiv new_env (add_tx tx pre) ->
        ChainStep pre act new_env []
  | step_deploy :
      forall {pre : Environment}
             {act : Action}
             {new_env : Environment}
             (from to : Address)
             (amount : Amount)
             (wc : WeakContract)
             (setup : OakValue)
             (state : OakValue),
      amount <= account_balance pre from ->
      env_contracts pre to = None ->
      incoming_txs pre to = [] ->
      address_is_contract to = true ->
      act = build_act from (act_deploy amount wc setup) ->
      let tx := build_tx
                  from to amount
                  (tx_deploy (build_contract_deployment (wc_version wc) setup)) in
      wc_init
        wc
        (add_tx tx pre)
        (build_ctx from to amount)
        setup = Some state ->
      EnvironmentEquiv
        new_env
        (set_contract_state to state (add_contract to wc (add_tx tx pre))) ->
      ChainStep pre act new_env []
  | step_call_empty :
      forall {pre : Environment}
             {act : Action}
             {new_env : Environment}
             {new_acts : list Action}
             (from to : Address)
             (amount : Amount)
             (wc : WeakContract)
             (prev_state : OakValue)
             (new_state : OakValue)
             (resp_acts : list ActionBody),
      amount <= account_balance pre from ->
      env_contracts pre to = Some wc ->
      contract_state pre to = Some prev_state ->
      act = build_act from (act_transfer to amount) ->
      let tx := build_tx from to amount tx_empty in
      wc_receive
        wc
        (add_tx tx pre)
        (build_ctx from to amount)
        prev_state
        None = Some (new_state, resp_acts) ->
      new_acts = map (build_act to) resp_acts ->
      EnvironmentEquiv
        new_env
        (set_contract_state to new_state (add_tx tx pre)) ->
      ChainStep pre act new_env new_acts
  | step_call_msg :
      forall {pre : Environment}
             {act : Action}
             {new_env : Environment}
             {new_acts : list Action}
             (from to : Address)
             (amount : Amount)
             (wc : WeakContract)
             (msg : OakValue)
             (prev_state : OakValue)
             (new_state : OakValue)
             (resp_acts : list ActionBody),
      amount <= account_balance pre from ->
      env_contracts pre to = Some wc ->
      contract_state pre to = Some prev_state ->
      act = build_act from (act_call to amount msg) ->
      let tx := build_tx from to amount (tx_call msg) in
      wc_receive
        wc
        (add_tx tx pre)
        (build_ctx from to amount)
        prev_state
        (Some msg) = Some (new_state, resp_acts) ->
      new_acts = map (build_act to) resp_acts ->
      EnvironmentEquiv
        new_env
        (set_contract_state to new_state (add_tx tx pre)) ->
      ChainStep pre act new_env new_acts.

Section Accessors.
Context {pre : Environment} {act : Action}
        {post : Environment} {new_acts : list Action}
        (step : ChainStep pre act post new_acts).

Definition step_from : Address :=
  match step with
  | step_empty from _ _ _ _ _ _ _
  | step_deploy from _ _ _ _ _ _ _ _ _ _ _ _ _
  | step_call_empty from _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | step_call_msg from _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => from
  end.

Definition step_to : Address :=
  match step with
  | step_empty _ to _ _ _ _ _ _
  | step_deploy _ to _ _ _ _ _ _ _ _ _ _ _ _
  | step_call_empty _ to _ _ _ _ _ _ _ _ _ _ _ _ _
  | step_call_msg _ to _ _ _ _ _ _ _ _ _ _ _ _ _ _ => to
  end.

Definition step_amount : Amount :=
  match step with
  | step_empty _ _ amount _ _ _ _ _
  | step_deploy _ _ amount _ _ _ _ _ _ _ _ _ _ _
  | step_call_empty _ _ amount _ _ _ _ _ _ _ _ _ _ _ _
  | step_call_msg _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ => amount
  end.
End Accessors.

Section Theories.
Context {pre : Environment} {act : Action}
        {post : Environment} {new_acts : list Action}
        (step : ChainStep pre act post new_acts).

Lemma account_balance_post (addr : Address) :
  account_balance post addr =
  account_balance pre addr
  + (if (addr =? step_to step)%address then step_amount step else 0)
  - (if (addr =? step_from step)%address then step_amount step else 0).
Proof.
  unfold account_balance.
  destruct step; subst; cbn;
    match goal with
    | [H: EnvironmentEquiv _ _ |- _] => rewrite H
    end;
    cbn; unfold add_tx_to_map; destruct_address_eq; cbn; lia.
Qed.

Lemma account_balance_post_to :
  step_from step <> step_to step ->
  account_balance post (step_to step) =
  account_balance pre (step_to step) + step_amount step.
Proof.
  rewrite account_balance_post.
  destruct_address_eq; prove.
Qed.

Lemma account_balance_post_from :
  step_from step <> step_to step ->
  account_balance post (step_from step) =
  account_balance pre (step_from step) - step_amount step.
Proof.
  rewrite account_balance_post.
  destruct_address_eq; prove.
Qed.

Lemma account_balance_post_irrelevant (addr : Address) :
  addr <> step_from step ->
  addr <> step_to step ->
  account_balance post addr = account_balance pre addr.
Proof.
  rewrite account_balance_post.
  destruct_address_eq; prove.
Qed.

Lemma block_header_post_step : block_header post = block_header pre.
Proof.
  destruct step;
    match goal with
    | [H: EnvironmentEquiv _ _ |- _] => now rewrite H
    end.
Qed.
End Theories.
End Step.

Section Trace.
Definition add_new_block_header
          (header : BlockHeader)
          (baker : Address)
          (env : Environment) : Environment :=
let chain := env_chain env in
let chain :=
    {| block_header := header;
       incoming_txs := incoming_txs chain;
       outgoing_txs := outgoing_txs chain;
       contract_state := contract_state chain;
       blocks_baked a :=
         if address_eqb a baker
         then block_height header :: blocks_baked chain a
         else blocks_baked chain a; |} in
env <|env_chain := chain|>.

(* Todo: this should just be a computation. But I still do not *)
(* know exactly what the best way of working with reflect is *)
Definition IsValidNextBlock (new old : BlockHeader) : Prop :=
  block_height new = S (block_height old) /\
  slot_number new > slot_number old /\
  finalized_height new >= finalized_height old /\
  finalized_height new < block_height new.

Record ChainState :=
  build_chain_state {
    chain_state_env :> Environment;
    chain_state_queue : list Action;
  }.

Inductive ChainEvent : ChainState -> ChainState -> Type :=
  | evt_block :
      forall {prev : ChainState}
             {header : BlockHeader}
             {baker : Address}
             {next : ChainState},
        chain_state_queue prev = [] ->
        IsValidNextBlock header (block_header prev) ->
        Forall
          (fun act => address_is_contract (act_from act) = false)
          (chain_state_queue next) ->
        EnvironmentEquiv
          next
          (add_new_block_header header baker prev) ->
        ChainEvent prev next
  | evt_step :
      forall {prev : ChainState}
             {act : Action}
             {acts : list Action}
             {next : ChainState}
             {new_acts : list Action},
        chain_state_queue prev = act :: acts ->
        ChainStep prev act next new_acts ->
        chain_state_queue next = new_acts ++ acts ->
        ChainEvent prev next
  | evt_permute :
      forall {prev new : ChainState},
        chain_state_env prev = chain_state_env new ->
        Permutation (chain_state_queue prev) (chain_state_queue new) ->
        ChainEvent prev new.

Definition empty_state : ChainState :=
  {| chain_state_env :=
       {| env_chain :=
            {| block_header :=
                 {| block_height := 0;
                    slot_number := 0;
                    finalized_height := 0; |};
               incoming_txs a := [];
               outgoing_txs a := [];
               blocks_baked a := [];
               contract_state a := None; |};
          env_contracts a := None; |};
     chain_state_queue := [] |}.

(* The ChainTrace captures that there is a valid execution where,
starting from one environment and queue of actions, we end up in a
different environment and queue of actions. *)
Definition ChainTrace := CursorList ChainState ChainEvent.

Section Theories.
Ltac rewrite_environment_equiv :=
  match goal with
  | [H: EnvironmentEquiv _ _ |- _] => rewrite H in *
  end.

Ltac destruct_event :=
  match goal with
  | [H: ChainEvent _ _ |- _] => destruct H
  end.

Ltac destruct_step :=
  match goal with
  | [H: ChainStep _ _ _ _ |- _] => destruct H
  end.

Lemma contract_addr_format
      {to}
      (trace : ChainTrace empty_state to)
      (addr : Address) (wc : WeakContract) :
  env_contracts to addr = Some wc ->
  address_is_contract addr = true.
Proof.
  intros contract_at_addr.
  remember empty_state eqn:eq.
  induction trace; rewrite eq in *; clear eq.
  - cbn in *; congruence.
  - destruct_event.
    + rewrite_environment_equiv; cbn in *; auto.
    + destruct_step; rewrite_environment_equiv; cbn in *; destruct_address_eq; subst; auto.
    + intuition.
Qed.

End Theories.
End Trace.
End Semantics.

Class ChainBuilderType :=
  build_builder {
    builder_type : Type;

    builder_initial : builder_type;

    builder_env : builder_type -> Environment;

    builder_add_block
      (b : builder_type)
      (baker : Address)
      (actions : list Action)
      (slot_number : nat)
      (finalized_height : nat) :
      option builder_type;

    builder_trace (b : builder_type) :
      inhabited (ChainTrace empty_state (build_chain_state (builder_env b) []));
  }.

Global Coercion builder_type : ChainBuilderType >-> Sortclass.
End Blockchain.

Arguments version {_ _ _ _ _ _ _}.
Arguments init {_ _ _ _ _ _ _}.
Arguments receive {_ _ _ _ _ _ _}.
Arguments build_contract {_ _ _ _ _ _ _}.
Arguments ContractInterface {_} _ _ _.
Arguments build_contract_interface {_ _ _ _}.
