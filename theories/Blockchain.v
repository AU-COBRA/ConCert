From Coq Require Import Arith ZArith.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import Permutation.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.
From SmartContracts Require Import Serializable.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Extras.
From SmartContracts Require Import Automation.
From SmartContracts Require Import ChainedList.
From RecordUpdate Require Import RecordUpdate.
From stdpp Require countable.

Import ListNotations.

Definition Amount := Z.
Bind Scope Z_scope with Amount.

Class ChainBase :=
  build_chain_base {
    Address : Type;
    address_eqb : Address -> Address -> bool;
    address_eqb_spec :
      forall (a b : Address), Bool.reflect (a = b) (address_eqb a b);
    address_eqdec :> stdpp.base.EqDecision Address;
    address_countable :> countable.Countable Address;
    address_serializable :> Serializable Address;
    address_is_contract : Address -> bool;
  }.

Global Opaque Address address_eqb address_eqb_spec
       address_eqdec address_countable address_serializable.

Delimit Scope address_scope with address.
Bind Scope address_scope with Address.
Infix "=?" := address_eqb (at level 70) : address_scope.

Lemma address_eq_refl `{ChainBase} x :
  address_eqb x x = true.
Proof. destruct (address_eqb_spec x x); auto; congruence. Qed.

Lemma address_eq_ne `{ChainBase} x y :
  x <> y ->
  address_eqb x y = false.
Proof. destruct (address_eqb_spec x y) as [->|]; tauto. Qed.

Lemma address_eq_sym `{ChainBase} x y :
  address_eqb x y = address_eqb y x.
Proof.
  destruct (address_eqb_spec x y) as [->|].
  - now rewrite address_eq_refl.
  - rewrite address_eq_ne; auto.
Qed.

Global Ltac destruct_address_eq :=
  repeat
    match goal with
    | [H: context[address_eqb ?a ?b] |- _] =>
      try rewrite (address_eq_sym b a) in *; destruct (address_eqb_spec a b)
    | [|- context[address_eqb ?a ?b]] =>
      try rewrite (address_eq_sym b a) in *; destruct (address_eqb_spec a b)
    end.

Section Blockchain.
Context {BaseTypes : ChainBase}.

(* This represents the view of the blockchain that a contract
can access and interact with. *)
Record Chain :=
  build_chain {
    chain_height : nat;
    current_slot : nat;
    finalized_height : nat;
    account_balance : Address -> Amount;
  }.

(* Two chains are said to be equivalent if they are extensionally equal.
We will later require that all deployed contracts respect this relation.
This equivalence is equality if funext is assumed. *)
Record ChainEquiv (c1 c2 : Chain) : Prop :=
  build_chain_equiv {
    chain_height_eq : chain_height c1 = chain_height c2;
    current_slot_eq : current_slot c1 = current_slot c2;
    finalized_height_eq : finalized_height c1 = finalized_height c2;
    account_balance_eq : forall addr, account_balance c1 addr = account_balance c2 addr;
  }.

Global Program Instance chain_equiv_equivalence : Equivalence ChainEquiv.
Next Obligation. repeat intro; apply build_chain_equiv; reflexivity. Qed.
Next Obligation. intros x y []; apply build_chain_equiv; congruence. Qed.
Next Obligation. intros x y z [] []; apply build_chain_equiv; congruence. Qed.

Global Instance chain_equiv_chain_height :
  Proper (ChainEquiv ==> eq) chain_height.
Proof. repeat intro; auto using chain_height_eq. Qed.
Global Instance chain_equiv_current_slot :
  Proper (ChainEquiv ==> eq) current_slot.
Proof. repeat intro; auto using current_slot_eq. Qed.
Global Instance chain_equiv_finalized_height :
  Proper (ChainEquiv ==> eq) finalized_height.
Proof. repeat intro; auto using finalized_height_eq. Qed.
Global Instance chain_equiv_account_balance_proper :
  Proper (ChainEquiv ==> eq ==> eq) account_balance.
Proof. repeat intro; subst; auto using account_balance_eq. Qed.

Record ContractCallContext :=
  build_ctx {
    (* Address sending the funds *)
    ctx_from : Address;
    (* Address of the contract being called *)
    ctx_contract_address : Address;
    (* Amount of currency passed in call *)
    ctx_amount : Amount;
  }.

(* Operations that a contract can return or that a user can use
to interact with a chain. *)
Inductive ActionBody :=
  | act_transfer (to : Address) (amount : Amount)
  | act_call (to : Address) (amount : Amount) (msg : SerializedValue)
  | act_deploy (amount : Amount) (c : WeakContract) (setup : SerializedValue)
with WeakContract :=
     | build_weak_contract
         (init :
            Chain ->
            ContractCallContext ->
            SerializedValue (* setup *) ->
            option SerializedValue)
         (* Init respects chain equivalence *)
         (init_proper :
            Proper (ChainEquiv ==> eq ==> eq ==> eq) init)
         (receive :
            Chain ->
            ContractCallContext ->
            SerializedValue (* state *) ->
            option SerializedValue (* message *) ->
            option (SerializedValue * list ActionBody))
         (* And so does receive *)
         (receive_proper :
            Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive).

Definition wc_init (wc : WeakContract) :=
  let (i, _, _, _) := wc in i.

Global Instance wc_init_proper :
  Proper (eq ==> ChainEquiv ==> eq ==> eq ==> eq) wc_init.
Proof.
  intros wc wc' eq; subst wc'.
  exact (
      match wc return
            Proper (ChainEquiv ==> eq ==> eq ==> eq) (wc_init wc) with
      | build_weak_contract _ ip _ _ => ip
      end).
Qed.

Definition wc_receive (wc : WeakContract) :=
  let (_, _, r, _) := wc in r.

Global Instance wc_receive_proper :
  Proper (eq ==> ChainEquiv ==> eq ==> eq ==> eq ==> eq) wc_receive.
Proof.
  intros wc wc' eq; subst wc'.
  exact (
      match wc return
            Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) (wc_receive wc) with
      | build_weak_contract _ _ _ rp => rp
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
      (Setup Msg State : Type)
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State} :=
  build_contract {
    init :
      Chain ->
      ContractCallContext ->
      Setup ->
      option State;
    init_proper :
      Proper (ChainEquiv ==> eq ==> eq ==> eq) init;
    receive :
      Chain ->
      ContractCallContext ->
      State ->
      option Msg ->
      option (State * list ActionBody);
    receive_proper :
      Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive;
  }.

Arguments init {_ _ _ _ _ _}.
Arguments receive {_ _ _ _ _ _}.
Arguments build_contract {_ _ _ _ _ _}.

Program Definition contract_to_weak_contract
          {Setup Msg State : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          (c : Contract Setup Msg State) : WeakContract :=
      let weak_init chain ctx ser_setup :=
          do setup <- deserialize ser_setup;
          do state <- c.(init) chain ctx setup;
          Some (serialize state) in
      let weak_recv chain ctx ser_state ser_msg_opt :=
          do state <- deserialize ser_state;
          match ser_msg_opt with
          | Some ser_msg =>
            do msg <- deserialize ser_msg;
            do '(new_state, acts) <- c.(receive) chain ctx state (Some msg);
            Some (serialize new_state, acts)
          | None =>
            do '(new_state, acts) <- c.(receive) chain ctx state None;
            Some (serialize new_state, acts)
          end in
      build_weak_contract weak_init _ weak_recv _.
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
  + destruct (deserialize _); auto; simpl.
    now rewrite receive_proper.
  + now rewrite receive_proper.
Qed.

Coercion contract_to_weak_contract : Contract >-> WeakContract.

(* Deploy a strongly typed contract with some amount and setup *)
Definition create_deployment
          {Setup Msg State : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          (amount : Amount)
          (contract : Contract Setup Msg State)
          (setup : Setup) : ActionBody :=
  act_deploy amount contract (serialize setup).

(* The contract interface is the main mechanism allowing a deployed
contract to interact with another deployed contract. This hides
the ugly details of everything being SerializedValue away from contracts. *)
Record ContractInterface {Msg : Type} :=
  build_contract_interface {
    (* The address of the contract being interfaced with *)
    contract_address : Address;
    (* Make an action sending money and optionally a message to the contract *)
    send : Amount -> option Msg -> ActionBody;
  }.

Arguments ContractInterface _ : clear implicits.

Definition get_contract_interface
          (chain : Chain) (addr : Address)
          (Msg : Type) `{Serializable Msg}
  : option (ContractInterface Msg) :=
  let ifc_send amount msg :=
      match msg with
      | None => act_transfer addr amount
      | Some msg => act_call addr amount (serialize msg)
      end in
  Some {| contract_address := addr; send := ifc_send; |}.

Section Semantics.
Instance chain_settable : Settable _ :=
  settable! build_chain
  <chain_height; current_slot; finalized_height; account_balance>.

Definition add_balance (addr : Address) (amount : Amount) (map : Address -> Amount) :
  Address -> Amount :=
  fun a => if (a =? addr)%address
           then (amount + map a)%Z
           else map a.

Definition set_chain_contract_state
           (addr : Address) (state : SerializedValue)
           (map : Address -> option SerializedValue)
  : Address -> option SerializedValue :=
  fun a => if (a =? addr)%address
           then Some state
           else map a.

Record Environment :=
  build_env {
    env_chain :> Chain;
    env_contracts : Address -> option WeakContract;
    env_contract_states : Address -> option SerializedValue;
  }.

(* Furthermore we define extensional equality for such environments. *)
Record EnvironmentEquiv (e1 e2 : Environment) : Prop :=
  build_env_equiv {
    chain_equiv : ChainEquiv e1 e2;
    contracts_eq : forall a, env_contracts e1 a = env_contracts e2 a;
    contract_states_eq : forall addr, env_contract_states e1 addr = env_contract_states e2 addr;
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

Global Instance environment_equiv_contract_states_proper :
  Proper (EnvironmentEquiv ==> eq ==> eq) env_contract_states.
Proof. repeat intro; subst; apply contract_states_eq; assumption. Qed.

Global Instance environment_equiv_chain_equiv_proper :
  Proper (EnvironmentEquiv ==> ChainEquiv) env_chain.
Proof. repeat intro; apply chain_equiv; assumption. Qed.

Instance env_settable : Settable _ :=
  settable! build_env <env_chain; env_contracts; env_contract_states>.

Definition transfer_balance (from to : Address) (amount : Amount) (env : Environment) :=
  env<|env_chain; account_balance ::= add_balance to amount|>
     <|env_chain; account_balance ::= add_balance from (-amount)|>.

Definition add_contract (addr : Address) (contract : WeakContract) (env : Environment)
  : Environment :=
  env<|env_contracts ::=
    fun f a =>
      if (a =? addr)%address
      then Some contract
      else f a|>.

Definition set_contract_state
           (addr : Address) (state : SerializedValue) (env : Environment) :=
  env<|env_contract_states ::= set_chain_contract_state addr state|>.

Ltac rewrite_environment_equiv :=
  match goal with
  | [H: EnvironmentEquiv _ _ |- _] => rewrite H in *
  end.

Ltac solve_proper :=
  apply build_env_equiv;
  [apply build_chain_equiv| |];
  cbn;
  repeat intro;
  repeat rewrite_environment_equiv;
  auto.

Global Instance transfer_balance_proper :
  Proper (eq ==> eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) transfer_balance.
Proof.
  repeat intro; subst.
  unfold transfer_balance, add_balance.
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
  unfold set_contract_state, set_chain_contract_state.
  solve_proper.
Qed.

Local Open Scope Z.
(* Next we define how actions are executed. It specifies how an action
changes an environment and which external actions to execute after it.
Note that there can be multiple ways to execute an action. For example, if
the action says to deploy a contract, the implementation is responsible for
selecting which address the new contract should get. *)
Inductive ActionEvaluation :
  Environment -> Action ->
  Environment -> list Action -> Type :=
  | eval_transfer :
      forall {pre : Environment}
             {act : Action}
             {new_env : Environment}
             (from to : Address)
             (amount : Amount),
        amount <= account_balance pre from ->
        address_is_contract to = false ->
        act = build_act from (act_transfer to amount) ->
        EnvironmentEquiv
          new_env
          (transfer_balance from to amount pre) ->
        ActionEvaluation pre act new_env []
  | eval_deploy :
      forall {pre : Environment}
             {act : Action}
             {new_env : Environment}
             (from to : Address)
             (amount : Amount)
             (wc : WeakContract)
             (setup : SerializedValue)
             (state : SerializedValue),
      amount <= account_balance pre from ->
      address_is_contract to = true ->
      env_contracts pre to = None ->
      act = build_act from (act_deploy amount wc setup) ->
      wc_init
        wc
        (transfer_balance from to amount pre)
        (build_ctx from to amount)
        setup = Some state ->
      EnvironmentEquiv
        new_env
        (set_contract_state to state (add_contract to wc (transfer_balance from to amount pre))) ->
      ActionEvaluation pre act new_env []
  | eval_call :
      forall {pre : Environment}
             {act : Action}
             {new_env : Environment}
             {new_acts : list Action}
             (from to : Address)
             (amount : Amount)
             (wc : WeakContract)
             (msg : option SerializedValue)
             (prev_state : SerializedValue)
             (new_state : SerializedValue)
             (resp_acts : list ActionBody),
      amount <= account_balance pre from ->
      env_contracts pre to = Some wc ->
      env_contract_states pre to = Some prev_state ->
      act = build_act from (match msg with
                            | None => act_transfer to amount
                            | Some msg => act_call to amount msg
                            end) ->
      wc_receive
        wc
        (transfer_balance from to amount pre)
        (build_ctx from to amount)
        prev_state
        msg = Some (new_state, resp_acts) ->
      new_acts = map (build_act to) resp_acts ->
      EnvironmentEquiv
        new_env
        (set_contract_state to new_state (transfer_balance from to amount pre)) ->
      ActionEvaluation pre act new_env new_acts.

Section Accessors.
Context {pre : Environment} {act : Action}
        {post : Environment} {new_acts : list Action}
        (eval : ActionEvaluation pre act post new_acts).

Definition eval_from : Address :=
  match eval with
  | eval_transfer from _ _ _ _ _ _
  | eval_deploy from _ _ _ _ _ _ _ _ _ _ _
  | eval_call from _ _ _ _ _ _ _ _ _ _ _ _ _ _ => from
  end.

Definition eval_to : Address :=
  match eval with
  | eval_transfer _ to _ _ _ _ _
  | eval_deploy _ to _ _ _ _ _ _ _ _ _ _
  | eval_call _ to _ _ _ _ _ _ _ _ _ _ _ _ _ => to
  end.

Definition eval_amount : Amount :=
  match eval with
  | eval_transfer _ _ amount _ _ _ _
  | eval_deploy _ _ amount _ _ _ _ _ _ _ _ _
  | eval_call _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ => amount
  end.
End Accessors.

Section Theories.
Context {pre : Environment} {act : Action}
        {post : Environment} {new_acts : list Action}
        (eval : ActionEvaluation pre act post new_acts).

Lemma account_balance_post (addr : Address) :
  account_balance post addr =
  account_balance pre addr
  + (if (addr =? eval_to eval)%address then eval_amount eval else 0)
  - (if (addr =? eval_from eval)%address then eval_amount eval else 0).
Proof.
  destruct eval; cbn; rewrite_environment_equiv; cbn;
    unfold add_balance; destruct_address_eq; lia.
Qed.

Lemma account_balance_post_to :
  eval_from eval <> eval_to eval ->
  account_balance post (eval_to eval) =
  account_balance pre (eval_to eval) + eval_amount eval.
Proof.
  intros neq.
  rewrite account_balance_post.
  rewrite address_eq_refl, address_eq_ne by auto.
  lia.
Qed.

Lemma account_balance_post_from :
  eval_from eval <> eval_to eval ->
  account_balance post (eval_from eval) =
  account_balance pre (eval_from eval) - eval_amount eval.
Proof.
  intros neq.
  rewrite account_balance_post.
  rewrite address_eq_refl, address_eq_ne by auto.
  lia.
Qed.

Lemma account_balance_post_irrelevant (addr : Address) :
  addr <> eval_from eval ->
  addr <> eval_to eval ->
  account_balance post addr = account_balance pre addr.
Proof.
  intros neq_from neq_to.
  rewrite account_balance_post.
  repeat rewrite address_eq_ne by auto.
  lia.
Qed.

Lemma chain_height_post_action : chain_height post = chain_height pre.
Proof. destruct eval; rewrite_environment_equiv; auto. Qed.

Lemma current_slot_post_action : current_slot post = current_slot pre.
Proof. destruct eval; rewrite_environment_equiv; auto. Qed.

Lemma finalized_height_post_action : finalized_height post = finalized_height pre.
Proof. destruct eval; rewrite_environment_equiv; auto. Qed.

Lemma contracts_post_pre_none contract :
  env_contracts post contract = None ->
  env_contracts pre contract = None.
Proof.
  intros H.
  destruct eval; rewrite_environment_equiv; auto.
  cbn in *.
  destruct_address_eq; congruence.
Qed.
End Theories.

Section Trace.

Record BlockHeader :=
  build_block_Header {
    block_height : nat;
    block_slot : nat;
    block_finalized_height : nat;
    block_reward : Amount;
    block_creator : Address;
  }.

Definition add_new_block_to_env
           (header : BlockHeader) (env : Environment) : Environment :=
  env<|env_chain; chain_height := block_height header|>
     <|env_chain; current_slot := block_slot header|>
     <|env_chain; finalized_height := block_finalized_height header|>
     <|env_chain; account_balance ::=
         add_balance (block_creator header) (block_reward header)|>.

(* Todo: this should just be a computation. But I still do not *)
(* know exactly what the best way of working with reflect is *)
Local Open Scope nat.
Definition act_is_from_account (act : Action) : Prop :=
  address_is_contract (act_from act) = false.

Record IsValidNextBlock (header : BlockHeader) (chain : Chain) : Prop :=
  build_is_valid_next_block {
    valid_height : block_height header = S (chain_height chain);
    valid_slot : block_slot header > current_slot chain;
    valid_finalized_height :
      block_finalized_height header >= finalized_height chain /\
      block_finalized_height header < block_height header;
    valid_creator : address_is_contract (block_creator header) = false;
    valid_reward : (block_reward header >= 0)%Z;
  }.

Record ChainState :=
  build_chain_state {
    chain_state_env :> Environment;
    chain_state_queue : list Action;
  }.

Global Instance chain_state_settable : Settable _ :=
  settable! build_chain_state <chain_state_env; chain_state_queue>.

Inductive ChainStep : ChainState -> ChainState -> Type :=
| step_block :
    forall {prev next : ChainState}
           (header : BlockHeader),
      chain_state_queue prev = [] ->
      IsValidNextBlock header prev ->
      Forall act_is_from_account (chain_state_queue next) ->
      EnvironmentEquiv
        next
        (add_new_block_to_env header prev) ->
      ChainStep prev next
| step_action :
    forall {prev next : ChainState}
           (act : Action)
           (acts : list Action)
           (new_acts : list Action),
      chain_state_queue prev = act :: acts ->
      ActionEvaluation prev act next new_acts ->
      chain_state_queue next = new_acts ++ acts ->
      ChainStep prev next
| step_permute :
    forall {prev next : ChainState},
      chain_state_env prev = chain_state_env next ->
      Permutation (chain_state_queue prev) (chain_state_queue next) ->
      ChainStep prev next.

Definition empty_state : ChainState :=
  {| chain_state_env :=
       {| env_chain :=
            {| chain_height := 0;
               current_slot := 0;
               finalized_height := 0;
               account_balance a := 0%Z; |};
          env_contract_states a := None;
          env_contracts a := None; |};
     chain_state_queue := [] |}.

(* The ChainTrace captures that there is a valid execution where,
starting from one environment and queue of actions, we end up in a
different environment and queue of actions. *)
Definition ChainTrace := ChainedList ChainState ChainStep.

(* Additionally, a state is reachable if there is a trace ending in this trace. *)
Definition reachable (state : ChainState) : Prop :=
  inhabited (ChainTrace empty_state state).

(* We define a transaction as a "fully specified" action, recording all info. For
example, a transaction contains the contract address that was created when a contract
is deployed. This is more about bridging the gap between our definitions and what
a normal blockchain is. Each evaluation of an action in the blockchain corresponds to
a transaction, so we can go from a trace to a list of transactions. *)
Inductive TxBody :=
  | tx_empty
  | tx_deploy (wc : WeakContract) (setup : SerializedValue)
  | tx_call (msg : option SerializedValue).

Record Tx :=
  build_tx {
      tx_from : Address;
      tx_to : Address;
      tx_amount : Amount;
      tx_body : TxBody;
  }.

Definition eval_tx {pre : Environment} {act : Action}
                   {post : Environment} {new_acts : list Action}
                   (step : ActionEvaluation pre act post new_acts) : Tx :=
  match step with
  | eval_transfer from to amount _ _ _ _ =>
    build_tx from to amount tx_empty
  | eval_deploy from to amount wc setup _ _ _ _ _ _ _ =>
    build_tx from to amount (tx_deploy wc setup)
  | eval_call from to amount _ msg _ _ _ _ _ _ _ _ _ _ =>
    build_tx from to amount (tx_call msg)
  end.

Fixpoint trace_txs {from to : ChainState} (trace : ChainTrace from to) : list Tx :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ eval _ => eval_tx eval :: trace_txs trace'
    | _ => trace_txs trace'
    end
  | _ => []
  end.

Definition incoming_txs
           {from to : ChainState}
           (trace : ChainTrace from to)
           (addr : Address) : list Tx :=
  filter (fun tx => (tx_to tx =? addr)%address) (trace_txs trace).

Definition outgoing_txs
           {from to : ChainState}
           (trace : ChainTrace from to)
           (addr : Address) : list Tx :=
  filter (fun tx => (tx_from tx =? addr)%address) (trace_txs trace).

Fixpoint trace_blocks {from to : ChainState}
         (trace : ChainTrace from to) : list BlockHeader :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_block header _ _ _ _ =>
      header :: trace_blocks trace'
    | _ => trace_blocks trace'
    end
  | clnil => []
  end.

Definition created_blocks
           {from to : ChainState} (trace : ChainTrace from to)
           (creator : Address) : list BlockHeader :=
  filter (fun b => (block_creator b =? creator)%address)
         (trace_blocks trace).

Section Theories.
Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
        [prev next header queue_prev valid_header acts_from_accs env_eq|
         prev next act acts new_acts queue_prev eval queue_new|
         prev next prev_next perm]
  end.

Ltac destruct_action_eval :=
  match goal with
  | [eval: ActionEvaluation _ _ _ _ |- _] => destruct eval
  end.

Lemma contract_addr_format {to} (addr : Address) (wc : WeakContract) :
  reachable to ->
  env_contracts to addr = Some wc ->
  address_is_contract addr = true.
Proof.
  intros [trace] contract_at_addr.
  remember empty_state eqn:eq.
  induction trace; rewrite eq in *; clear eq.
  - cbn in *; congruence.
  - destruct_chain_step.
    + rewrite_environment_equiv; cbn in *; auto.
    + destruct_action_eval; rewrite_environment_equiv; cbn in *; destruct_address_eq; subst; auto.
    + intuition.
Qed.

Lemma new_acts_no_out_queue addr1 addr2 new_acts resp_acts :
  addr1 <> addr2 ->
  new_acts = map (build_act addr2) resp_acts ->
  Forall (fun a => (act_from a =? addr1)%address = false) new_acts.
Proof.
  intros neq ?; subst.
  induction resp_acts; cbn; auto.
  constructor; destruct_address_eq; cbn in *; congruence.
Qed.

Local Open Scope address.
(* This next lemma shows that any for a full chain trace,
the ending state will not have any queued actions from
undeployed contracts. *)
Lemma undeployed_contract_no_out_queue contract state :
  reachable state ->
  address_is_contract contract = true ->
  env_contracts state contract = None ->
  Forall (fun act => (act_from act =? contract) = false) (chain_state_queue state).
Proof.
  intros [trace] is_contract.
  remember empty_state eqn:eq.
  induction trace;
    intros undeployed; rewrite eq in *; clear eq; cbn; auto.
  destruct_chain_step; [|destruct_action_eval|];
    try rewrite_environment_equiv;
    repeat
      match goal with
      | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
      end;
    cbn in *.
  - (* New block *)
    match goal with
    | [H: Forall _ _ |- _] => induction H
    end; constructor; auto.
    destruct_address_eq; congruence.
  - (* Transfer step, just use IH *)
    eapply list.Forall_cons; eauto.
  - (* Deploy step. First show that it is not to contract and then use IH. *)
    destruct_address_eq; try congruence.
    eapply list.Forall_cons; eauto.
  - (* Call. Show that it holds for new actions as it is from *)
    (* another contract, and use IH for remaining. *)
    apply list.Forall_app.
    assert (contract <> to) by congruence.
    split; [eapply new_acts_no_out_queue|eapply list.Forall_cons]; eauto.
  - (* Permutation *)
    subst.
    specialize_hypotheses.
    match goal with
    | [prev_eq_new: _ = _, perm: Permutation _ _ |- _] =>
      now rewrite prev_eq_new in *; rewrite <- perm; auto
    end.
Qed.

(* With this lemma proven, we can show that the (perhaps seemingly stronger)
fact, that an undeployed contract has no outgoing txs, holds. *)
Lemma undeployed_contract_no_out_txs
      contract state (trace : ChainTrace empty_state state) :
  address_is_contract contract = true ->
  env_contracts state contract = None ->
  outgoing_txs trace contract = [].
Proof.
  intros is_contract undeployed.
  remember empty_state eqn:eq.
  induction trace; cbn; auto.
  destruct_chain_step.
  - (* New block *)
    rewrite_environment_equiv; auto.
  - (* In these steps we will use that the queue did not contain txs to the contract. *)
    Hint Resolve contracts_post_pre_none : core.
    Hint Unfold reachable : core.
    subst.
    cbn.
    pose proof
         (undeployed_contract_no_out_queue
            contract prev
            ltac:(auto) ltac:(auto) ltac:(eauto)) as Hqueue.
    repeat
      match goal with
      | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
      end.
    inversion_clear Hqueue.
    destruct_action_eval; rewrite_environment_equiv;
      subst;
      cbn in *;
      destruct_address_eq;
      subst; try tauto; congruence.
  - match goal with
    | [H: _ = _ |- _] => rewrite H in *; auto
    end.
Qed.

Lemma undeployed_contract_no_in_txs
      contract state (trace : ChainTrace empty_state state) :
  address_is_contract contract = true ->
  env_contracts state contract = None ->
  incoming_txs trace contract = [].
Proof.
  intros is_contract undeployed.
  remember empty_state eqn:eq.
  induction trace; cbn; auto.
  destruct_chain_step.
  - (* New block *)
    rewrite_environment_equiv; auto.
  - destruct_action_eval; rewrite_environment_equiv;
      cbn in *;
      destruct_address_eq; auto; subst; congruence.
  - match goal with
    | [H: _ = _ |- _] => rewrite H in *; auto
    end.
Qed.

Local Open Scope Z.
Lemma account_balance_trace state (trace : ChainTrace empty_state state) addr :
  account_balance state addr =
  sumZ tx_amount (incoming_txs trace addr) +
  sumZ block_reward (created_blocks trace addr) -
  sumZ tx_amount (outgoing_txs trace addr).
Proof.
  unfold incoming_txs, outgoing_txs.
  remember empty_state as from_state.
  induction trace; [|destruct_chain_step].
  - subst. cbn. lia.
  - (* Block *)
    rewrite_environment_equiv.
    cbn.
    fold (created_blocks trace addr).
    unfold add_balance.
    rewrite IHtrace by auto.
    destruct_address_eq; subst; cbn; lia.
  - (* Step *)
    cbn.
    destruct_action_eval; cbn; rewrite_environment_equiv; cbn.
    all: fold (created_blocks trace addr); unfold add_balance; rewrite IHtrace by auto.
    all: destruct_address_eq; cbn; lia.
  - cbn.
    rewrite <- prev_next.
    auto.
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
      (builder : builder_type)
      (header : BlockHeader)
      (actions : list Action) :
      option builder_type;

    builder_trace (builder : builder_type) :
      ChainTrace empty_state (build_chain_state (builder_env builder) []);
  }.

Global Coercion builder_type : ChainBuilderType >-> Sortclass.
Global Coercion builder_env : builder_type >-> Environment.
End Blockchain.

Arguments init {_ _ _ _ _ _ _}.
Arguments receive {_ _ _ _ _ _ _}.
Arguments build_contract {_ _ _ _ _ _ _}.
Arguments ContractInterface {_} _.
Arguments build_contract_interface {_ _ _ _}.

Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
        [prev next header queue_prev valid_header acts_from_accs env_eq|
         prev next act acts new_acts queue_prev eval queue_new|
         prev next prev_next perm]
  end.

Ltac destruct_action_eval :=
  match goal with
  | [eval: ActionEvaluation _ _ _ _ |- _] => destruct eval
  end.

Ltac rewrite_environment_equiv :=
  match goal with
  | [eq: EnvironmentEquiv _ _ |- _] => rewrite eq in *
  end.
