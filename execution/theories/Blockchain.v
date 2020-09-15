(* This file defines blockchains, both a contract's view (which is
more computational) and the semantics of executing smart contracts
in a blockchain.

The most important types are:

* The ChainBase type, describing basic assumptions made of any blockchain.
In most cases we will abstract over this type.

* The Chain type, describing a smart contract's view of the blockchain.
This is the the data that can be accessed by smart contracts.

* The Action type, describing how smart contracts (and external users)
interact with the blockchain. We allow transfers, calls and deployment
of contracts.

* The WeakContract type, describing a "weak" or "stringly" typed
version of smart contracts. Contracts are just two functions init and
receive to respectively initialize state on deployment and to update
state when receiving messages. The weak version of contracts means that
the state/message/setup types, which would normally vary with contracts,
are stored in a serialized format.

* The Contract type, describing a more strongly typed version of a contract.
This is the same as the above except we abstract over the appropriate types.
Users of the framework will mostly need to deal with this.

The next types deal with semantics.

* The Environment type. This augments the Chain type with more information.
Environment can be thought of as the information that a realistic blockchain
implementation would need to keep track of to implement operations. For instance,
it is reasonable to assume that an implementation needs to access the state of
contracts, but not to assume that it needs to store the full transaction history
of all addresses.

* The ActionEvaluation type. This specifies how to evaluate actions returned by
contracts or input in blocks. This related an environment and action to a new
environment and list of new actions to execute.

* The ChainState type. This augments the Environment type with a queue of
"outstanding" actions that need to be executed. For instance, when a block is
added, its actions are put into this queue.

* The ChainStep type. This specifies how the blockchain should execute smart
contracts, and how new blocks are added. It relates a ChainState to a new ChainState.
There are steps to allow adding blocks, evaluating actions in the queue and to
permute the queue (allowing to model any execution order).

* The ChainTrace type. This just represents a sequence of steps. If a trace ends
in a state it means that state is reachable and there is a "semantically correct"
way of executing to get to this state. This type records the full history of a
blockchain's execution and it would thus be unrealistic to extract.

* The ChainBuilderType type. This is a typeclass for implementations of blockchains,
where these implementations need to prove that they satisfy our semantics.

*)


From Coq Require Import Arith ZArith.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import Permutation.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.
Require Import Automation.
Require Import ChainedList.
Require Import Extras.
Require Import Monads.
Require Import ResultMonad.
Require Import Serializable.
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
Context {Base : ChainBase}.

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

Definition act_body_amount (ab : ActionBody) : Z :=
  match ab with
  | act_transfer _ amount
  | act_call _ amount _
  | act_deploy amount _ _ => amount
  end.

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

Definition act_amount (a : Action) := act_body_amount (act_body a).

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

Global Arguments init {_ _ _ _ _ _}.
Global Arguments receive {_ _ _ _ _ _}.
Global Arguments build_contract {_ _ _ _ _ _}.

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
  repeat intro.
  subst.
  subst weak_init.
  cbn.
  destruct (deserialize _); auto.
  cbn.
  now rewrite init_proper.
Qed.
Next Obligation.
  repeat intro.
  subst.
  subst weak_recv.
  cbn.
  destruct (deserialize _); auto.
  cbn.
  destruct_match.
  - destruct (deserialize _); auto.
    cbn.
    now rewrite receive_proper.
  - now rewrite receive_proper.
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

Global Arguments ContractInterface _ : clear implicits.

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
Global Instance chain_settable : Settable _ :=
  settable! build_chain
  <chain_height; current_slot; finalized_height; account_balance>.

Definition add_balance (addr : Address) (amount : Amount) (map : Address -> Amount) :
  Address -> Amount :=
  fun a => if (a =? addr)%address
           then (amount + map a)%Z
           else map a.

Global Arguments add_balance _ _ _ /.

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

(* Strongly typed version of contract state *)
Definition contract_state
           {A : Type} `{Serializable A}
           (env : Environment) (addr : Address) : option A :=
  env_contract_states env addr >>= deserialize.

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

Global Instance environment_equiv_env_contracts_proper :
  Proper (EnvironmentEquiv ==> eq ==> eq) env_contracts.
Proof. repeat intro; subst; apply contracts_eq; assumption. Qed.

Global Instance environment_equiv_env_contract_states_proper :
  Proper (EnvironmentEquiv ==> eq ==> eq) env_contract_states.
Proof. repeat intro; subst; apply contract_states_eq; assumption. Qed.

Global Instance environment_equiv_env_chain_equiv_proper :
  Proper (EnvironmentEquiv ==> ChainEquiv) env_chain.
Proof. repeat intro; apply chain_equiv; assumption. Qed.

Global Instance environment_equiv_contract_state_proper
  {A : Type} `{Serializable A} :
  Proper (EnvironmentEquiv ==> eq ==> (@eq (option A))) contract_state.
Proof.
  intros ? ? env_eq ? ? ?.
  subst.
  unfold contract_state.
  now rewrite env_eq.
Qed.

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

(* set_chain_contract_state updates a map (function) by returning a
   new map (function).  If this function is immediately applied to a
   key, then unfold it. *)
Global Arguments set_chain_contract_state _ _ _ /.

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
Inductive ActionEvaluation
          (prev_env : Environment) (act : Action)
          (new_env : Environment) (new_acts : list Action) : Type :=
  | eval_transfer :
      forall (from_addr to_addr : Address)
             (amount : Amount),
        amount >= 0 ->
        amount <= account_balance prev_env from_addr ->
        address_is_contract to_addr = false ->
        act = build_act from_addr (act_transfer to_addr amount) ->
        EnvironmentEquiv
          new_env
          (transfer_balance from_addr to_addr amount prev_env) ->
        new_acts = [] ->
        ActionEvaluation prev_env act new_env new_acts
  | eval_deploy :
      forall (from_addr to_addr : Address)
             (amount : Amount)
             (wc : WeakContract)
             (setup : SerializedValue)
             (state : SerializedValue),
      amount >= 0 ->
      amount <= account_balance prev_env from_addr ->
      address_is_contract to_addr = true ->
      env_contracts prev_env to_addr = None ->
      act = build_act from_addr (act_deploy amount wc setup) ->
      wc_init
        wc
        (transfer_balance from_addr to_addr amount prev_env)
        (build_ctx from_addr to_addr amount)
        setup = Some state ->
      EnvironmentEquiv
        new_env
        (set_contract_state
           to_addr state (add_contract
                       to_addr wc (transfer_balance from_addr to_addr amount prev_env))) ->
      new_acts = [] ->
      ActionEvaluation prev_env act new_env new_acts
  | eval_call :
      forall (from_addr to_addr : Address)
             (amount : Amount)
             (wc : WeakContract)
             (msg : option SerializedValue)
             (prev_state : SerializedValue)
             (new_state : SerializedValue)
             (resp_acts : list ActionBody),
      amount >= 0 ->
      amount <= account_balance prev_env from_addr ->
      env_contracts prev_env to_addr = Some wc ->
      env_contract_states prev_env to_addr = Some prev_state ->
      act = build_act from_addr
                      (match msg with
                       | None => act_transfer to_addr amount
                       | Some msg => act_call to_addr amount msg
                       end) ->
      wc_receive
        wc
        (transfer_balance from_addr to_addr amount prev_env)
        (build_ctx from_addr to_addr amount)
        prev_state
        msg = Some (new_state, resp_acts) ->
      new_acts = map (build_act to_addr) resp_acts ->
      EnvironmentEquiv
        new_env
        (set_contract_state to_addr new_state (transfer_balance from_addr to_addr amount prev_env)) ->
      ActionEvaluation prev_env act new_env new_acts.

Global Arguments eval_transfer {_ _ _ _}.
Global Arguments eval_deploy {_ _ _ _}.
Global Arguments eval_call {_ _ _ _}.

Section Accessors.
Context {pre : Environment} {act : Action}
        {post : Environment} {new_acts : list Action}
        (eval : ActionEvaluation pre act post new_acts).

Definition eval_from : Address :=
  match eval with
  | eval_transfer from _ _ _ _ _ _ _ _
  | eval_deploy from _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_call from _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => from
  end.

Definition eval_to : Address :=
  match eval with
  | eval_transfer _ to _ _ _ _ _ _ _
  | eval_deploy _ to _ _ _ _ _ _ _ _ _ _ _ _
  | eval_call _ to _ _ _ _ _ _ _ _ _ _ _ _ _ _ => to
  end.

Definition eval_amount : Amount :=
  match eval with
  | eval_transfer _ _ amount _ _ _ _ _ _
  | eval_deploy _ _ amount _ _ _ _ _ _ _ _ _ _ _
  | eval_call _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ => amount
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
    destruct_address_eq; lia.
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

Lemma eval_amount_nonnegative : eval_amount eval >= 0.
Proof. now destruct eval. Qed.

Lemma eval_amount_le_account_balance :
  eval_amount eval <= account_balance pre (eval_from eval).
Proof. now destruct eval. Qed.

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

Inductive ChainStep (prev_bstate : ChainState) (next_bstate : ChainState) :=
| step_block :
    forall (header : BlockHeader),
      chain_state_queue prev_bstate = [] ->
      IsValidNextBlock header prev_bstate ->
      Forall act_is_from_account (chain_state_queue next_bstate) ->
      EnvironmentEquiv
        next_bstate
        (add_new_block_to_env header prev_bstate) ->
      ChainStep prev_bstate next_bstate
| step_action :
    forall (act : Action)
           (acts : list Action)
           (new_acts : list Action),
      chain_state_queue prev_bstate = act :: acts ->
      ActionEvaluation prev_bstate act next_bstate new_acts ->
      chain_state_queue next_bstate = new_acts ++ acts ->
      ChainStep prev_bstate next_bstate
| step_permute :
      chain_state_env prev_bstate = chain_state_env next_bstate ->
      Permutation (chain_state_queue prev_bstate) (chain_state_queue next_bstate) ->
      ChainStep prev_bstate next_bstate.

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

Definition outgoing_acts (state : ChainState) (addr : Address) : list ActionBody :=
  map act_body
      (filter (fun act => (act_from act =? addr)%address) (chain_state_queue state)).

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
  | eval_transfer from to amount _ _ _ _ _ _ =>
    build_tx from to amount tx_empty
  | eval_deploy from to amount wc setup _ _ _ _ _ _ _ _ _ =>
    build_tx from to amount (tx_deploy wc setup)
  | eval_call from to amount _ msg _ _ _ _ _ _ _ _ _ _ _ =>
    build_tx from to amount (tx_call msg)
  end.

Fixpoint trace_txs {from to : ChainState} (trace : ChainTrace from to) : list Tx :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ _ _ eval _ => eval_tx eval :: trace_txs trace'
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

Record ContractCallInfo (Msg : Type) :=
  build_call_info
  {
    call_from : Address;
    call_amount : Amount;
    call_msg : option Msg;
  }.

Global Arguments build_call_info {_}.
Global Arguments call_from {_}.
Global Arguments call_amount {_}.
Global Arguments call_msg {_}.

Fixpoint incoming_calls
           (Msg : Type) `{Serializable Msg}
           {from to : ChainState}
           (trace : ChainTrace from to)
           (caddr : Address) : option (list (ContractCallInfo Msg)) :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ _ _ (eval_call from to amount _ msg _ _ _ _ _ _ _ _ _ _ _) _ =>
      if (to =? caddr)%address then
        (* If there is a message it should deserialize correctly,
           otherwise the entire operation returns None. *)
        do hd_msg <- match msg with
                     | Some msg =>
                       match deserialize msg with
                       | Some msg => Some (Some msg)
                       | None => None
                       end
                     | None => Some None
                     end;
        do tl <- incoming_calls Msg trace' caddr;
        Some (build_call_info from amount hd_msg :: tl)
      else
        incoming_calls Msg trace' caddr
    | _ => incoming_calls Msg trace' caddr
    end
  | _ => Some []
  end.

Record DeploymentInfo (Setup : Type) :=
  build_deployment_info
  {
    deployment_from : Address;
    deployment_amount : Amount;
    deployment_setup : Setup;
  }.

Global Arguments build_deployment_info {_}.
Global Arguments deployment_from {_}.
Global Arguments deployment_amount {_}.
Global Arguments deployment_setup {_}.

Fixpoint deployment_info
           (Setup : Type) `{Serializable Setup}
           {from to : ChainState}
           (trace : ChainTrace from to)
           (caddr : Address) : option (DeploymentInfo Setup) :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ _ _ (eval_deploy from to amount _ setup _ _ _ _ _ _ _ _ _) _ =>
      if (to =? caddr)%address then
        do setup <- deserialize setup;
        Some (build_deployment_info from amount setup)
      else
        deployment_info Setup trace' caddr
    | _ => deployment_info Setup trace' caddr
    end
  | clnil => None
  end.

Fixpoint trace_blocks {from to : ChainState}
         (trace : ChainTrace from to) : list BlockHeader :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_block _ _ header _ _ _ _ =>
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

Definition is_deploy (ac : ActionBody) : bool :=
  match ac with
  | act_transfer _ _ => false
  | act_call _ _ _ => false
  | act_deploy _ _ _ => true
  end.

Definition is_call (ac : ActionBody) : bool :=
  match ac with
  | act_transfer _ _ => false
  | act_call _ _ _ => true
  | act_deploy _ _ _ => false
  end.

Definition is_transfer (ac : ActionBody) : bool :=
  match ac with
  | act_transfer _ _ => true
  | act_call _ _ _ => false
  | act_deploy _ _ _ => false
  end.

Section Theories.
Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
        [header queue_prev valid_header acts_from_accs env_eq|
         act acts new_acts queue_prev eval queue_new|
         prev_next perm]
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

Lemma outgoing_acts_after_block_nil bstate addr :
  Forall act_is_from_account (chain_state_queue bstate) ->
  address_is_contract addr = true ->
  outgoing_acts bstate addr = [].
Proof.
  intros all is_contract.
  unfold outgoing_acts.
  induction (chain_state_queue bstate); auto.
  cbn.
  inversion_clear all.
  destruct_address_eq; subst; auto.
  unfold act_is_from_account in *.
  congruence.
Qed.

Lemma outgoing_acts_after_deploy_nil bstate addr :
  Forall (fun act => (act_from act =? addr)%address = false) (chain_state_queue bstate) ->
  outgoing_acts bstate addr = [].
Proof.
  intros all.
  unfold outgoing_acts.
  induction (chain_state_queue bstate) as [|hd tl IH]; auto.
  cbn in *.
  inversion_clear all.
  rewrite H.
  auto.
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
    subst;
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
    assert (contract <> to_addr) by congruence.
    split; [eapply new_acts_no_out_queue|eapply list.Forall_cons]; eauto.
  - (* Permutation *)
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
  remember empty_state; induction trace; subst; cbn; auto.
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
            contract mid
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
  remember empty_state; induction trace; subst; cbn; auto.
  destruct_chain_step.
  - (* New block *)
    rewrite_environment_equiv; auto.
  - destruct_action_eval; rewrite_environment_equiv;
      cbn in *;
      destruct_address_eq; auto; subst; congruence.
  - rewrite prev_next in *; auto.
Qed.

Lemma deployment_info_some
      Setup `{Serializable Setup}
      {to} (trace : ChainTrace empty_state to) caddr :
  deployment_info Setup trace caddr <> None ->
  env_contracts to caddr <> None.
Proof.
  remember empty_state; induction trace as [|? ? ? ? IH]; subst; cbn in *; try tauto.
  destruct_chain_step.
  - rewrite_environment_equiv.
    auto.
  - destruct_action_eval; rewrite_environment_equiv; auto.
    (* Deploy *)
    cbn in *.
    rewrite (address_eq_sym caddr).
    destruct_address_eq; try discriminate.
    auto.
  - rewrite <- prev_next; auto.
Qed.

Lemma deployment_info_addr_format
      Setup `{Serializable Setup} {to}
      (trace : ChainTrace empty_state to)
      caddr :
  deployment_info Setup trace caddr <> None ->
  address_is_contract caddr = true.
Proof.
  intros has_deployment_info.
  pose proof (deployment_info_some _ _ _ has_deployment_info).
  destruct (env_contracts to caddr) as [wc|] eqn:?; try congruence.
  eapply contract_addr_format; eauto.
Qed.

Lemma incoming_txs_contract
      caddr bstate (trace : ChainTrace empty_state bstate)
      Setup `{Serializable Setup} (depinfo : DeploymentInfo Setup)
      Msg `{Serializable Msg} (msgs : list (ContractCallInfo Msg)) :
  deployment_info Setup trace caddr = Some depinfo ->
  incoming_calls Msg trace caddr = Some msgs ->
  map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) (incoming_txs trace caddr) =
  map (fun call => (call_from call, caddr, call_amount call)) msgs ++
       [(deployment_from depinfo, caddr, deployment_amount depinfo)].
Proof.
  intros depinfo_eq calls_eq.
  enough ((env_contracts bstate caddr = None ->
           incoming_txs trace caddr = [] /\
           deployment_info Setup trace caddr = None /\
           incoming_calls Msg trace caddr = Some []) /\
          (env_contracts bstate caddr <> None ->
           deployment_info Setup trace caddr <> None ->
           incoming_calls Msg trace caddr <> None ->
           exists (depinfo : DeploymentInfo Setup)
                  (inc_calls : list (ContractCallInfo Msg))
                  (call_txs : list Tx) (dep_tx : Tx),
             deployment_info Setup trace caddr = Some depinfo /\
             incoming_calls Msg trace caddr = Some inc_calls /\
             incoming_txs trace caddr = call_txs ++ [dep_tx] /\
             map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) call_txs =
             map (fun call => (call_from call, caddr, call_amount call)) inc_calls /\
             (tx_from dep_tx, tx_to dep_tx, tx_amount dep_tx) =
             (deployment_from depinfo, caddr, deployment_amount depinfo))) as generalized.
  {
    rewrite depinfo_eq, calls_eq in *.
    destruct (env_contracts bstate caddr).
    - destruct generalized as [_ generalized].
      specialize (generalized ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
      destruct generalized as [? [? [? [? [? [? [-> [? ?]]]]]]]].
      rewrite map_app.
      cbn.
      congruence.
    - destruct generalized as [generalized _].
      specialize (generalized eq_refl).
      destruct generalized as [_ [? _]]; congruence.
  }

  assert (is_contract: address_is_contract caddr = true).
  { assert (deployment_info Setup trace caddr <> None) by congruence.
    eapply (deployment_info_addr_format Setup); eassumption. }

  clear depinfo_eq calls_eq depinfo msgs.

  remember empty_state; induction trace as [|? ? ? ? IH]; subst; cbn in *;
    try tauto.
  destruct_chain_step; cbn in *.
  - (* Add new block *)
    rewrite_environment_equiv.
    auto.
  - (* Evaluation *)
    destruct_action_eval; cbn in *; rewrite_environment_equiv.
    + (* Transfer *)
      destruct_address_eq; auto.
      subst.
      cbn.
      congruence.
    + (* Deploy *)
      cbn in *.
      rewrite (address_eq_sym caddr) in *.
      destruct_address_eq; auto.
      split; try discriminate.
      intros _ depinfo_ne_none calls_ne_none.
      subst.
      cbn in *.
      destruct (deserialize setup); cbn in *; try congruence.
      remember (build_deployment_info _ _ _) as depinfo.
      remember (build_tx _ _ _ _) as deptx.
      destruct IH as [IH _]; auto.
      specialize (IH ltac:(auto)).
      fold (incoming_txs trace caddr).
      destruct IH as [-> [? ->]].
      exists depinfo, [], [], deptx; subst; cbn in *.
      tauto.
    + (* Call *)
      destruct_address_eq; subst; auto.
      cbn in *.
      split; [intros; congruence|].
      destruct IH as [_ IH]; auto.
      intros _ deploy_info calls.
      destruct (match msg with | Some _ => _ | _ => Some None end);
        cbn in *; try congruence.
      destruct (incoming_calls _ _) as [inc_calls|]; cbn in *; try congruence.
      unshelve epose proof (IH _ _ _) as IH; auto; try congruence.
      destruct IH as
          [depinfo [prev_calls
                      [prev_call_txs [dep_tx
                                        [depinfo_eq [inc_calls_eq
                                                       [inc_txs_eq [map_eq ?]]]]]]]].
      remember (build_tx _ _ _ _) as new_tx.
      remember (build_call_info _ _ _) as new_call.
      exists depinfo, (new_call :: inc_calls), (new_tx :: prev_call_txs), dep_tx.
      split; auto.
      split; auto.
      fold (incoming_txs trace caddr).
      rewrite inc_txs_eq.
      split; [now rewrite app_comm_cons|].
      inversion_clear inc_calls_eq.
      cbn.
      rewrite map_eq.
      subst; tauto.
  - (* Permutation *)
    rewrite <- prev_next; auto.
Qed.

Lemma undeployed_contract_no_in_calls
      {Msg} `{Serializable Msg}
      contract state (trace : ChainTrace empty_state state) :
  env_contracts state contract = None ->
  incoming_calls Msg trace contract = Some [].
Proof.
  unfold incoming_calls.
  intros undeployed.
  remember empty_state; induction trace; subst; cbn in *; auto.
  destruct_chain_step.
  - (* New block *)
    rewrite_environment_equiv; auto.
  - destruct_action_eval; rewrite_environment_equiv;
      cbn in *;
      destruct_address_eq; auto; subst; congruence.
  - rewrite prev_next in *; auto.
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
    rewrite IHtrace by auto.
    destruct_address_eq; subst; cbn; lia.
  - (* Step *)
    cbn.
    destruct_action_eval; cbn; rewrite_environment_equiv; cbn.
    all: fold (created_blocks trace addr); rewrite IHtrace by auto.
    all: destruct_address_eq; cbn; lia.
  - cbn.
    rewrite <- prev_next.
    auto.
Qed.

Lemma contract_no_created_blocks state (trace : ChainTrace empty_state state) addr :
  address_is_contract addr = true ->
  created_blocks trace addr = [].
Proof.
  intros is_contract.
  remember empty_state eqn:eq.
  induction trace; auto.
  destruct_chain_step; auto.
  cbn.
  subst.
  inversion valid_header.
  destruct (address_eqb_spec (block_creator header) addr); auto.
  congruence.
Qed.

Lemma undeployed_contract_balance_0 state addr :
  reachable state ->
  address_is_contract addr = true ->
  env_contracts state addr = None ->
  account_balance state addr = 0.
Proof.
  intros [trace] is_contract no_contract.
  rewrite (account_balance_trace _ trace); auto.
  rewrite undeployed_contract_no_out_txs, undeployed_contract_no_in_txs,
          contract_no_created_blocks; auto.
Qed.

Lemma account_balance_nonnegative state addr :
  reachable state ->
  account_balance state addr >= 0.
Proof.
  intros [trace].
  remember empty_state eqn:eq.
  induction trace; subst; cbn; try lia.
  specialize (IHtrace eq_refl).
  destruct_chain_step.
  - (* New block *)
    rewrite_environment_equiv.
    cbn.
    inversion valid_header.
    destruct_address_eq; lia.
  - (* Action evaluation *)
    rewrite (account_balance_post eval addr).
    pose proof (eval_amount_nonnegative eval).
    pose proof (eval_amount_le_account_balance eval).
    destruct_address_eq; subst; cbn in *; lia.
  - now rewrite <- prev_next.
Qed.

Lemma wc_init_strong {Setup Msg State : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          {contract : Contract Setup Msg State}
          {chain ctx setup result} :
  wc_init (contract : WeakContract) chain ctx setup = Some result ->
  exists setup_strong result_strong,
    deserialize setup = Some setup_strong /\
    serialize result_strong = result /\
    Blockchain.init contract chain ctx setup_strong = Some result_strong.
Proof.
  intros init.
  cbn in *.
  destruct (deserialize setup) as [setup_strong|] eqn:deser_setup;
    cbn in *; try congruence.
  exists setup_strong.
  destruct (Blockchain.init _ _ _ _) as [result_strong|] eqn:result_eq;
    cbn in *; try congruence.
  exists result_strong.
  repeat split; auto with congruence.
Qed.

Lemma wc_receive_strong {Setup Msg State : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          {contract : Contract Setup Msg State}
          {chain ctx prev_state msg new_state new_acts} :
  wc_receive (contract : WeakContract) chain ctx prev_state msg =
  Some (new_state, new_acts) ->
  exists prev_state_strong msg_strong new_state_strong,
    deserialize prev_state = Some prev_state_strong /\
    match msg_strong with
    | Some msg_strong => msg >>= deserialize = Some msg_strong
    | None => msg = None
    end /\
    serialize new_state_strong = new_state /\
    Blockchain.receive contract chain ctx prev_state_strong msg_strong =
    Some (new_state_strong, new_acts).
Proof.
  intros receive.
  cbn in *.
  destruct (deserialize prev_state) as [prev_state_strong|] eqn:deser_state;
    cbn in *; try congruence.
  exists prev_state_strong.
  exists (msg >>= deserialize).
  destruct msg as [msg|]; cbn in *.
  1: destruct (deserialize msg) as [msg_strong|];
    cbn in *; try congruence.
  all: destruct (Blockchain.receive _ _ _ _ _)
    as [[resp_state_strong resp_acts_strong]|] eqn:result_eq;
    cbn in *; try congruence.
  all: exists resp_state_strong.
  all: inversion_clear receive; auto.
Qed.

Lemma deployed_contract_state_typed
          {Setup Msg State : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          {contract : Contract Setup Msg State}
          {bstate : ChainState}
          {caddr} :
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  reachable bstate ->
  exists (cstate : State),
    contract_state bstate caddr = Some cstate.
Proof.
  intros contract_deployed [trace].
  destruct (contract_state bstate caddr) as [cstate|] eqn:eq;
    [exists cstate; auto|].
  unfold contract_state in *.
  (* Show that eq is a contradiction. *)
  remember empty_state; induction trace; subst; cbn in *; try congruence.
  destruct_chain_step.
  - (* New block, use IH *)
    rewrite_environment_equiv; auto.
  - (* Action evaluation *)
    destruct_action_eval; subst; rewrite_environment_equiv; cbn in *.
    (*destruct_action_eval; rewrite_environment_equiv; cbn in *.*)
    + (* Transfer, use IH *)
      auto.
    + (* Deployment *)
      destruct_address_eq; subst; auto.
      (* To this contract, show that deserialization would not fail. *)
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_init_strong ltac:(eassumption))
        as [setup_strong [result_strong [? [<- init]]]].
      cbn in eq.
      rewrite deserialize_serialize in eq; congruence.
    + (* Call *)
      destruct_address_eq; subst; auto.
      (* To this contract, show that deserialization would not fail. *)
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_receive_strong ltac:(eassumption))
        as [state_strong [msg_strong [resp_state_strong [? [? [<- receive]]]]]].
      cbn in eq.
      rewrite deserialize_serialize in eq; congruence.
  - (* Permutation *)
    rewrite prev_next in *.
    auto.
Qed.

Inductive TagFacts := tag_facts.
Inductive TagAddBlock := tag_add_block.
Inductive TagDeployment := tag_deployment.
Inductive TagOutgoingAct := tag_outgoing_act.
Inductive TagNonrecursiveCall := tag_nonrecursive_call.
Inductive TagRecursiveCall := tag_recursive_call.
Inductive TagPermuteQueue := tag_permute_queue.

Hint Constructors
     TagFacts TagAddBlock TagDeployment TagOutgoingAct
     TagNonrecursiveCall TagRecursiveCall TagPermuteQueue : core.

Lemma contract_induction
      {Setup Msg State : Type}
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      (contract : Contract Setup Msg State)
      (AddBlockFacts :
         forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                (new_height : nat) (new_slot : nat) (new_finalized_height : nat), Prop)
      (DeployFacts : forall (chain : Chain) (ctx : ContractCallContext), Prop)
      (CallFacts :
         forall (chain : Chain)
                (ctx : ContractCallContext)
                (cstate : State), Prop)
      (P : forall (chain_height : nat)
                  (current_slot : nat)
                  (finalized_height : nat)
                  (caddr : Address)
                  (deployment_info : DeploymentInfo Setup)
                  (cstate : State)
                  (balance : Amount)
                  (outgoing_actions_queued : list ActionBody)
                  (incoming_calls_seen : list (ContractCallInfo Msg))
                  (outgoing_txs_seen : list Tx), Prop) :

  (* Facts *)
  (forall (bstate_from bstate_to : ChainState) (step : ChainStep bstate_from bstate_to)
          (from_reachable : reachable bstate_from)
          (tag : TagFacts),
      match step with
      | step_block _ _ header _ _ _ _ =>
        AddBlockFacts (chain_height bstate_from)
                      (current_slot bstate_from)
                      (finalized_height bstate_from)
                      (block_height header)
                      (block_slot header)
                      (block_finalized_height header)
      | step_action _ _ _ _ _ _ (eval_deploy from to amount _ _ _ _ _ _ _ _ _ _ _) _ =>
        DeployFacts (transfer_balance from to amount bstate_from)
                    (build_ctx from to amount)
      | step_action _ _ _ _ _ _ (eval_call from to amount _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
        forall (cstate : State),
          env_contracts bstate_from to = Some (contract : WeakContract) ->
          contract_state bstate_from to = Some cstate ->
          CallFacts (transfer_balance from to amount bstate_from)
                    (build_ctx from to amount)
                    cstate
      | _ => Logic.True
      end) ->

  (* Add block *)
  (forall old_chain_height old_cur_slot old_fin_height
          new_chain_height new_cur_slot new_fin_height
          caddr dep_info state balance inc_calls out_txs
          (facts : AddBlockFacts old_chain_height old_cur_slot old_fin_height
                                 new_chain_height new_cur_slot new_fin_height)
          (IH : P old_chain_height old_cur_slot old_fin_height
                  caddr dep_info state balance [] inc_calls out_txs)
          (tag : TagAddBlock),
      P new_chain_height new_cur_slot new_fin_height
        caddr dep_info state balance [] inc_calls out_txs) ->

  (* Deploy contract *)
  (forall chain ctx setup result
          (facts : DeployFacts chain ctx)
          (init_some : init contract chain ctx setup = Some result)
          (tag : TagDeployment),
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (ctx_contract_address ctx)
        (build_deployment_info (ctx_from ctx) (ctx_amount ctx) setup)
        result
        (ctx_amount ctx)
        []
        []
        []) ->

  (* Transfer/call/deploy to someone else *)
  (forall height slot fin_height caddr dep_info cstate
          balance out_act out_acts inc_calls prev_out_txs tx
          (IH : P height slot fin_height caddr dep_info cstate balance
                  (out_act :: out_acts) inc_calls prev_out_txs)
          (tx_from_caddr : tx_from tx = caddr)
          (tx_amount_eq : tx_amount tx = act_body_amount out_act)
          (tx_act_match :
             match out_act with
             | act_transfer to amount =>
               tx_to tx = to /\ tx_amount tx = amount /\
               (tx_body tx = tx_empty \/ tx_body tx = tx_call None)
             | act_deploy amount wc setup =>
               tx_amount tx = amount /\ tx_body tx = tx_deploy wc setup
             | act_call to amount msg =>
               tx_to tx = to /\ tx_amount tx = amount /\ tx_body tx = tx_call (Some msg)
             end)
          (tag : TagOutgoingAct),
      P height slot fin_height caddr dep_info cstate (balance - act_body_amount out_act)
        out_acts inc_calls (tx :: prev_out_txs)) ->

  (* Non-recursive call *)
  (forall chain ctx dep_info prev_state msg
          prev_out_queue prev_inc_calls prev_out_txs
          new_state new_acts
          (from_other : ctx_from ctx <> ctx_contract_address ctx)
          (facts : CallFacts chain ctx prev_state)
          (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                  (ctx_contract_address ctx) dep_info prev_state
                  (account_balance chain (ctx_contract_address ctx) - ctx_amount ctx)
                  prev_out_queue prev_inc_calls prev_out_txs)
          (receive_some : receive contract chain ctx prev_state msg =
                          Some (new_state, new_acts))
          (tag : TagNonrecursiveCall),
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (ctx_contract_address ctx)
        dep_info
        new_state
        (account_balance chain (ctx_contract_address ctx))
        (new_acts ++ prev_out_queue)
        (build_call_info (ctx_from ctx) (ctx_amount ctx) msg :: prev_inc_calls)
        prev_out_txs) ->

  (* Recursive call *)
  (forall chain ctx dep_info prev_state msg
          head prev_out_queue prev_inc_calls prev_out_txs
          new_state new_acts
          (from_self : ctx_from ctx = ctx_contract_address ctx)
          (facts : CallFacts chain ctx prev_state)
          (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                  (ctx_contract_address ctx) dep_info prev_state
                  (account_balance chain (ctx_contract_address ctx))
                  (head :: prev_out_queue) prev_inc_calls prev_out_txs)
          (action_facts :
             match head with
             | act_transfer to amount => to = ctx_contract_address ctx /\
                                         amount = ctx_amount ctx /\
                                         msg = None
             | act_call to amount msg_ser => to = ctx_contract_address ctx /\
                                             amount = ctx_amount ctx /\
                                             msg <> None /\
                                             deserialize msg_ser = msg
             | _ => False
             end)
          (receive_some : receive contract chain ctx prev_state msg =
                          Some (new_state, new_acts))
          (tag : TagRecursiveCall),
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (ctx_contract_address ctx)
        dep_info
        new_state
        (account_balance chain (ctx_contract_address ctx))
        (new_acts ++ prev_out_queue)
        (build_call_info (ctx_from ctx) (ctx_amount ctx) msg :: prev_inc_calls)
        (build_tx (ctx_from ctx)
                  (ctx_contract_address ctx)
                  (ctx_amount ctx)
                  (tx_call (match head with
                            | act_call _ _ msg => Some msg
                            | _ => None
                            end)) :: prev_out_txs)) ->

  (* Queue permutation *)
  (forall height slot fin_height
          caddr dep_info cstate balance
          out_queue inc_calls out_txs
          out_queue'
          (IH : P height slot fin_height caddr dep_info cstate balance
                  out_queue inc_calls out_txs)
          (perm : Permutation out_queue out_queue')
          (tag : TagPermuteQueue),
      P height slot fin_height
        caddr dep_info cstate balance out_queue' inc_calls out_txs) ->

  forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists dep cstate inc_calls,
      deployment_info Setup trace caddr = Some dep /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      P (chain_height bstate)
        (current_slot bstate)
        (finalized_height bstate)
        caddr
        dep
        cstate
        (account_balance bstate caddr)
        (outgoing_acts bstate caddr)
        inc_calls
        (outgoing_txs trace caddr).
Proof.
  intros establish_facts
         add_block_case
         init_case
         transfer_case
         nonrecursive_call_case
         recursive_call_case
         permute_queue_case
         bstate caddr trace contract_deployed.
  assert (address_is_contract caddr = true) as is_contract
      by (eapply contract_addr_format; eauto).
  unfold contract_state in *.
  remember empty_state; induction trace as [|? ? ? ? IH];
    intros; subst; try solve [cbn in *; congruence].
  specialize (establish_facts mid to ltac:(auto) ltac:(auto) tag_facts).
  destruct_chain_step;
    [|clear add_block_case; destruct_action_eval; rewrite_environment_equiv; cbn in *|].
  - (* New block *)
    clear init_case recursive_call_case nonrecursive_call_case permute_queue_case.
    rewrite_environment_equiv.
    cbn in *.
    specialize_hypotheses.
    destruct IH as (depinfo' & cstate' & inc_calls' & -> & ? & -> & ?).
    exists depinfo', cstate', inc_calls'.
    rewrite_environment_equiv.
    repeat split; auto.
    inversion valid_header.
    cbn in *.
    destruct_address_eq; try congruence.
    rewrite outgoing_acts_after_block_nil by auto.
    unfold outgoing_acts in *; rewrite queue_prev in *; cbn in *.
    eapply add_block_case; try constructor.
    + apply establish_facts.
    + assumption.
  - (* Evaluation: transfer *)
    clear init_case recursive_call_case nonrecursive_call_case permute_queue_case.
    specialize_hypotheses.
    destruct IH as (depinfo' & cstate' & inc_calls' & -> & ? & -> & ?).
    exists depinfo', cstate', inc_calls'.
    rewrite_environment_equiv.
    repeat split; auto.
    rewrite (address_eq_sym from_addr) in *.
    cbn in *.
    (* Transfer cannot be to contract as that would be a
    call. Resolve this now. *)
    destruct (address_eqb_spec caddr to_addr) as [->|];
      cbn in *; try congruence.

    unfold outgoing_acts in *.
    rewrite queue_prev, queue_new in *.
    subst.
    cbn in *.
    rewrite (address_eq_sym from_addr) in *.
    destruct (address_eqb_spec caddr from_addr) as [<-|];
      cbn in *.
    + (* Transfer from contract *)
      remember (act_transfer _ _) as out_act.
      replace (-amount + account_balance mid caddr) with
          (account_balance mid caddr - act_body_amount out_act) by
          (subst; cbn; lia).
      subst.
      apply transfer_case; auto.
    + (* Irrelevant transfer *)
      auto.
  - (* Evaluation: Deploy *)
    clear recursive_call_case nonrecursive_call_case permute_queue_case.
    rewrite (address_eq_sym to_addr caddr) in *.
    destruct (address_eqb_spec caddr to_addr) as [->|]; cbn in *.
    + (* Deployment of this contract *)
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_init_strong ltac:(eassumption))
        as (setup_strong & result_strong & deser_setup_eq & <- & init).
      rewrite deser_setup_eq in *.
      cbn in *.
      exists (build_deployment_info from_addr amount setup_strong),
             result_strong,
             [].
      rewrite_environment_equiv; cbn.
      rewrite address_eq_refl.
      cbn.
      rewrite deserialize_serialize.
      assert (incoming_calls Msg trace to_addr = Some [])
        by (apply undeployed_contract_no_in_calls; auto).
      unfold incoming_calls in *; rewrite is_contract in *.
      repeat split; cbn in *; subst; auto.
      unfold outgoing_acts.
      rewrite queue_new.
      cbn.
      rewrite (address_eq_sym to_addr) in *.
      fold (outgoing_txs trace to_addr).
      pose proof (undeployed_contract_no_out_queue
                    to_addr mid ltac:(auto) ltac:(auto) ltac:(auto)) as queue_ne_to.
      rewrite queue_prev in queue_ne_to.
      inversion_clear queue_ne_to as [|? ? from_ne_to rest_ne_to].
      cbn in from_ne_to.
      rewrite (address_eq_ne from_addr to_addr) by (destruct_address_eq; auto).
      rewrite Forall_false_filter_nil by assumption.
      rewrite undeployed_contract_no_out_txs, undeployed_contract_balance_0 by auto.
      remember (build_ctx _ _ _) as ctx.
      replace from_addr with (ctx_from ctx) by (subst; auto).
      replace to_addr with (ctx_contract_address ctx) by (subst; auto).
      replace amount with (ctx_amount ctx) by (subst; auto).
      rewrite Z.add_0_r.
      pose proof
           (init_case (mid <| account_balance ::= add_balance to_addr amount |>
                           <| account_balance ::= add_balance from_addr (- amount) |>)).
      cbn in *.
      auto.
    + (* Deployment of other contract, might be by this contract. *)
      specialize_hypotheses.
      destruct IH as (depinfo & cstate & inc_calls & -> & ? & -> & ?).
      exists depinfo, cstate, inc_calls.
      rewrite_environment_equiv; cbn.
      rewrite address_eq_ne by auto.
      repeat split; auto.
      rewrite (address_eq_sym caddr).
      unfold outgoing_acts in *.
      rewrite queue_prev, queue_new in *.
      subst new_acts act.
      cbn in *.
      fold (outgoing_txs trace caddr).
      destruct_address_eq; subst; cbn in *; auto.
      (* This contract deploys other contract *)
      remember (act_deploy _ _ _) as abody.
      replace (-amount + account_balance mid caddr)
        with (account_balance mid caddr - act_body_amount abody)
        by (subst; cbn; lia).
      subst.
      apply transfer_case; auto.
  - (* Evaluation: Call *)
    clear init_case permute_queue_case.
    specialize_hypotheses.
    subst act new_acts.
    destruct IH as (depinfo & cstate & inc_calls & -> & ? & -> & IH).
    unfold outgoing_acts in *.
    rewrite queue_prev, queue_new in *.
    cbn in *.
    rewrite filter_app, filter_map, map_app, map_map; cbn in *.
    destruct (address_eqb_spec to_addr caddr) as [->|].
    + (* Call to contract *)
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_receive_strong ltac:(eassumption))
        as (prev_state_strong & msg_strong & resp_state_strong &
            deser_state & deser_msg & <- & receive).
      replace (env_contract_states mid caddr) with (Some prev_state) in * by auto.
      cbn in *.
      replace prev_state_strong with cstate in * by congruence; clear prev_state_strong.
      exists depinfo, resp_state_strong.
      exists (build_call_info from_addr amount msg_strong :: inc_calls).
      rewrite_environment_equiv.
      cbn.
      rewrite address_eq_refl.
      cbn.
      rewrite deserialize_serialize.
      repeat split; auto.
      {
        destruct msg_strong as [msg_strong|], msg as [msg|];
          try solve [cbn in *; congruence].
        now replace (deserialize msg) with (Some msg_strong) by auto.
      }

      rewrite (address_eq_sym caddr), filter_true, map_id.

      destruct (address_eqb_spec from_addr caddr) as [->|?]; cbn in *.
      * (* Recursive call *)
        remember (build_ctx _ _ _) as ctx.
        pose proof
            (recursive_call_case
               (transfer_balance caddr caddr amount mid)
               ctx depinfo cstate msg_strong
               (match msg with
                | Some msg => act_call caddr amount msg
                | None => act_transfer caddr amount
                end)) as case.
        subst ctx.
        cbn in case.
        rewrite address_eq_refl in case.
        replace (-amount + (amount + account_balance mid caddr))
          with (account_balance mid caddr)
          in * by lia.
        destruct msg_strong as [msg_strong|], msg as [msg|];
          cbn in *; try congruence; auto.
      * (* Someone else calls contract *)
        remember (build_ctx _ _ _) as ctx.
        pose proof
            (nonrecursive_call_case
               (transfer_balance from_addr caddr amount mid)
               ctx depinfo cstate msg_strong) as case.
        subst ctx.
        cbn in case.
        rewrite address_eq_ne in case by (subst; auto).
        rewrite address_eq_refl in case.
        replace (amount + account_balance mid caddr - amount)
          with (account_balance mid caddr) in case
          by lia.
        fold (outgoing_txs trace caddr).
        apply case; auto.
    + (* Call to other contract *)
      exists depinfo, cstate, inc_calls.
      rewrite_environment_equiv.
      rewrite filter_false.
      cbn.
      rewrite address_eq_ne by auto.
      rewrite (address_eq_sym caddr).
      destruct (address_eqb_spec from_addr caddr) as [->|?].
      * (* Call from us to other contract *)
        repeat split; auto.
        fold (outgoing_txs trace caddr).
        cbn in *.
        destruct msg as [msg|].
        1: remember (act_call _ _ _) as abody.
        2: remember (act_transfer _ _) as abody.
        1, 2: replace (-amount + account_balance mid caddr)
          with (account_balance mid caddr - act_body_amount abody)
          by (subst; cbn; lia).
        1, 2: subst; apply transfer_case; auto.
      * (* Irrelevant call. *)
        fold (outgoing_txs trace caddr).
        auto.
  - (* Permutation *)
    rewrite prev_next in *.
    specialize_hypotheses.
    destruct IH as (depinfo & cstate & inc_calls & ? & ? & ? & IH).
    exists depinfo, cstate, inc_calls.
    cbn.
    repeat split; auto.
    unfold outgoing_acts in *.
    fold (outgoing_txs trace caddr).
    apply permute_queue_case with
        (out_queue := map act_body
                          (filter (fun a => (act_from a =? caddr)%address)
                                  (chain_state_queue mid))); auto.
    now apply Permutation_map, Permutation_filter.
Qed.

End Theories.
End Trace.
End Semantics.

Inductive ActionEvaluationError :=
| amount_negative (* amount is negative *)
| amount_too_high (* sender does not have enough money *)
| no_such_contract (* there is not contract at that address *)
| too_many_contracts (* cannot generate fresh address for new contract *)
| init_failed (* contract init function failed *)
| receive_failed (* contract receive function failed *)
| internal_error. (* unexpected internal error *)

Inductive AddBlockError :=
| invalid_header (* header for next block is invalid *)
| invalid_root_action (act : Action) (* a specified root action is invalid *)
| action_evaluation_depth_exceeded (* out of fuel while evaluating actions recursively *)
| action_evaluation_error (* error when evaluating single action *)
    (act : Action)
    (err : ActionEvaluationError).

Class ChainBuilderType :=
  build_builder {
    builder_type : Type;

    builder_initial : builder_type;

    builder_env : builder_type -> Environment;

    builder_add_block
      (builder : builder_type)
      (header : BlockHeader)
      (actions : list Action) :
      result builder_type AddBlockError;

    builder_trace (builder : builder_type) :
      ChainTrace empty_state (build_chain_state (builder_env builder) []);
  }.

Global Coercion builder_type : ChainBuilderType >-> Sortclass.
Global Coercion builder_env : builder_type >-> Environment.
End Blockchain.

Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
        [header queue_prev valid_header acts_from_accs env_eq|
         act acts new_acts queue_prev eval queue_new|
         prev_next perm]
  end.

Ltac destruct_action_eval :=
  match goal with
  | [eval: ActionEvaluation _ _ _ _ |- _] => destruct eval
  end.

Ltac rewrite_environment_equiv :=
  match goal with
  | [eq: EnvironmentEquiv _ _ |- _] => rewrite eq in *
  end.

Local Ltac generalize_contract_statement_aux
      bstate caddr trace is_deployed Setup Msg State post :=
  let P := fresh "P" in
  evar (P : forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                   (caddr : Address) (deployment_info : DeploymentInfo Setup)
                   (cstate : State) (balance : Amount)
                   (outgoing_actions_queued : list ActionBody)
                   (incoming_calls_seen : list (ContractCallInfo Msg))
                   (outgoing_txs_seen : list Tx),
           Prop);
  let H := fresh "H" in
  enough (H: exists (dep : DeploymentInfo Setup)
                    (cstate : State)
                    (inc_calls : list (ContractCallInfo Msg)),
             deployment_info Setup trace caddr = Some dep /\
             contract_state bstate caddr = Some cstate /\
             incoming_calls Msg trace caddr = Some inc_calls /\
             P (chain_height bstate)
               (current_slot bstate)
               (finalized_height bstate)
               caddr dep cstate
               (account_balance bstate caddr)
               (outgoing_acts bstate caddr)
               inc_calls (outgoing_txs trace caddr));
  [let depinfo := fresh "depinfo" in
   let cstate := fresh "cstate" in
   let inc_calls := fresh "inc_calls" in
   let depinfo_strong := fresh "depinfo_strong" in
   let cstate_strong := fresh "cstate_strong" in
   let inc_calls_strong := fresh "inc_calls_strong" in
   let provenP := fresh "provenP" in
   destruct H as (depinfo & cstate & inc_calls &
                  depinfo_strong & cstate_strong & inc_calls_strong & provenP);
   repeat
     match goal with
     | [|- exists _ : DeploymentInfo Setup, _] => exists depinfo
     | [|- exists _ : State, _] => exists cstate
     | [|- exists _ : list (ContractCallInfo Msg), _] => exists inc_calls
     | [|- ?a /\ ?b] => refine (conj depinfo_strong _)
     | [|- ?a /\ ?b] => refine (conj cstate_strong _)
     | [|- ?a /\ ?b] => refine (conj inc_calls_strong _)
     end;
   pattern (chain_height bstate), (current_slot bstate), (finalized_height bstate),
           caddr, depinfo, cstate, (account_balance bstate caddr),
           (outgoing_acts bstate caddr), inc_calls, (outgoing_txs trace caddr);
   match goal with
   | [|- ?f _ _ _ _ _ _ _ _ _ _] => instantiate (P := f); exact provenP
   end
  | post bstate caddr trace is_deployed Setup Msg State P ].

Local Ltac generalize_contract_statement_with_post post :=
  intros;
  match goal with
  | [bstate : ChainState, caddr : Address |- _] =>
    try
      match goal with
      | [is_reachable : reachable bstate |- _] =>
        let trace := fresh "trace" in
        destruct is_reachable as [trace]
      end;
    match goal with
      [trace : ChainTrace empty_state bstate,
               is_deployed : env_contracts (_ bstate) caddr =
                             Some (contract_to_weak_contract ?c) |- _] =>
      match type of c with
      | Contract ?Setup ?Msg ?State =>
        generalize_contract_statement_aux bstate caddr trace
                                          is_deployed Setup Msg State post
      end
    end
  end.

Ltac generalize_contract_statement :=
  generalize_contract_statement_with_post
    ltac:(fun _ _ _ is_deployed _ _ _ _ => revert is_deployed).

Ltac contract_induction :=
  generalize_contract_statement_with_post
    ltac:(fun _ _ _ is_deployed Setup Msg State P =>
       revert is_deployed;
       let AddBlockFacts := fresh "AddBlockFacts" in
       let DeployFacts := fresh "DeployFacts" in
       let CallFacts := fresh "CallFacts" in
       evar (AddBlockFacts :
               forall (chain_height : nat) (current_slot : nat)
                      (finalized_height : nat) (new_height : nat)
                      (new_slot : nat) (new_finalized_height : nat), Prop);
       evar (DeployFacts : forall (chain : Chain)
                                  (ctx : ContractCallContext), Prop);
       evar (CallFacts : forall (chain : Chain) (ctx : ContractCallContext)
                                (cstate : State), Prop);
       apply (contract_induction _ AddBlockFacts DeployFacts CallFacts);
       cbv [P]; clear P; cycle 1).

Global Notation "'Please' 'prove' 'your' 'facts'" := TagFacts (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'addition' 'of' 'a' 'block'"
  := TagAddBlock (at level 100, only printing).
Global Notation "'Please' 'establish' 'the' 'invariant' 'after' 'deployment' 'of' 'the' 'contract'"
  := TagDeployment (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'an' 'outgoing' 'action'"
  := TagOutgoingAct (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'a' 'nonrecursive' 'call'"
  := TagNonrecursiveCall (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'a' 'recursive' 'call'"
  := TagRecursiveCall (at level 100, only printing).
Global Notation
       "'Please' 'reestablish' 'the' 'invariant' 'after' 'permutation' 'of' 'the' 'action' 'queue'"
  := TagPermuteQueue (at level 100, only printing).


Section LiftTransactionProp.

  Context {BaseTypes : ChainBase}
          {Setup : Type} `{Serializable Setup}
          {Msg : Type} `{Serializable Msg}
          {State : Type} `{Serializable State}.

(** If some property [P] holds for all actions in the output of the receive function, the property can be lifted to all outgoing actions for all reachabile states. *)
Lemma lift_outgoing_acts_prop {P : ActionBody -> Prop}
      (contract : Contract Setup Msg State) (bstate : ChainState) (addr : Address) :
  reachable bstate ->
  (forall chain ctx cstate msg new_cstate acts,
      contract.(receive) chain ctx cstate msg = Some (new_cstate, acts) ->
      Forall P acts) ->
  env_contracts bstate addr = Some (contract : WeakContract) ->
  Forall P (outgoing_acts bstate addr).
Proof.
  intros Hr Hc.
  contract_induction; intros; cbn in *; auto.
  - inversion_clear IH; auto.
  - apply Forall_app.
    split; auto.
    eauto.
  - apply Forall_app.
    inversion_clear IH.
    split; auto.
    eauto.
  - now rewrite <- perm.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => Logic.True).
    instantiate (DeployFacts := fun _ _ => Logic.True).
    instantiate (CallFacts := fun _ _ _ => Logic.True).
    unset_all; subst.
    destruct step; auto.
    destruct a; auto.
Qed.

(** If the receive function always returns an empty list of actions,
 the same holds for all reachable states *)
Lemma lift_outgoing_acts_nil (contract : Contract Setup Msg State)
      (bstate : ChainState) (addr : Address) :
  reachable bstate ->
  (forall chain ctx cstate msg new_cstate acts,
      contract.(receive) chain ctx cstate msg = Some (new_cstate, acts) ->
      acts = []) ->
  env_contracts bstate addr = Some (contract : WeakContract) ->
  outgoing_acts bstate addr = [].
Proof.
  intros.
  enough (all_false: Forall (fun _ => False) (outgoing_acts bstate addr)) by (now destruct all_false).
  apply (lift_outgoing_acts_prop contract); auto.
  intros.
  erewrite (H3 _ _ _ _ _ acts); [constructor|eassumption].
Qed.

End LiftTransactionProp.
