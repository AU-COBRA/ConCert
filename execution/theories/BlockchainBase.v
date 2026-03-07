(** This file defines blockchains, both a contract's view (which is
more computational) and the semantics of executing smart contracts
in a blockchain.

The most important types are:

- The [ChainBase] type describes basic assumptions made of any blockchain.
  In most cases, we will abstract over this type.

- The [Chain] type describes a smart contract's view of the blockchain.
  This is the data that can be accessed by smart contracts.

- The [Action] type describes how smart contracts (and external users)
  interact with the blockchain. We allow transfers, calls and deployment
  of contracts.

- The [WeakContract] type describes a "weak" or "stringly" typed
  version of smart contracts. Contracts are just two functions init and
  receive to respectively initialize the state on deployment and update
  the state when receiving messages. The weak version of contracts means that
  the state/message/setup types, which would normally vary with contracts,
  are stored in a serialized format.

- The [Contract] type describes a more strongly typed version of a contract.
  This is the same as the above except we abstract over the appropriate types.
  Users of the framework will mostly need to deal with this.

The next types deal with semantics.

- The [Environment] type augments the Chain type with more information.
  [Environment] can be thought of as the information that a realistic blockchain
  implementation would need to keep track of to implement operations. For instance,
  it is reasonable to assume that an implementation needs to access the state of
  contracts, but not to assume that it needs to store the full transaction history
  of all addresses.

- The [ActionEvaluation] type. This specifies how to evaluate actions returned by
  contracts or input in blocks. This related an environment and action to a new
  environment and a list of new actions to execute.

- The [ChainState] type. This augments the [Environment] type with a queue of
  "outstanding" actions that need to be executed. For instance, when a block is
  added, its actions are put into this queue.

- The [ChainStep] type. This specifies how the blockchain should execute smart
  contracts, and how new blocks are added. It relates a [ChainState] to a new [ChainState].
  There are steps to allow adding blocks, evaluating actions in the queue and permuting
  the queue (allowing to model any execution order).

- The [ChainTrace] type. This just represents a sequence of steps. If a trace ends
  in a state it means that the state is [reachable] and there is a "semantically correct"
  way of executing to get to this state. This type records the full history of a
  blockchain's execution, and it would thus be unrealistic to extract.

- The [ChainBuilderType] type. This is a typeclass for implementations of blockchains,
  where these implementations need to prove that they satisfy our semantics.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Psatz.
From Stdlib Require Import Permutation.
From Stdlib Require Import Morphisms.
From Stdlib Require Import String.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.



Definition Amount := Z.
Bind Scope Z_scope with Amount.

Class ChainBase :=
  build_chain_base {
    Address : Type;
    address_eqb : Address -> Address -> bool;
    address_eqb_spec :
      forall (a b : Address), Bool.reflect (a = b) (address_eqb a b);
    address_eqdec :: stdpp.base.EqDecision Address;
    address_countable :: countable.Countable Address;
    address_serializable :: Serializable Address;
    address_is_contract : Address -> bool;
  }.

Global Opaque Address address_eqb address_eqb_spec
              address_eqdec address_countable
              address_serializable.


Declare Scope address_scope.
Delimit Scope address_scope with address.
Bind Scope address_scope with Address.
Infix "=?" := address_eqb (at level 70) : address_scope.

Section Address.
  Context {Base : ChainBase}.

  Definition address_neqb (x y : Address) : bool :=
    negb (address_eqb x y).

  Definition address_not_contract (x : Address) : bool :=
    negb (address_is_contract x).

  Lemma address_eq_refl x :
    address_eqb x x = true.
  Proof.
    destruct (address_eqb_spec x x); auto; congruence.
  Qed.

  Lemma address_eq_ne x y :
    x <> y ->
    address_eqb x y = false.
  Proof.
    destruct (address_eqb_spec x y) as [->|]; tauto.
  Qed.

  Lemma address_eq_ne' x y :
    x <> y <->
    address_eqb x y = false.
  Proof.
    split; destruct (address_eqb_spec x y) as [->|]; (discriminate || tauto).
  Qed.

  Lemma address_eq_sym x y :
    address_eqb x y = address_eqb y x.
  Proof.
    destruct (address_eqb_spec x y) as [->|].
    - now rewrite address_eq_refl.
    - rewrite address_eq_ne; auto.
  Qed.

  Lemma address_neqb_eq x y :
    address_neqb x y = false <->
    x = y.
  Proof.
    unfold address_neqb.
    rewrite Bool.negb_false_iff.
    now destruct (address_eqb_spec x y).
  Qed.

  Lemma address_neq_sym x y :
    address_neqb x y = address_neqb y x.
  Proof.
    unfold address_neqb.
    f_equal.
    apply address_eq_sym.
  Qed.

End Address.



Global Ltac destruct_address_eq :=
  repeat
    match goal with
    | [H: context[address_eqb ?a ?b] |- _] =>
      try rewrite (address_eq_sym b a) in *; destruct (address_eqb_spec a b)
    | [|- context[address_eqb ?a ?b]] =>
      try rewrite (address_eq_sym b a) in *; destruct (address_eqb_spec a b)
    | [H: context[address_neqb ?a ?b] |- _] =>
      try unfold address_neqb in *; destruct (address_eqb_spec a b)
    | [|- context[address_neqb ?a ?b]] =>
      try unfold address_neqb in *; destruct (address_eqb_spec a b)
    end.



Section Blockchain.
  Context {Base : ChainBase}.

  (** This represents the view of the blockchain that a contract
  can access and interact with. *)
  Record Chain :=
    build_chain {
      chain_height     : nat;
      current_slot     : nat;
      finalized_height : nat;
    }.

  Record ContractCallContext :=
    build_ctx {
      (** Address that initiated the transaction (never a contract) *)
      ctx_origin : Address;
      (** Address of the immediate account that sent
          the call (can be a contract or a user account) *)
      ctx_from : Address;
      (** Address of the contract being called *)
      ctx_contract_address : Address;
      (** Balance of the contract being called *)
      ctx_contract_balance : Amount;
      (** Amount of currency passed in call *)
      ctx_amount : Amount;
    }.

  Record ValidChain (chain : Chain) := {
    chain_height_valid     : (chain.(chain_height) <= chain.(current_slot))%nat;
    finalized_height_valid : (chain.(finalized_height) < S chain.(chain_height))%nat;
  }.

  Record ValidContext (ctx : ContractCallContext) := {
    ctx_origin_valid           : address_is_contract ctx.(ctx_origin) = false;
    ctx_contract_address_valid : address_is_contract ctx.(ctx_contract_address) = true;
    ctx_contract_balance_valid : (0 <= ctx.(ctx_contract_balance))%Z;
    ctx_amount_valid           : (0 <= ctx.(ctx_amount))%Z;
  }.

  (** Operations that a contract can return or that a user can use
  to interact with a chain. *)
  Inductive ActionBody :=
  | act_transfer (to : Address) (amount : Amount)
  | act_call (to : Address) (amount : Amount) (msg : SerializedValue)
  | act_deploy (amount : Amount) (c : WeakContract) (setup : SerializedValue)
  with
    WeakContract :=
    | build_weak_contract
        (init :
            Chain ->
            ContractCallContext ->
            SerializedValue (* setup *) ->
            result SerializedValue SerializedValue)
        (receive :
            Chain ->
            ContractCallContext ->
            SerializedValue (* state *) ->
            option SerializedValue (* message *) ->
            result (SerializedValue * list ActionBody) SerializedValue).

  Definition act_body_amount (ab : ActionBody) : Z :=
    match ab with
    | act_transfer _ amount
    | act_call _ amount _
    | act_deploy amount _ _ => amount
    end.

  Definition wc_init (wc : WeakContract) :=
    let (i, _) := wc in i.

  Definition wc_receive (wc : WeakContract) :=
    let (_, r) := wc in r.

  Record Action :=
    build_act {
      act_origin : Address;
      act_from   : Address;
      act_body   : ActionBody;
    }.

  Definition act_amount (a : Action) :=
    act_body_amount (act_body a).

  (** Represents a strongly-typed contract. This is what users will primarily
  use and interact with when they want deployment. We keep the weak contract
  only "internally" for blockchains, while any strongly-typed contract can
  be converted to and from *)
  Record Contract
         (Setup Msg State Error : Type)
        `{Serializable Setup}
        `{Serializable Msg}
        `{Serializable State}
        `{Serializable Error} :=
    build_contract {

      init :
        Chain ->
        ContractCallContext ->
        Setup ->
        result State Error;

      receive :
        Chain ->
        ContractCallContext ->
        State ->
        option Msg ->
        result (State * list ActionBody) Error;
    }.

  Global Arguments init {_ _ _ _ _ _ _ _}.
  Global Arguments receive {_ _ _ _ _ _ _ _}.
  Global Arguments build_contract {_ _ _ _ _ _ _ _}.

  Definition deser_error :=
    serialize "Deserialization failed"%string.

  Definition error_to_weak_error {T E : Type}
                                `{Serializable E}
                                 (r : result T E)
                                 : result T SerializedValue :=
    bind_error (fun err => serialize err) r.

  Definition contract_to_weak_contract
             {Setup Msg State Error : Type}
            `{Serializable Setup}
            `{Serializable Msg}
            `{Serializable State}
            `{Serializable Error}
             (c : Contract Setup Msg State Error)
             : WeakContract :=
        let weak_init chain ctx ser_setup :=
            do setup <- result_of_option (deserialize ser_setup) deser_error;
            do state <- error_to_weak_error (c.(init) chain ctx setup);
            Ok (serialize state) in
        let weak_recv chain ctx ser_state ser_msg_opt :=
            do state <- result_of_option (deserialize ser_state) deser_error;
            match ser_msg_opt with
            | Some ser_msg =>
              do msg <- result_of_option (deserialize ser_msg) deser_error;
              do '(new_state, acts) <- error_to_weak_error (c.(receive) chain ctx state (Some msg));
              Ok (serialize new_state, acts)
            | None =>
              do '(new_state, acts) <- error_to_weak_error (c.(receive) chain ctx state None);
              Ok (serialize new_state, acts)
            end in
        build_weak_contract weak_init weak_recv.

  Coercion contract_to_weak_contract : Contract >-> WeakContract.

  (** Deploy a strongly typed contract with some amount and setup *)
  Definition create_deployment
             {Setup Msg State Error : Type}
            `{Serializable Setup}
            `{Serializable Msg}
            `{Serializable State}
            `{Serializable Error}
             (amount : Amount)
             (contract : Contract Setup Msg State Error)
             (setup : Setup) : ActionBody :=
    act_deploy amount contract (serialize setup).

  (** The contract interface is the main mechanism allowing a deployed
  contract to interact with another deployed contract. This hides
  the ugly details of everything being SerializedValue away from contracts. *)
  Record ContractInterface {Msg : Type} :=
    build_contract_interface {
      (** The address of the contract being interfaced with *)
      contract_address : Address;
      (** Make an action sending money and optionally a message to the contract *)
      send : Amount -> option Msg -> ActionBody;
    }.

  Global Arguments ContractInterface _ : clear implicits.

  Definition get_contract_interface
             (chain : Chain)
             (addr : Address)
             (Msg : Type)
            `{Serializable Msg}
             : option (ContractInterface Msg) :=
    let ifc_send amount msg :=
        match msg with
        | None => act_transfer addr amount
        | Some msg => act_call addr amount (serialize msg)
        end in
    Some {| contract_address := addr; send := ifc_send; |}.

  Section Semantics.
    MetaRocq Run (make_setters Chain).

    Definition add_balance
               (addr : Address)
               (amount : Amount)
               (map : Address -> Amount)
               : Address -> Amount :=
      fun a => if (a =? addr)%address
               then (amount + map a)%Z
               else map a.

    Global Arguments add_balance _ _ _ /.

    Definition set_chain_contract_state
               (addr : Address)
               (state : SerializedValue)
               (map : Address -> option SerializedValue)
               : Address -> option SerializedValue :=
      fun a => if (a =? addr)%address
               then Some state
               else map a.

    Record Environment :=
      build_env {
        env_chain :> Chain;
        env_account_balances : Address -> Amount;
        env_contracts : Address -> option WeakContract;
        env_contract_states : Address -> option SerializedValue;
      }.

    (** Two environments are equivalent if they are extensionally equal *)
    Record EnvironmentEquiv (e1 e2 : Environment) : Prop :=
      build_env_equiv {
        chain_eq : env_chain e1 = env_chain e2;
        account_balances_eq :
          forall a, env_account_balances e1 a = env_account_balances e2 a;
        contracts_eq :
          forall a, env_contracts e1 a = env_contracts e2 a;
        contract_states_eq :
          forall addr, env_contract_states e1 addr = env_contract_states e2 addr;
      }.

    (** Strongly typed version of the contract state *)
    Definition contract_state
               {A : Type}
              `{Serializable A}
               (env : Environment)
               (addr : Address)
               : option A :=
      env_contract_states env addr >>= deserialize.

    Global Program Instance environment_equiv_equivalence :
      Equivalence EnvironmentEquiv.
    Next Obligation.
      apply build_env_equiv; reflexivity.
    Qed.
    Next Obligation.
      destruct H; apply build_env_equiv; now symmetry.
    Qed.
    Next Obligation.
      destruct H, H0; apply build_env_equiv; try congruence.
    Qed.

    Global Instance environment_equiv_env_account_balances_proper :
      Proper (EnvironmentEquiv ==> eq ==> eq) env_account_balances.
    Proof.
      repeat intro; subst; apply account_balances_eq; assumption.
    Qed.

    Global Instance environment_equiv_env_contracts_proper :
      Proper (EnvironmentEquiv ==> eq ==> eq) env_contracts.
    Proof.
      repeat intro; subst; apply contracts_eq; assumption.
    Qed.

    Global Instance environment_equiv_env_contract_states_proper :
      Proper (EnvironmentEquiv ==> eq ==> eq) env_contract_states.
    Proof.
      repeat intro; subst; apply contract_states_eq; assumption.
    Qed.

    Global Instance environment_equiv_env_chain_equiv_proper :
      Proper (EnvironmentEquiv ==> eq) env_chain.
    Proof.
      repeat intro; apply chain_eq; assumption.
    Qed.

    Global Instance environment_equiv_contract_state_proper
      {A : Type} `{Serializable A} :
      Proper (EnvironmentEquiv ==> eq ==> (@eq (option A))) contract_state.
    Proof.
      intros ? ? env_eq ? ? ?.
      subst.
      unfold contract_state.
      now rewrite env_eq.
    Qed.

    MetaRocq Run (make_setters Environment).

    Definition transfer_balance (from to : Address)
                                (amount : Amount)
                                (env : Environment) :=
      env<|env_account_balances ::= add_balance to amount|>
         <|env_account_balances ::= add_balance from (-amount)|>.

    Definition add_contract (addr : Address)
                            (contract : WeakContract)
                            (env : Environment)
                            : Environment :=
      env<|env_contracts ::=
        fun f a =>
          if (a =? addr)%address
          then Some contract
          else f a|>.

    Definition set_contract_state (addr : Address)
                                  (state : SerializedValue)
                                  (env : Environment) :=
      env<|env_contract_states ::= set_chain_contract_state addr state|>.

    (* set_chain_contract_state updates a map (function) by returning a
      new map (function). If this function is immediately applied to a
      key, then unfold it. *)
    Global Arguments set_chain_contract_state _ _ _ /.

    Ltac rewrite_environment_equiv :=
      match goal with
      | [H: EnvironmentEquiv _ _ |- _] => try rewrite H in *
      end.

    Ltac solve_proper :=
      apply build_env_equiv;
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
    Inductive ActionEvaluation (prev_env : Environment)
                               (act : Action)
                               (new_env : Environment)
                               (new_acts : list Action)
                               : Type :=
      | eval_transfer :
          forall (origin from_addr to_addr : Address)
                 (amount : Amount),
            amount >= 0 ->
            amount <= env_account_balances prev_env from_addr ->
            address_is_contract to_addr = false ->
            act = build_act origin from_addr (act_transfer to_addr amount) ->
            EnvironmentEquiv
              new_env
              (transfer_balance from_addr to_addr amount prev_env) ->
            new_acts = [] ->
            ActionEvaluation prev_env act new_env new_acts
      | eval_deploy :
          forall (origin from_addr to_addr : Address)
                 (amount : Amount)
                 (wc : WeakContract)
                 (setup : SerializedValue)
                 (state : SerializedValue),
          amount >= 0 ->
          amount <= env_account_balances prev_env from_addr ->
          address_is_contract to_addr = true ->
          env_contracts prev_env to_addr = None ->
          act = build_act origin from_addr (act_deploy amount wc setup) ->
          wc_init
            wc
            (transfer_balance from_addr to_addr amount prev_env)
            (build_ctx origin from_addr to_addr amount amount)
            setup = Ok state ->
          EnvironmentEquiv
            new_env
            (set_contract_state
              to_addr state (add_contract
                          to_addr wc (transfer_balance from_addr to_addr amount prev_env))) ->
          new_acts = [] ->
          ActionEvaluation prev_env act new_env new_acts
      | eval_call :
          forall (origin from_addr to_addr : Address)
                 (amount : Amount)
                 (wc : WeakContract)
                 (msg : option SerializedValue)
                 (prev_state : SerializedValue)
                 (new_state : SerializedValue)
                 (resp_acts : list ActionBody),
          amount >= 0 ->
          amount <= env_account_balances prev_env from_addr ->
          env_contracts prev_env to_addr = Some wc ->
          env_contract_states prev_env to_addr = Some prev_state ->
          act = build_act origin from_addr
                          (match msg with
                          | None => act_transfer to_addr amount
                          | Some msg => act_call to_addr amount msg
                          end) ->
          wc_receive
            wc
            (transfer_balance from_addr to_addr amount prev_env)
            (build_ctx origin from_addr to_addr (env_account_balances new_env to_addr) amount)
            prev_state
            msg = Ok (new_state, resp_acts) ->
          new_acts = map (build_act origin to_addr) resp_acts ->
          EnvironmentEquiv
            new_env
            (set_contract_state to_addr new_state (transfer_balance from_addr to_addr amount prev_env)) ->
          ActionEvaluation prev_env act new_env new_acts.

    Global Arguments eval_transfer {_ _ _ _ }.
    Global Arguments eval_deploy {_ _ _ _ }.
    Global Arguments eval_call {_ _ _ _}.

    Section Accessors.
      Context {origin : Address}
              {pre : Environment}
              {post : Environment}
              {act : Action}
              {new_acts : list Action}
              (eval : ActionEvaluation pre act post new_acts).

      Definition eval_origin : Address :=
        match eval with
        | eval_transfer origin _ _ _ _ _ _ _ _ _
        | eval_deploy origin _ _ _ _ _ _ _ _ _ _ _ _ _ _
        | eval_call origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => origin
        end.

      Definition eval_from : Address :=
        match eval with
        | eval_transfer _ from _ _ _ _ _ _ _ _
        | eval_deploy _ from _ _ _ _ _ _ _ _ _ _ _ _ _
        | eval_call _ from _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => from
        end.

      Definition eval_to : Address :=
        match eval with
        | eval_transfer _ _ to _ _ _ _ _ _ _
        | eval_deploy _ _ to _ _ _ _ _ _ _ _ _ _ _ _
        | eval_call _ _ to _ _ _ _ _ _ _ _ _ _ _ _ _ _ => to
        end.

      Definition eval_amount : Amount :=
        match eval with
        | eval_transfer _ _ _ amount _ _ _ _ _ _
        | eval_deploy _ _ _ amount _ _ _ _ _ _ _ _ _ _ _
        | eval_call _ _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ => amount
        end.

    End Accessors.



    Section Trace.

    Record BlockHeader :=
      build_block_Header {
        block_height           : nat;
        block_slot             : nat;
        block_finalized_height : nat;
        block_reward           : Amount;
        block_creator          : Address;
      }.

    Definition add_new_block_to_env (header : BlockHeader)
                                    (env : Environment)
                                    : Environment :=
      env<|env_chain; chain_height := block_height header|>
         <|env_chain; current_slot := block_slot header|>
         <|env_chain; finalized_height := block_finalized_height header|>
         <|env_account_balances ::=
            add_balance (block_creator header) (block_reward header)|>.

    (* Todo: this should just be a computation. But I still do not *)
    (* know exactly what the best way of working with reflect is *)
    Local Open Scope nat.
    Definition act_is_from_account (act : Action) : Prop :=
      address_is_contract (act_from act) = false.

    Definition act_origin_is_account (act : Action) : Prop :=
      address_is_contract (act_origin act) = false.

    Definition act_origin_is_eq_from (act : Action) : Prop :=
      address_eqb (act_origin act) (act_from act) = true.


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
        chain_state_env   :> Environment;
        chain_state_queue : list Action;
      }.

    MetaRocq Run (make_setters ChainState).

    Inductive ChainStep (prev_bstate next_bstate : ChainState) :=
    | step_block :
        forall (header : BlockHeader),
          chain_state_queue prev_bstate = [] ->
          IsValidNextBlock header prev_bstate ->
          Forall act_is_from_account (chain_state_queue next_bstate) ->
          Forall act_origin_is_eq_from (chain_state_queue next_bstate) ->
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
    | step_action_invalid :
        forall (act : Action)
              (acts : list Action),
          EnvironmentEquiv next_bstate prev_bstate ->
          chain_state_queue prev_bstate = act :: acts ->
          chain_state_queue next_bstate = acts ->
          act_is_from_account act ->
          (forall bstate new_acts,
            ActionEvaluation prev_bstate act bstate new_acts -> False) ->
          ChainStep prev_bstate next_bstate
    | step_permute :
          EnvironmentEquiv next_bstate prev_bstate ->
          Permutation (chain_state_queue prev_bstate) (chain_state_queue next_bstate) ->
          ChainStep prev_bstate next_bstate.

    Lemma origin_is_account acts :
      Forall act_is_from_account acts ->
      Forall act_origin_is_eq_from acts ->
      Forall act_origin_is_account acts.
    Proof.
      intros Hall.
      induction Hall as [| a Ha]; intros Hall0; auto.
      inversion Hall0; subst.
      constructor; auto.
      specialize (address_eqb_spec (act_origin a) (act_from a)) as Haddr;
        unfold act_origin_is_eq_from in *; destruct Haddr; easy.
    Qed.



    (* Reachability *)

    Definition empty_state : ChainState :=
      {| chain_state_env :=
          {| env_chain :=
                {| chain_height := 0;
                  current_slot := 0;
                  finalized_height := 0; |};
              env_account_balances a := 0%Z;
              env_contract_states a := None;
              env_contracts a := None; |};
        chain_state_queue := [] |}.

    (* The ChainTrace captures that there is a valid execution where,
    starting from one environment and queue of actions, we end up in a
    different environment and queue of actions. *)
    Definition ChainTrace :=
      ChainedList ChainState ChainStep.

    (* Additionally, a state is reachable if there is a trace ending in this trace. *)
    Definition reachable (to : ChainState) : Prop :=
      inhabited (ChainTrace empty_state to).

    (* A state `to` is reachable through `mid` if `mid` is reachable and there exists a trace
        from `mid` to `to`. This captures that there is a valid execution ending up in `to`
        and going through the state `mid` at some point *)
    Definition reachable_through mid to :=
      reachable mid /\ inhabited (ChainTrace mid to).



    Definition outgoing_acts (state : ChainState)
                             (addr : Address)
                             : list ActionBody :=
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
          tx_origin : Address;
          tx_from   : Address;
          tx_to     : Address;
          tx_amount : Amount;
          tx_body   : TxBody;
      }.

    Definition eval_tx {pre : Environment} {act : Action}
                       {post : Environment} {new_acts : list Action}
                       (step : ActionEvaluation pre act post new_acts) : Tx :=
      match step with
      | eval_transfer origin from to amount _ _ _ _ _ _ =>
        build_tx origin from to amount tx_empty
      | eval_deploy origin from to amount wc setup _ _ _ _ _ _ _ _ _ =>
        build_tx origin from to amount (tx_deploy wc setup)
      | eval_call origin from to amount _ msg _ _ _ _ _ _ _ _ _ _ _ =>
        build_tx origin from to amount (tx_call msg)
      end.

    Fixpoint trace_txs {from to : ChainState}
                       (trace : ChainTrace from to)
                       : list Tx :=
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
               (addr : Address)
               : list Tx :=
      filter (fun tx => (tx_to tx =? addr)%address) (trace_txs trace).

    Definition outgoing_txs
               {from to : ChainState}
               (trace : ChainTrace from to)
               (addr : Address)
               : list Tx :=
      filter (fun tx => (tx_from tx =? addr)%address)
             (trace_txs trace).

    Record ContractCallInfo (Msg : Type) :=
      build_call_info {
        call_origin : Address;
        call_from   : Address;
        call_amount : Amount;
        call_msg    : option Msg;
      }.

    Global Arguments build_call_info {_}.
    Global Arguments call_origin {_}.
    Global Arguments call_from {_}.
    Global Arguments call_amount {_}.
    Global Arguments call_msg {_}.

    Fixpoint incoming_calls
             (Msg : Type) `{Serializable Msg}
             {from to : ChainState}
             (trace : ChainTrace from to)
             (caddr : Address)
             : option (list (ContractCallInfo Msg)) :=
      match trace with
      | snoc trace' step =>
        match step with
        | step_action _ _ _ _ _ _ (eval_call origin from to amount _ msg _ _ _ _ _ _ _ _ _ _ _) _ =>
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
            Some (build_call_info origin from amount hd_msg :: tl)
          else
            incoming_calls Msg trace' caddr
        | _ => incoming_calls Msg trace' caddr
        end
      | _ => Some []
      end.

    Record DeploymentInfo (Setup : Type) :=
      build_deployment_info {
        deployment_origin : Address;
        deployment_from   : Address;
        deployment_amount : Amount;
        deployment_setup  : Setup;
      }.

    Global Arguments build_deployment_info {_}.
    Global Arguments deployment_origin {_}.
    Global Arguments deployment_from {_}.
    Global Arguments deployment_amount {_}.
    Global Arguments deployment_setup {_}.

    Fixpoint deployment_info
             (Setup : Type)
            `{Serializable Setup}
             {from to : ChainState}
             (trace : ChainTrace from to)
             (caddr : Address)
             : option (DeploymentInfo Setup) :=
      match trace with
      | snoc trace' step =>
        match step with
        | step_action _ _ _ _ _ _ (eval_deploy origin from to amount _ setup _ _ _ _ _ _ _ _ _) _ =>
          if (to =? caddr)%address then
            do setup <- deserialize setup;
            Some (build_deployment_info origin from amount setup)
          else
            deployment_info Setup trace' caddr
        | _ => deployment_info Setup trace' caddr
        end
      | clnil => None
      end.

    Fixpoint trace_blocks {from to : ChainState}
                          (trace : ChainTrace from to)
                          : list BlockHeader :=
      match trace with
      | snoc trace' step =>
        match step with
        | step_block _ _ header _ _ _ _ _ =>
          header :: trace_blocks trace'
        | _ => trace_blocks trace'
        end
      | clnil => []
      end.

    Definition created_blocks
               {from to : ChainState}
               (trace : ChainTrace from to)
               (creator : Address)
               : list BlockHeader :=
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

    End Trace.
  End Semantics.
End Blockchain.



Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
        [?header ?queue_prev ?valid_header ?acts_from_accs ?origin_correct ?env_eq|
         ?act ?acts ?new_acts ?queue_prev ?eval ?queue_new|
         ?act ?acts ?env_eq ?queue_prev ?queue_new ?act_from_acc ?no_eval|
         ?env_eq ?perm]
  end.

Ltac destruct_action_eval :=
  match goal with
  | [eval: ActionEvaluation _ _ _ _ |- _] =>
    destruct eval as
      [?origin ?from_addr ?to_addr ?amount ?amount_nonnegative ?enough_balance
       ?to_addr_not_contract ?act_eq ?env_eq ?new_acts_eq |
       ?origin ?from_addr ?to_addr ?amount ?wc ?setup ?state ?amount_nonnegative
        ?enough_balance ?to_addr_contract ?not_deployed
        ?act_eq ?init_some ?env_eq ?new_acts_eq |
       ?origin ?from_addr ?to_addr ?amount ?wc ?msg ?prev_state ?new_state ?resp_acts
        ?amount_nonnegative ?enough_balance ?deployed ?deployed_state ?act_eq
        ?receive_some ?new_acts_eq ?env_eq ]
  end.

Ltac rewrite_environment_equiv :=
  match goal with
  | [eq: EnvironmentEquiv _ _ |- _] => rewrite eq
  end.

Tactic Notation "rewrite_environment_equiv" "in" hyp(H) :=
  match goal with
  | [eq: EnvironmentEquiv _ _ |- _] => rewrite eq in H
  end.

Tactic Notation "rewrite_environment_equiv" "in" "*" :=
  match goal with
  | [eq: EnvironmentEquiv _ _ |- _] => rewrite eq in *
  end.
