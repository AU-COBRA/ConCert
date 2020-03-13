From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
From Coq Require Import Morphisms.
Require Import Blockchain.
Require Import Monads.
Require Import Serializable.
Import ListNotations.

Section ContractMonads.
Context `{ChainBase}.

Definition ContractReader (T : Type) : Type :=
  Chain -> ContractCallContext -> (Chain * ContractCallContext * T).

Definition run_contract_reader
           {T : Type}
           (chain : Chain) (ctx : ContractCallContext)
           (m : ContractReader T) : T :=
  let '(_, _, result) := m chain ctx in result.

Global Instance contract_reader_monad : Monad ContractReader :=
  {| ret _ x chain ctx := (chain, ctx, x);
     bind _ _ prev f chain ctx :=
       let '(chain, ctx, res) := prev chain ctx in
       f res chain ctx; |}.

Global Instance contract_reader_laws : MonadLaws contract_reader_monad.
Proof.
  constructor.
  - reflexivity.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _) as [[? ?] ?]; auto.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _) as [[? ?] ?]; auto.
Qed.

Definition ContractIniter (Setup T : Type) : Type :=
  Chain -> ContractCallContext -> Setup ->
  (Chain * ContractCallContext * Setup * option T).

Definition run_contract_initer
           {Setup T : Type}
           (m : ContractIniter Setup T)
           (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : option T :=
  let '(_, _, _, result) := m chain ctx setup in result.

Global Arguments run_contract_initer {_ _} _ /.

Global Instance contract_initer_monad (Setup : Type) : Monad (ContractIniter Setup) :=
  {| ret _ x chain ctx setup := (chain, ctx, setup, Some x);
     bind _ _ prev f chain ctx setup :=
       let '(chain, ctx, setup, res) := prev chain ctx setup in
       match res with
       | Some res => f res chain ctx setup
       | None => (chain, ctx, setup, None)
       end; |}.

Global Instance contract_initer_laws
       (Setup : Type) : MonadLaws (contract_initer_monad Setup).
Proof.
  constructor.
  - reflexivity.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _ _) as [[[[? ?] ?] ?] []]; auto.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _ _) as [[[[? ?] ?] ?] []]; auto.
Qed.

Global Instance contract_reader_to_contract_initer
       {Setup : Type} : MonadTrans (ContractIniter Setup) ContractReader :=
  {| lift _ (reader : ContractReader _) chain ctx setup :=
       let '(chain, ctx, res) := reader chain ctx in
       (chain, ctx, setup, Some res) |}.

Global Instance option_to_contract_initer
       {Setup : Type} : MonadTrans (ContractIniter Setup) option :=
  {| lift _ (opt : option _) chain ctx setup := (chain, ctx, setup, opt) |}.

Definition ContractReceiver (State Msg T : Type) : Type :=
  Chain -> ContractCallContext -> State -> option Msg -> list ActionBody ->
  (Chain * ContractCallContext * State * option Msg * list ActionBody * option T).

Global Instance contract_receiver_monad (State Msg : Type) : Monad (ContractReceiver State Msg) :=
  {| ret _ x chain ctx state msg acts := (chain, ctx, state, msg, acts, Some x);
     bind _ _ prev f chain ctx state msg acts :=
       let '(chain, ctx, state, msg, acts, res) := prev chain ctx state msg acts in
       match res with
       | Some res => f res chain ctx state msg acts
       | None => (chain, ctx, state, msg, acts, None)
       end |}.

Definition run_contract_receiver
           {State Msg T : Type}
           (m : ContractReceiver State Msg T)
           (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg)
           : option (T * list ActionBody) :=
  let '(_, _, _, _, acts, result) := m chain ctx state msg [] in
  option_map (fun result => (result, acts)) result.

Global Arguments run_contract_receiver {_ _ _} _ /.

Global Instance contract_receiver_laws
       (State Msg : Type) : MonadLaws (contract_receiver_monad State State).
Proof.
  constructor.
  - reflexivity.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _ _ _ _) as [[[[[? ?] ?] ?] ?] []]; auto.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _ _ _ _) as [[[[[? ?] ?] ?] ?] []]; auto.
Qed.

Global Instance contract_reader_to_receiver
       {State Msg : Type} : MonadTrans (ContractReceiver State Msg) ContractReader :=
  {| lift _ (reader : ContractReader _) chain ctx state msg acts :=
       let '(chain, ctx, res) := reader chain ctx in
       (chain, ctx, state, msg, acts, Some res) |}.

Global Instance option_to_contract_receiver
       {State Msg : Type} : MonadTrans (ContractReceiver State Msg) option :=
  {| lift _ (opt : option _) chain ctx state msg acts := (chain, ctx, state, msg, acts, opt) |}.

Definition chain_height : ContractReader nat :=
  fun chain ctx => (chain, ctx, chain_height chain).

Definition current_slot : ContractReader nat :=
  fun chain ctx => (chain, ctx, current_slot chain).

Definition finalized_height : ContractReader nat :=
  fun chain ctx => (chain, ctx, finalized_height chain).

Definition account_balance (addr : Address) : ContractReader Amount :=
  fun chain ctx => (chain, ctx, account_balance chain addr).

Definition caller_addr : ContractReader Address :=
  fun chain ctx => (chain, ctx, ctx_from ctx).

Definition my_addr : ContractReader Address :=
  fun chain ctx => (chain, ctx, ctx_contract_address ctx).

Definition call_amount : ContractReader Amount :=
  fun chain ctx => (chain, ctx, ctx_amount ctx).

Definition deployment_setup {Setup : Type}
  : ContractIniter Setup Setup :=
  fun chain ctx setup => (chain, ctx, setup, Some setup).

Definition reject_deployment {Setup State : Type}
  : ContractIniter Setup State :=
  fun chain ctx setup => (chain, ctx, setup, None).

Definition accept_deployment
           {Setup State : Type} (state : State) : ContractIniter Setup State :=
  ret state.

Definition call_msg
           {State Msg : Type} : ContractReceiver State Msg (option Msg) :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts, Some msg).

Definition my_state
           {State Msg : Type} : ContractReceiver State Msg State :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts, Some state).

Definition queue
           {State Msg : Type} (act : ActionBody) : ContractReceiver State Msg unit :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts ++ [act], Some tt).

Definition reject_call
           {State Msg : Type} : ContractReceiver State Msg State :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, [], None).

Definition accept_call
           {State Msg : Type} (new_state : State) : ContractReceiver State Msg State :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts, Some new_state).

Definition build_contract
           {Setup Msg State : Type}
           `{Serializable Setup} `{Serializable Msg} `{Serializable State}
           (init : ContractIniter Setup State)
           (receive : ContractReceiver State Msg State)
           (init_proper :
              Proper (ChainEquiv ==> eq ==> eq ==> eq) (run_contract_initer init))
           (receive_proper :
              Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) (run_contract_receiver receive))
  : Contract Setup Msg State :=
  {| init := (run_contract_initer init);
     receive := (run_contract_receiver receive);
     init_proper := init_proper;
     receive_proper := receive_proper; |}.

End ContractMonads.
