From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
Import ListNotations.

Section ContractMonads.
Context `{ChainBase}.

Definition ContractReader (T : Type) : Type :=
  Chain -> ContractCallContext -> (Chain * ContractCallContext * T).

Definition run_contract_reader
            {T : Type}
            (chain : Chain)
            (ctx : ContractCallContext)
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

Definition ContractIniter (Setup Error T : Type) : Type :=
  Chain -> ContractCallContext -> Setup ->
  (Chain * ContractCallContext * Setup * result T Error).

Definition run_contract_initer
            {Setup Error T: Type}
            (m : ContractIniter Setup Error T)
            (chain : Chain)
            (ctx : ContractCallContext)
            (setup : Setup)
            : result T Error :=
  let '(_, _, _, res) := m chain ctx setup in res.

Global Arguments run_contract_initer {_ _ _} _ /.

Global Instance contract_initer_monad
        {Setup Error : Type}
        : Monad (ContractIniter Setup Error) :=
  {| ret _ x chain ctx setup := (chain, ctx, setup, Ok x);
     bind _ _ prev f chain ctx setup :=
       let '(chain, ctx, setup, res) := prev chain ctx setup in
       match res with
       | Ok res => f res chain ctx setup
       | Err e => (chain, ctx, setup, Err e)
       end; |}.

Global Instance contract_initer_laws
        {Setup Error : Type}
        : MonadLaws (@contract_initer_monad Setup Error).
Proof.
  constructor.
  - reflexivity.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct t as [[[[? ?] ?] ?] []]; auto.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct t as [[[[? ?] ?] ?] []]; auto.
Qed.

Global Instance contract_reader_to_contract_initer
        {Setup Error : Type}
        : MonadTrans (ContractIniter Setup Error) ContractReader :=
  {| lift _ (reader : ContractReader _) chain ctx setup :=
       let '(chain, ctx, res) := reader chain ctx in
       (chain, ctx, setup, Ok res) |}.

Global Instance result_to_contract_initer
        {Setup Error : Type}
        : MonadTrans (ContractIniter Setup Error) (fun T => result T Error) :=
  {| lift _ (opt : result _ Error) chain ctx setup := (chain, ctx, setup, opt) |}.

Definition ContractReceiver (State Msg Error T : Type) : Type :=
  Chain -> ContractCallContext -> State -> option Msg -> list ActionBody ->
  (Chain * ContractCallContext * State * option Msg * list ActionBody * result T Error).

Global Instance contract_receiver_monad
      (State Msg Error : Type)
      : Monad (ContractReceiver State Msg Error) :=
  {| ret _ x chain ctx state msg acts := (chain, ctx, state, msg, acts, Ok x);
     bind _ _ prev f chain ctx state msg acts :=
       let '(chain, ctx, state, msg, acts, res) := prev chain ctx state msg acts in
       match res with
       | Ok res => f res chain ctx state msg acts
       | Err e => (chain, ctx, state, msg, acts, Err e)
       end |}.

Definition run_contract_receiver
            {State Msg Error T : Type}
            (m : ContractReceiver State Msg Error T)
            (chain : Chain)
            (ctx : ContractCallContext)
            (state : State)
            (msg : option Msg)
            : result (T * list ActionBody) Error :=
  let '(_, _, _, _, acts, result) := m chain ctx state msg [] in
  match result with
  | Ok res => Ok (res, acts)
  | Err e => Err e
  end.

Global Arguments run_contract_receiver {_ _ _ _} _ /.

Global Instance contract_receiver_laws
        (State Msg Error : Type)
        : MonadLaws (contract_receiver_monad State Msg Error).
Proof.
  constructor.
  - reflexivity.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct t as [[[[[? ?] ?] ?] ?] []]; auto.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct t as [[[[[? ?] ?] ?] ?] []]; auto.
Qed.

Global Instance contract_reader_to_receiver
        {State Msg Error : Type}
        : MonadTrans (ContractReceiver State Msg Error) ContractReader :=
  {| lift _ (reader : ContractReader _) chain ctx state msg acts :=
       let '(chain, ctx, res) := reader chain ctx in
       (chain, ctx, state, msg, acts, Ok res) |}.

Global Instance result_to_contract_receiver
        {State Msg Error : Type}
        : MonadTrans (ContractReceiver State Msg Error) (fun T => result T Error) :=
  {| lift _ (opt : result _ Error) chain ctx state msg acts := (chain, ctx, state, msg, acts, opt) |}.

Definition chain_height : ContractReader nat :=
  fun chain ctx => (chain, ctx, chain_height chain).

Definition current_slot : ContractReader nat :=
  fun chain ctx => (chain, ctx, current_slot chain).

Definition finalized_height : ContractReader nat :=
  fun chain ctx => (chain, ctx, finalized_height chain).

Definition caller_addr : ContractReader Address :=
  fun chain ctx => (chain, ctx, ctx_from ctx).

Definition my_addr : ContractReader Address :=
  fun chain ctx => (chain, ctx, ctx_contract_address ctx).

Definition my_balance : ContractReader Amount :=
  fun chain ctx => (chain, ctx, ctx_contract_balance ctx).

Definition call_amount : ContractReader Amount :=
  fun chain ctx => (chain, ctx, ctx_amount ctx).

Definition deployment_setup {Setup Error : Type}
  : ContractIniter Setup Error Setup :=
  fun chain ctx setup => (chain, ctx, setup, Ok setup).

Definition reject_deployment {Setup State Error : Type} (err : Error)
  : ContractIniter Setup Error State :=
  fun chain ctx setup => (chain, ctx, setup, Err err).

Definition accept_deployment
            {Setup Error State : Type}
            (state : State)
            : ContractIniter Setup Error State :=
  ret state.

Definition call_msg
            {State Msg Error: Type}
            (err : Error)
            : ContractReceiver State Msg Error Msg :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts, result_of_option msg err).

Definition my_state
           {State Msg Error : Type}
           : ContractReceiver State Msg Error State :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts, Ok state).

Definition queue
           {State Msg Error : Type}
           (act : ActionBody)
           : ContractReceiver State Msg Error unit :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts ++ [act], Ok tt).

Definition reject_call
           {State Msg Error : Type}
           (err : Error)
           : ContractReceiver State Msg Error State :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, [], Err err).

Definition accept_call
           {State Msg Error : Type}
           (new_state : State)
           : ContractReceiver State Msg Error State :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts, Ok new_state).

Definition build_contract
           {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
           (init : ContractIniter Setup Error State)
           (receive : ContractReceiver State Msg Error State)
           : Contract Setup Msg State Error :=
  {| init := (run_contract_initer init);
     receive := (run_contract_receiver receive); |}.

End ContractMonads.
