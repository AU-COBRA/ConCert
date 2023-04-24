(** * Counter *)

From Coq Require Import ZArith_base.
From Coq Require Import List.
From Coq Require Import Basics.
From Coq Require Import Lia.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.

Import ListNotations.

Open Scope Z.

(** ** Definition *)
Section Counter.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Context {BaseTypes : ChainBase}.

  (** The state is a current counter value and the owner's address *)
  Record State :=
    build_state { count : Z ;
                  owner : Address }.

  (** The contract accepts two kinds of messages: increment or decrement by some number *)
  Inductive Msg :=
  | Inc (i : Z)
  | Dec (i : Z).

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (** Since a contract is essentially a state transition function, we isolate
      the functionality corresponding to each kind of message into step functions *)
  Definition increment (n : Z) (st : State) : State :=
    {| count := st.(count) + n ;
       owner := st.(owner) |}.

  Definition decrement (n : Z) (st : State) : State :=
    {| count := st.(count) - n ;
       owner := st.(owner) |}.

  (** The main functionality of the contract.
      Dispatches on a message, validates the input and calls the step functions *)
  Definition counter (st : State)
                     (msg : Msg)
                     : result State Error :=
    match msg with
    | Inc i => if (0 <? i)
               then Ok (increment i st)
               else Err default_error
    | Dec i => if (0 <? i)
               then Ok (decrement i st)
               else Err default_error
    end.

  (** The "entrypoint" of the contract. Dispatches on a message and calls [counter]. *)
  Definition counter_receive (chain : Chain)
                             (ctx : ContractCallContext)
                             (state : State)
                             (msg : option Msg)
                             : result (State * list ActionBody) Error :=
    match msg with
    | Some m => match counter state m with
                | Ok res => Ok (res, [])
                | Err e => Err e
                end
    | None => Err default_error
    end.

  (** We initialize the contract state with [init_value] and set [owner] to the address from which the contract was deployed *)
  Definition counter_init (chain : Chain)
                          (ctx : ContractCallContext)
                          (init_value : Z)
                          : result State Error :=
    Ok {|
      count := init_value ;
      owner := ctx.(ctx_from)
    |}.

  Section Serialization.
    (** Deriving the [Serializable] instances for the state and for the messages *)
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<Inc, Dec>.
  End Serialization.

  (** The counter contract *)
  Definition counter_contract : Contract Z Msg State Error :=
    build_contract counter_init counter_receive.

End Counter.

(** ** Functional properties *)
Section FunctionalProperties.
  Context {BaseTypes : ChainBase}.

  (** *** Specification *)

  (** If the counter call succeeds and returns [next_state] then,
      depending on a message, it either increments or decrements
      by the number sent in the corresponding message *)
  Lemma counter_correct {prev_state next_state msg} :
    counter prev_state msg = Ok next_state ->
    match msg with
    | Inc n => prev_state.(count) < next_state.(count)
              /\ next_state.(count) = prev_state.(count) + n
    | Dec n => prev_state.(count) > next_state.(count)
              /\ next_state.(count) = prev_state.(count) - n
    end.
  Proof.
    intros H.
    all : destruct msg; cbn in *; unfold increment,decrement in *.
    all : destruct (0 <? i) eqn:Hz; inversion H; cbn in *.
    all : rewrite Z.ltb_lt in *; split; auto; lia.
  Qed.

End FunctionalProperties.

(** ** Safety properties *)

(** Safety properties are stated for all states reachable from the initial state. *)
Section SafetyProperties.
  Context {BaseTypes : ChainBase}.

  (** Converting a message to a number. Note that the decrements are negative. *)
  Definition opt_msg_to_number (msg : option Msg) :=
    match msg with
    | Some (Inc i) => i
    | Some (Dec i) => - i
    | _ => 0
    end.

  Open Scope program_scope.

  Lemma receive_produces_no_calls {chain ctx cstate msg new_cstate} acts :
    counter_receive chain ctx cstate msg = Ok (new_cstate, acts) ->
    acts = [].
  Proof.
    intros receive_some.
    destruct msg as [msg | ]; try discriminate; cbn in *.
    destruct (counter _ _) as [[? ?] | ] eqn:Hreceive; try inversion receive_some; subst; cbn in *; auto.
  Qed.

  (** The sum of all increment/decrement messages sent to the contract. *)
  Definition sum_inc_dec (l : list (ContractCallInfo Msg)) :=
    sumZ (opt_msg_to_number ∘ call_msg) l.

  (** We state the following safety property: for all reachable states (i.e. at any point in time after deployment), the state of the counter is equal to the initial value plus the sum of all successful increment and decrement messages sent to the contract.

  We use a special induction principle [contract_induction] that takes care of the boilerplate and exposes the cases in the convenient form. The [tag] variable in the context contains a hint what is expected to be done in each case. *)
  Lemma counter_safe block_state counter_addr
        (trace : ChainTrace empty_state block_state) :
    env_contracts block_state counter_addr = Some (counter_contract : WeakContract) ->
    exists cstate call_info deploy_info,
      incoming_calls Msg trace counter_addr = Some call_info
      /\ contract_state block_state counter_addr = Some cstate
      /\ deployment_info _ trace counter_addr = Some deploy_info
      /\ let init_val := deploy_info.(deployment_setup) in
        init_val + sum_inc_dec call_info = cstate.(count).
  Proof.
    contract_induction; intros; cbn in *; auto.
    + (* deployment *)
      inversion init_some; subst; clear init_some; cbn in *. lia.
    + (* contract call *)
      destruct msg as [msg|]; try discriminate; cbn in *.
      destruct (counter _ _) as [cstate|] eqn:counter_some; inversion receive_some; subst.
      (* NOTE: we use the functional correctness here *)
      specialize (counter_correct counter_some) as Cspec.
      destruct msg; auto; unfold sum_inc_dec in *; lia.
    + (* contract self-call *)
      (* NOTE: we know that the self-call is not possible because [counter_receive]
        always returns an empty list of actions. We instantiate the [CallFacts]
        predicate with the assumption that the from-address is not equal to the
        contract address. We will be asked to prove this goal later. *)
      instantiate (CallFacts := fun _ ctx _ _ _ => ctx_from ctx <> ctx_contract_address ctx);
        subst CallFacts; cbn in *; congruence.
    + (* we asked to prove additional assumptions we might have made.
      Since we instantiated only [CallFacts], we instantiate other assumptions
      with a trivial proposition *)
      instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      unset_all; subst; cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      cbn. intros cstate Hc Hstate.
      (* we use the fact that [counter_receive] doesn't return any actions *)
      assert ((outgoing_acts bstate_from to_addr) = []) as Hempty.
      { apply lift_outgoing_acts_nil with (contract := counter_contract); eauto.
        now constructor.
        intros. eapply (receive_produces_no_calls (chain := chain) (ctx := ctx)); eauto. apply H. }
      unfold outgoing_acts in *. rewrite queue_prev in *.
      subst act; cbn in Hempty.
      now destruct_address_eq.
  Qed.

End SafetyProperties.
