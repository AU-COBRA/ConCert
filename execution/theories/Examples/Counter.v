(** * Counter *)

From Coq Require Import Morphisms ZArith Basics Bool.
From Coq Require Import List.
From RecordUpdate Require Import RecordUpdate.

Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
Require Import Serializable.
Require Import Blockchain.

Import ListNotations.

Open Scope Z.

(** ** Definition *)
Section Counter.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Context {BaseTypes : ChainBase}.

  Record State :=
    mkState { count : Z ;
              owner : Address }.

  Inductive Msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition increment (st : State) (new_balance : Z) :=
    {| count := st.(count) + new_balance ;
       owner := st.(owner) |}.

  Definition decrement (st : State) (new_balance : Z) :=
      {| count := st.(count) - new_balance ;
         owner := st.(owner) |}.

  (** The main functionality of the contract *)
  Definition counter (st : State) (msg : Msg) : option State :=
    match msg with
    | Inc i => if (0 <? i) then Some (increment st i)
              else None
    | Dec i => if (0 <? i) then Some (decrement st i)
              else None
    end.

  (** The "entry point" of the contract. Dispatches on a message and calls [counter]. *)
  Definition counter_receive (chain : Chain) (ctx : ContractCallContext)
             (state : State) (msg : option Msg) : option (State * list ActionBody)
    := match msg with
       | Some m => match counter state m with
                   | Some res => Some (res, [])
                   | None => None
                  end
       | None => None
       end.

  (** We initialize the contract state with [init_value] and set [owner] to the address from which the contract was deployed *)
  Definition counter_init (chain : Chain) (ctx : ContractCallContext) (init_value : Z)
    : option State :=
    Some {| count := init_value ;
            owner := ctx.(ctx_from) |}.

  (** Deriving the [Serializable] instances for the state and for the messages *)
  Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<mkState>.

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<Inc, Dec>.

  (** The counter contract *)
  Program Definition counter_contract : Contract Z Msg State :=
  build_contract counter_init _ counter_receive _.

End Counter.

(** ** Functional properties *)
Section FunctionalProperties.

  Import Lia.

  Context {BaseTypes : ChainBase}.

  (** *** Specification *)

  Definition increments (f : State -> option State) (prev_state : State) (n : Z) :=
    exists next_state, f prev_state = Some next_state
                /\ next_state.(count) >= prev_state.(count)
                /\ next_state.(count) = (prev_state.(count) + n).

  Definition decrements (f : State -> option State) (prev_state : State) (n : Z) :=
    exists next_state, f prev_state = Some next_state
                /\ next_state.(count) <= prev_state.(count)
                /\ next_state.(count) = (prev_state.(count) - n).

  (** Counter increments, decrements or fails *)
  Definition counter_spec (f : State -> option State) (msg : Msg) :=
    forall state, (exists n, msg = Inc n /\ increments f state n)
           \/ (exists n, msg = Dec n /\ decrements f state n)
           \/ f state = None.

  (** *** Proofs of functional correctness properties *)
  Lemma increment_correct state m :
    0 < m ->
    increments (fun s => counter s (Inc m)) state m.
  Proof.
    intros Hm.
    eexists. repeat split.
    - simpl. rewrite <-Z.ltb_lt in *; now rewrite Hm.
    - simpl. subst. lia.
    - simpl. congruence.
  Qed.

  Lemma decrement_correct state  m :
    0 < m ->
    decrements (fun s => counter s (Dec m)) state m.
  Proof.
    intros Hm.
    eexists. repeat split.
    - simpl. rewrite <-Z.ltb_lt in *; now rewrite Hm.
    - simpl. subst. lia.
    - simpl. congruence.
  Qed.

  Lemma counter_correct (msg : Msg) : counter_spec (fun s => counter s msg) msg.
  Proof.
    intros state.
    destruct msg eqn:Hmsg.
    + destruct (0 <? z) eqn:Hz.
      * left. eexists. split;eauto.
        rewrite Z.ltb_lt in *.
        now apply increment_correct.
      * cbn. rewrite Hz;auto.
    + destruct (0 <? z) eqn:Hz.
      * right. left. eexists. split;eauto.
        rewrite Z.ltb_lt in *.
        now apply decrement_correct.
      * cbn. rewrite Hz;auto.
  Qed.

End FunctionalProperties.

(** ** Safety properties *)

(** Safety properties are stated for all states reachable from the initial state. *)
Section SafetyProperties.

Context {BaseTypes : ChainBase}.

(** Auxiliary definitions for stating the safety property *)
Definition counter_state (env : Environment) (address : Blockchain.Address) : option State :=
match (env_contract_states env address) with
| Some sv => deserialize sv
| None => None
end.

(** Converting a message to a number. Note that the decrements are negative. *)
Definition opt_msg_to_number (msg : option Msg) :=
  match msg with
  | Some m => match m with
             | Inc n => n
             | Dec n => - n
             end
  | _ => 0
  end.

Open Scope program_scope.

Import Lia.

Lemma receive_produces_no_calls {chain ctx cstate msg new_cstate} acts :
  counter_receive chain ctx cstate msg = Some (new_cstate, acts) ->
  acts = [].
Proof.
  intros receive_some.
  destruct msg as [msg | ];try discriminate; cbn in *.
  destruct (counter _ _) as [[? ?] | ] eqn:Hreceive;try inversion receive_some;subst; cbn in *;auto.
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
    /\ counter_state block_state counter_addr = Some cstate
    /\ deployment_info _ trace counter_addr = Some deploy_info
    /\ let init_val := deploy_info.(deployment_setup) in
      init_val + sum_inc_dec call_info = cstate.(count).
Proof.
  contract_induction; intros; cbn in *; auto.
  + (* deployment *)
    inversion init_some;subst;clear init_some;cbn in *. lia.
  + (* contract call *)
    unfold receive in *.
    destruct msg as [msg|];try discriminate.
    (* NOTE: we use the functional correctness here *)
    specialize (counter_correct msg prev_state) as Cspec.
    destruct Cspec as [Hinc|[Hdec|Hfail]].
    * (* increments *)
      destruct Hinc as (n & Hmsg & Hinc).
      unfold increments in Hinc.
      destruct Hinc as (next_cstate & Hnstate & ? & Hadds).
      unfold counter_receive in *.
      rewrite Hnstate in receive_some.
      inversion receive_some;subst;clear receive_some.
      cbn in *. destruct (0 <? n);inversion Hnstate;subst.
      rewrite Hadds. rewrite <-IH;auto. unfold sum_inc_dec. lia.
    *  (* decrements *)
      destruct Hdec as (n & Hmsg & Hdec).
      unfold decrements in Hdec.
      destruct Hdec as (next_cstate & Hnstate & ? & Hsubstracts).
      unfold counter_receive in *.
      rewrite Hnstate in receive_some.
      inversion receive_some;subst;clear receive_some.
      cbn in *. destruct (0 <? n);inversion Hnstate;subst.
      rewrite Hsubstracts. rewrite <-IH;auto. unfold sum_inc_dec. lia.
    * (* fails *)
      unfold counter_receive in *.
      now rewrite Hfail in receive_some.
  + (* contract self-call *)
    (* NOTE: we know that the self-call is not possible because [counter_receive]
       always returns an empty list of actions. We instantiate the [CallFacts]
       predicate with the assumption that the from-address is not equal to the
       contract address. We will be asked to prove this goal later. *)
    instantiate (CallFacts := fun _ ctx _ => ctx_from ctx <> ctx_contract_address ctx);
      subst CallFacts; cbn in *; congruence.
  + (* we asked to prove additional assumtions we might have made.
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
    { apply lift_outgoing_txs_empty with (contract := counter_contract);eauto.
      intros. eapply (receive_produces_no_calls (chain:=chain) (ctx:=ctx));eauto. apply H. }
    unfold outgoing_acts in *.
    rewrite queue_prev in *.
    subst act; cbn in Hempty.
    destruct_address_eq; cbn in *; auto.
Qed.

End SafetyProperties.
