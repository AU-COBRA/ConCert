(** * Counter *)

From Coq Require Import Morphisms ZArith Notations.
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
  Definition receive (chain : Chain) (ctx : ContractCallContext)
             (state : State) (msg : option Msg) : option (State * list ActionBody)
    := match msg with
       | Some m => match counter state m with
                   | Some res => Some (res, [])
                   | None => None
                  end
       | None => None
       end.

  (** We initialize the contract state with [init_value] and set [owner] to the address from which the contract was deployed *)
  Definition init (chain : Chain) (ctx : ContractCallContext) (init_value : Z)
    : option State :=
    Some {| count := init_value ;
            owner := ctx.(ctx_from) |}.

  (** Deriving the [Serializable] instances for the state and for the messages *)
  Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<mkState>.

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<Inc, Dec>.

  Program Definition counter_contract : Contract Z Msg State :=
  build_contract init _ receive _.

End Counter.

(** ** Functional properties *)
Section FunctionalProperties.

  Import Lia.

  Context {BaseTypes : ChainBase}.

  (** ** Specification *)

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
