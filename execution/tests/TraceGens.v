(*
  The ChainTrace datatype is defined as a ChainedList of ChainStates and ChainSteps.
  This file defines a generator combinator, gChain, for the ChainBuilder type.
  From this, a generator/arbitrary instance for the ChainTrace type is derived automatically.

  This file also contains checker combinator  over ChainBuilders/ChainTraces, 
  like forAllChainTrace, reachableFrom_chaintrace, and pre_post_assertion.
*)

Global Set Warnings "-extraction-logical-axiom".

From QuickChick Require Import QuickChick. Import QcNotation.
From ConCert Require Import Blockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import ResultMonad.
From ConCert Require Import ChainedList.

From ConCert.Execution.QCTests Require Import TestUtils ChainPrinters .

From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

From Coq Require Import ZArith.
From Coq Require Import List.

Import BoundedN.Stdpp.
Import ListNotations.

Section TraceGens.
  Context  {ChainBuilder : ChainBuilderType}.
  Context `{Show ChainBuilder}.
  Context `{Show ChainState}.

  (* Adds a block with 50 money as reward. This will be used for all testing. *)
  Definition add_block (chain : ChainBuilder) acts : result ChainBuilder AddBlockError :=
    let header :=
        {| block_height := S (chain_height chain);
          block_slot := S (current_slot chain);
          block_finalized_height := finalized_height chain;
          block_creator := creator;
          block_reward := 50; |} in
    builder_add_block chain header acts.

  Definition gAdd_block (cb : ChainBuilder)
                          (gActOptFromChainSized : Environment -> nat -> GOpt Action)
                          (act_depth : nat)
                          (max_acts_per_block : nat)
                          : G (result ChainBuilder AddBlockError) :=
    acts <- optToVector max_acts_per_block (gActOptFromChainSized cb act_depth) ;;
    if (length acts) =? 0
    then returnGen (Err action_evaluation_depth_exceeded)
    else returnGen (add_block cb acts).

  Definition gChain (init_lc : ChainBuilder)
                    (gActOptFromChainSized : Environment -> nat -> GOpt Action)
                    (max_length : nat)
                    (act_depth : nat)
                    (max_acts_per_block : nat)
                    : G ChainBuilder := 
    let gAdd_block' lc := gAdd_block lc gActOptFromChainSized act_depth max_acts_per_block in
    let default_error := action_evaluation_depth_exceeded in (* Not ideal approach, but it suffices for now *)
    let try_twice g := backtrack_result default_error [(1, g);(1, g)] in
    let fix rec n (lc : ChainBuilder) : G ChainBuilder :=
      match n with
      | 0 => returnGen lc
      | S n => lc' <- try_twice (gAdd_block' lc) ;; (* heuristic: try twice for more expected robustness *)
              match lc' with
              | Ok lc' => rec n lc'
              (* if no new chain could be generated without error, return the old chain *)
              | err => returnGen lc 
              end
      end in 
    rec max_length init_lc.


  Definition get_reachable {to} : ChainTrace empty_state to -> reachable to := fun t => inhabits t.

  Definition gReachableFromTrace {to} (gtrace : G (ChainTrace empty_state to)) : G (reachable to) :=
    bindGen gtrace (fun trace =>
    returnGen (get_reachable trace)).

  Global Instance shrinkReachable : Shrink {to : ChainState | reachable to} :=
  {|
    shrink a := [a]
  |}.
    
  Global Instance genReachableSized `{GenSized ChainBuilder} : GenSized {to | reachable to}.
  Proof.
    constructor.
    intros H2. 
    apply H1 in H2.
    apply (bindGen H2).
    intros cb.
    remember (builder_trace cb) as trace.
    apply returnGen.
    eapply exist.
    apply get_reachable.
    apply trace.
  Defined.

  Global Instance shrinkChainTraceSig : Shrink {to : ChainState & ChainTrace empty_state to} := 
  {|
    shrink a := [a]
  |}.

  Global Instance genChainTraceSigSized `{GenSized ChainBuilder} : GenSized {to : ChainState & ChainTrace empty_state to}.
  Proof.
    constructor. 
    intros n.
    apply H1 in n.
    apply (bindGen n).
    intros cb.
    remember (builder_trace cb) as trace.
    apply returnGen.
    eapply existT.
    eauto.
  Defined.

  (* Checker combinators on ChainBuilder *)
  Definition forAllChainBuilder {prop : Type}
                              `{Checkable prop}
                              (maxLength : nat)
                              (init_lc : ChainBuilder)
                              (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                              (pf : ChainBuilder -> prop)
                              : Checker :=
    forAll (gTrace init_lc maxLength)
    (fun cb => checker (pf cb)).

  (* Gathers all ChainStates from a ChainTrace in a list, appearing in order. *)
  (* Currently not tail-call optimized. Can be improved if needed. *)
  Fixpoint trace_states {from to} (trace : ChainTrace from to) : list ChainState :=
    match trace with
    | snoc trace' step => trace_states trace' ++ [snd (chainstep_states step)]
    | clnil => []
    end.

  (* Variant that only gathers ChainStates of step_block steps in the trace. *)
  Fixpoint trace_states_step_block {from to} (trace : ChainTrace from to) : list ChainState :=
    match trace with
    | snoc trace' (Blockchain.step_block _ _ _ _ _ _ _ as step) => 
      trace_states_step_block trace' ++ [snd (chainstep_states step)]
    | snoc trace' _ => trace_states_step_block trace'
    | clnil => []
    end.

  (* Asserts that a ChainState property holds for all ChainStates in a ChainTrace  *)
  Definition ChainTrace_ChainTraceProp {prop : Type}
                                       {from to}
                                      `{Checkable prop}
                                       (trace : ChainTrace from to)
                                       (pf : ChainState -> prop)
                                       : Checker :=
    let printOnFail (cs : ChainState) : Checker := whenFail (show cs) (checker (pf cs)) in
    let trace_list := trace_states_step_block trace in
    discard_empty trace_list (conjoin_map printOnFail).

  (* -------------------- Checker combinators on traces --------------------  *)

  Definition forAllChainState {prop : Type}
                             `{Checkable prop}
                              (maxLength : nat)
                              (init_lc : ChainBuilder)
                              (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                              (pf : ChainState -> prop)
                              : Checker :=
    forAll (gTrace init_lc maxLength)
    (fun cb => ChainTrace_ChainTraceProp cb.(builder_trace) pf).

  (* Checker combinators on ChainTrace, asserting holds a property on 
    each pair of succeeding ChainStates in the trace. *)
  Definition forAllChainStatePairs {prop : Type}
                                  `{Checkable prop}
                                   (maxLength : nat)
                                   (init_lc : ChainBuilder)
                                   (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                                   (pf : ChainState -> ChainState -> prop)
                                   : Checker :=
    (* helper function folding over the trace*)
    let last_cstate {from to} (trace : ChainTrace from to) := to in
    let fix all_statepairs {from to : ChainState} (trace : ChainTrace from to) prev_bstate : Checker :=
      match trace with
      | snoc trace' step =>
        match step with
        | Blockchain.step_block _ _ _ _ _ _ _ =>
          (* next_bstate has acts, bstate_before_step_block has no acts *)
          let '(bstate_before_step_block, next_bstate) := chainstep_states step in
          conjoin [(checker (pf next_bstate prev_bstate)); all_statepairs trace' bstate_before_step_block] 
        | _ => all_statepairs trace' prev_bstate
          end
      | clnil  => checker true
      end in
    forAll (gTrace init_lc maxLength)
    (fun cb => all_statepairs cb.(builder_trace) (last_cstate cb.(builder_trace))).

  (* Asserts that a boolean predicate holds for at least one ChainState in the given ChainTrace *)
  Definition existsb_chaintrace {from to}
                                (pf : ChainState -> bool)  
                                (trace : ChainTrace from to) : bool :=
    existsb pf (trace_states trace).

  (* Asserts that a ChainState satisfying a given predicate is reachable from the given trace generator. *)
  Definition reachableFromSized_chaintrace
                          (maxLength : nat)
                          (init_lc : ChainBuilder)
                          (gTrace : ChainBuilder -> nat -> G ChainBuilder )
                          (pf : ChainState -> bool)
                          : Checker :=
    existsP (gTrace init_lc maxLength) (fun cb => 
      existsb_chaintrace pf cb.(builder_trace)).

  Definition reachableFrom_chaintrace init_lc gTrace pf : Checker :=
    sized (fun n => reachableFromSized_chaintrace n init_lc gTrace pf).

  (* This property states that if there is a reachable chainstate satisfying the reachable_prop predicate,
     then all succeeding chainstates must satisfy implied_prop *)
  Definition reachableFrom_implies_chaintracePropSized
                        {A prop : Type}
                       `{Checkable prop}
                        (maxLength : nat)
                        (init_cb : ChainBuilder)
                        (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                        (reachable_prop : ChainState -> option A)
                        (implied_prop : A -> list ChainState -> list ChainState -> prop)
                        : Checker :=
  forAll (gTrace init_cb maxLength)
  (fun cb =>
    let trace := cb.(builder_trace) in
    let reachable_prop_bool := isSome o reachable_prop in
    let tracelist := trace_states_step_block trace in
    match split_at_first_satisfying reachable_prop_bool tracelist with
    | Some ((x::xs) as pre, post) =>
      (* last_step is the element satisfying reachable_prop_bool *)
      let last_step := (List.last pre x) in
      isSomeCheck (reachable_prop last_step)
        (fun a => 
          (* assert that implied_prop holds on the post trace *)
          implied_prop a pre post
        )
    | _ => false ==> true
    end).

  (* if pre tests true, then post tests true, for all tested execution traces *)
  Definition pre_post_assertion {Setup Msg State prop : Type}
                               `{Checkable prop}
                               `{Serializable Msg}
                               `{Serializable State}
                               `{Serializable Setup}
                                (maxLength : nat)
                                (init_chain : ChainBuilder)
                                (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                                (c : Contract Setup Msg State)
                                (caddr : Address)
                                (pre : State -> Msg -> bool)
                                (post : ContractCallContext -> State -> Msg -> option (State * list ActionBody) -> prop) : Checker :=
      let messages_of_acts acts  := fold_right (fun act acc =>
          match act.(act_body) with
          | act_call _ _ ser_msg =>
            match @deserialize Msg _ ser_msg with
            | Some msg => (act, msg) :: acc
            | None => acc
            end
          | _ => acc
          end
        ) [] acts in
      let post_helper '(cctx, post_state) cstate msg := post cctx cstate msg post_state in
      let stepProp (cs : ChainState) :=
        let env : Environment := cs.(chain_state_env) in
        let msgs := messages_of_acts cs.(chain_state_queue) in
        let execute_receive env caddr cstate act msg :=
          let amount :=
            match act.(act_body) with
            | act_call _ amount _ => amount
            | _ => 0%Z
            end in
          let cctx := build_ctx act.(act_from) caddr amount in
          let new_state := c.(receive) env cctx cstate (Some msg) in
          (cctx, new_state) in
        match get_contract_state State env caddr with
        (* test that executing receive on the messages that satisfy the precondition, also satisfy the postcondition *)
        | Some cstate => (conjoin_map (fun '(act, msg) =>
                          if pre cstate msg
                          then checker (post_helper (execute_receive env caddr cstate act msg) cstate msg)
                          else checker true (* TODO: should be discarded!*)
                          ) msgs)
        | None => checker true
        end in
      (* combine it all with the forAllTraces checker combinator *)
      forAllChainState maxLength init_chain gTrace stepProp.

End TraceGens.
