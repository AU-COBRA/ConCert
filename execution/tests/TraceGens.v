(*
  The ChainTrace datatype is defined as a ChainedList of ChainStates and ChainSteps.
  The ChainStep is an inductive relation with constructors 'step_block', 'step_action', and 'step_permute'.
  Each constructor is guarded with a number of propositions, requiring various validity conditions.

  This makes it hard to construct a generator for the ChainTrace type, so instead we initially construct a simpler model
  for chain traces, which is essentially just a list of chain states.
  But since we are working in the context of black-box testing, this may even be a better approach than trying to implement
  generators for the ChainTrace type, since we don't want to ensure/require that certain conditions hold, we only want
  to generate data from the given functions, and see what result we get.
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

  Definition add_block (chain : ChainBuilder) acts : result ChainBuilder AddBlockError :=
    let header :=
        {| block_height := S (chain_height chain);
          block_slot := S (current_slot chain);
          block_finalized_height := finalized_height chain;
          block_creator := creator;
          block_reward := 50; |} in
    builder_add_block chain header acts.

  Definition next_header (chain : ChainBuilder) :=
      {| block_height := S (chain_height chain);
        block_slot := S (current_slot chain);
        block_finalized_height := finalized_height chain;
        block_creator := creator;
        block_reward := 50; |}.

  (* Helper function for backtrack_result. It picks and removes an element from a list of result generators. *)
  Fixpoint pickDrop {T E}
                    (default : E)
                    (xs : list (nat * G (result T E))) 
                    (n : nat) 
                    : nat * G (result T E) * list (nat * G (result T E)) :=
    match xs with
      | nil => (0, returnGen (Err default), nil)
      | (k, x) :: xs =>
        if (n <? k) then  (k, x, xs)
        else let '(k', x', xs') := pickDrop default xs (n - k)
            in (k', x', (k,x)::xs')
    end. 

  (* Backtracking generator for results instead of Option. Works the same way as backtrack. *)
  Fixpoint backtrack_result_fix {T E} (default : E) (fuel : nat) (gs : list (nat * G (result T E))) : G (result T E) :=
    match fuel with
    | 0 => returnGen (Err default)
    | S fuel' => idx <- choose (0, fuel') ;;
          let '(k, g, gs') := pickDrop default gs idx in
          ma <- g ;;
          match ma with
          | Err e => backtrack_result_fix default fuel' gs'
          | Ok r => returnGen (Ok r)
          end
    end.

  Definition backtrack_result {T E} (default : E) (gs : list (nat * G (result T E))) : G (result T E) :=
    backtrack_result_fix default (length gs) gs.

  Definition gAdd_block (cb : ChainBuilder)
                          (gActOptFromChainSized : Environment -> nat -> G (option Action))
                          (act_depth : nat)
                          (max_acts_per_block : nat)
                          : G (result ChainBuilder AddBlockError) :=
    acts <- optToVector max_acts_per_block (gActOptFromChainSized cb act_depth) ;;
    if (length acts) =? 0
    then returnGen (Err action_evaluation_depth_exceeded)
    else returnGen (add_block cb acts).

  Definition gChain (init_lc : ChainBuilder)
                    (gActOptFromChainSized : Environment -> nat -> G (option Action))
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
