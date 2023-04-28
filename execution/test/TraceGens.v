(*
  The ChainTrace datatype is defined as a ChainedList of ChainStates
  and ChainSteps. This file defines a generator combinator, gChain,
  for the ChainBuilder type. From this, a generator/arbitrary instance
  for the ChainTrace type is derived automatically.

  This file also contains checker combinator over ChainBuilders/ChainTraces,
  like forAllChainTrace, reachableFrom_chaintrace, and pre_post_assertion.
*)

Global Set Warnings "-extraction-logical-axiom".

From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution.Test Require Import TestUtils.
From QuickChick Require Import QuickChick.

Import MonadNotation. Open Scope monad_scope.

From Coq Require Import ZArith.
From Coq Require Import List.

Import QcNotation.
Import BoundedN.Stdpp.
Import ListNotations.

Section TraceGens.

  Context `{Show ChainBuilder}.
  Context `{Show ChainState}.
  Global Definition BlockReward : Amount := 50.
  Global Definition BlockCreator : Address := creator.
  Global Definition MaxGenAttempts : nat := 2.

  (* Deconstructs a ChainTrace to a list of blockheaders list of the minimum
     information needed to reconstruct a ChainTrace, that being a list of
     block headers and chain_state_queues from each step_block *)
  Fixpoint trace_blocks {from to} (trace : ChainTrace from to)
                        : list (BlockHeader * list Action) :=
    match trace with
    | snoc trace' (Blockchain.step_block _ _ header _ _ _ _ _ as step) =>
      trace_blocks trace' ++ [(header, chain_state_queue (snd (chainstep_states step)))]
    | snoc trace' _ => trace_blocks trace'
    | clnil => []
    end.

  (* Reconstructs list of block information (blockheaders and queues)
     to a ChainBuilder. It trims any empty blocks that can be removed
     without invalidating execution of the remaining actions.
     Also removes any actions that cannot be executed *)
  Fixpoint build_chain_builder (init_cb : ChainBuilder) blocks
                               : result ChainBuilder AddBlockError :=
    (* Instead of using the original header we need override height and
       finalized_height since the blockchain requires that the height always
       grows by one and if we trim and keep the height in the original header
       then the height would increase by two *)
    let new_header header :=
      {| block_height := S (chain_height init_cb);
        block_slot := header.(block_slot);
        block_finalized_height := finalized_height init_cb;
        block_creator := header.(block_creator);
        block_reward := header.(block_reward); |} in
    (* Remove any actions that are no longer valid due to earlier actions
        that could have been removed by the shrinker *)
    let try_remove_invalid_acts header acts blocks :=
      let valid_acts := fold_left (fun acts act =>
        match builder_add_block init_cb (new_header header) (acts ++ [act]) with
        | Ok cb => acts ++ [act]
        | Err error => acts
        end ) acts [] in
      (* TODO: also try to trim block here if valid_acts is empty *)
      match builder_add_block init_cb (new_header header) valid_acts with
      | Ok cb => build_chain_builder cb blocks
      | Err error => Err error
      end in
    let build_block header acts blocks :=
      match builder_add_block init_cb (new_header header) acts with
      | Ok cb => build_chain_builder cb blocks
      | Err error => try_remove_invalid_acts header acts blocks
      end in
    (* Attempt to trim block *)
    let try_trim header blocks :=
      let trimmed_result := build_chain_builder init_cb blocks in
        match trimmed_result with
        | Ok cb => Ok cb
        | Err error => build_block header [] blocks
        end in
    match blocks with
    | [] => Ok init_cb
    | (header, []) :: xs => try_trim header xs
    | (header, acts) :: xs => build_block header acts xs
    end.

  (* Reconstructs a list of ChainBuilders *)
  Fixpoint rebuild_chains (shrunk_chains : list (list (BlockHeader * list Action)))
                          init_cb : list ChainBuilder :=
    match shrunk_chains with
    | [] => []
    | block :: blocks =>
      match build_chain_builder init_cb block with
      | Ok cb => cb :: rebuild_chains blocks init_cb
      | Err error => rebuild_chains blocks init_cb
      end
    end.

  (* Alternative version of ordinary list shrinker that
     does not attempt to shrink list elements *)
  Fixpoint shrinkListAux_ {A} (l : list A) : list (list A) :=
    match l with
    | [] => []
    | x :: xs => xs :: map (fun xs' : list A => x :: xs') (shrinkListAux_ xs)
    end.

  (* Shrink list of blocks by trying all combinations of removing one action *)
  Fixpoint shrinkChainBuilderAux (blocks : list (BlockHeader * list Action))
                                 : list (list (BlockHeader * list Action)) :=
    match blocks with
    | [] => []
    | block :: blocks' =>
      let '(header, acts) := block in
      let acts_shrunk := shrinkListAux_ acts in
      let block_shrunk := map (fun acts => (header, acts)) acts_shrunk in
        (map (fun block' => block' :: blocks') block_shrunk) ++
          map (fun xs => block :: xs) (shrinkChainBuilderAux blocks')
    end.

  (* Shrinker for ChainBuilders, it will only try to shrink the
    blocks and their action queues, it will not attempt to
    shrink parameters of any actions *)
  Instance shrinkChainBuilder : Shrink ChainBuilder :=
  {
    shrink cb :=
      let cb_blocks := trace_blocks (builder_trace cb) in
      let shrunk_blocks := shrinkChainBuilderAux cb_blocks in
        rebuild_chains shrunk_blocks builder_initial
  }.

  (* Adds a block with miner reward of 50. This is used for all testing *)
  Definition add_block (chain : ChainBuilder) acts
                       : result ChainBuilder AddBlockError :=
    let header :=
        {| block_height := S (chain_height chain);
          block_slot := S (current_slot chain);
          block_finalized_height := finalized_height chain;
          block_creator := BlockCreator;
          block_reward := BlockReward; |} in
    builder_add_block chain header acts.

  Definition gAdd_block (cb : ChainBuilder)
                        (gActOptFromChainSized : Environment -> nat -> GOpt Action)
                        (act_depth : nat)
                        (max_acts_per_block : nat)
                        : G (result ChainBuilder AddBlockError) :=
    acts <- optToVector max_acts_per_block (gActOptFromChainSized cb act_depth) ;;
    returnGen (add_block cb acts).

  (* Given a function from [nat] to a generator,
     try the generator on decreasing number until one returns Ok *)
  Fixpoint try_decreasing {T E} (default : E) (n : nat)
                          (g : nat -> G (result T E)) : G (result T E) :=
      match n with
      | 0 => returnGen (Err default)
      | S n' =>
        ma <- (g n) ;;
        match ma with
        | Err e => try_decreasing default n' g
        | Ok r => returnGen (Ok r)
        end
      end.

  Definition try_repeated {T E} (default : E) (n : nat)
                          (g : G (result T E)) : G (result T E) :=
    backtrack_result default (repeat (1, g) n).

  Definition gChain (init_lc : ChainBuilder)
                    (gActOptFromChainSized : Environment -> nat -> GOpt Action)
                    (max_length : nat)
                    (act_depth : nat)
                    (max_acts_per_block : nat)
                    : G ChainBuilder :=
    let gAdd_block' lc max_acts := gAdd_block lc gActOptFromChainSized act_depth max_acts in
    (* TODO: Not ideal approach, but it suffices for now *)
    let default_error := action_evaluation_depth_exceeded in
    let try_repeat g := try_repeated default_error MaxGenAttempts g in
    let try_decreasing g := try_decreasing default_error max_acts_per_block (fun n => try_repeat (g n)) in
    (* Try decreasing max_acts_per_block, this is needed in some cases
       since there might be blocks where it is not possible to generate
       max_acts_per_block number of valid actions *)
    let fix rec n (lc : ChainBuilder) : G ChainBuilder :=
      match n with
      | 0 => returnGen lc
      (* heuristic: try multiple time and try decreasing for more expected robustness *)
      | S n => lc' <- try_decreasing (gAdd_block' lc) ;;
          match lc' with
          | Ok lc' => rec n lc'
          (* if no new chain could be generated without error, return the old chain *)
          | Err _ => returnGen lc
          end
      end in
    rec max_length init_lc.

  (* Generator that generates blocks of invalid actions.
     It will return a ChainBuilder and a list of actions that will
    cause an error if the actions are added as a new block to the ChainBuilder *)
  Definition gInvalidAction
                        (init_lc : ChainBuilder)
                        (gActOptFromChainSized : Environment -> nat -> GOpt Action)
                        (max_length : nat)
                        (act_depth : nat)
                        (max_acts_per_block : nat)
                        : G (ChainBuilder * list Action) :=
  let fix rec n (lc : ChainBuilder) : G (ChainBuilder * list Action) :=
    match n with
    | 0 => returnGen (lc, []) (* max_length was reached without any errors *)
    | S n =>
        acts <- optToVector max_acts_per_block (gActOptFromChainSized lc act_depth) ;;
        match (TraceGens.add_block lc acts) with
            | Ok lc' => rec n lc'
            (* If no new chain could be generated without error,
               return the trace and action list *)
            | Err _ => returnGen (lc, acts)
            end
    end in
  rec max_length init_lc.

  Definition get_reachable {to} : ChainTrace empty_state to -> reachable to :=
    fun t => inhabits t.

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

  Global Instance genChainTraceSigSized `{GenSized ChainBuilder} :
    GenSized {to : ChainState & ChainTrace empty_state to}.
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
    forAllShrink (gTrace init_lc maxLength)
      shrink (fun cb => checker (pf cb)).

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
    | snoc trace' (Blockchain.step_block _ _ _ _ _ _ _ _ as step) =>
      trace_states_step_block trace' ++ [snd (chainstep_states step)]
    | snoc trace' _ => trace_states_step_block trace'
    | clnil => []
    end.

  (* Gather execution information for each step_action in a ChainTrace *)
  Fixpoint trace_states_step_action {from to} (trace : ChainTrace from to)
                                    : list (Action * list Action * ChainState * ChainState) :=
    match trace with
    | snoc trace' (Blockchain.step_action _ _ act _ new_acts _ _ _ as step) =>
      let '(from, to) := chainstep_states step in
        trace_states_step_action trace' ++ [(act, new_acts, from, to)]
    | snoc trace' _ => trace_states_step_action trace'
    | clnil => []
    end.

  (* Asserts that a ChainState property holds for all step_block ChainStates in a ChainTrace *)
  Definition ChainTrace_ChainTraceProp {prop : Type}
                                       {from to}
                                      `{Checkable prop}
                                       (trace : ChainTrace from to)
                                       (pf : ChainState -> prop)
                                       : Checker :=
    let printOnFail (cs : ChainState) : Checker := whenFail (show cs) (checker (pf cs)) in
    let trace_list := trace_states_step_block trace in
    discard_empty trace_list (conjoin_map printOnFail).

  (* -------------------- Checker combinators on traces -------------------- *)

  (* Asserts that a ChainState property holds on all ChainStates in a ChainTrace *)
  Definition forAllChainState {prop : Type}
                             `{Checkable prop}
                              (maxLength : nat)
                              (init_lc : ChainBuilder)
                              (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                              (pf : ChainState -> prop)
                              : Checker :=
    let printOnFail (cs : ChainState) : Checker := whenFail (show cs) (checker (pf cs)) in
    forAllShrink (gTrace init_lc maxLength) shrink
    (fun cb => discard_empty (trace_states (builder_trace cb)) (conjoin_map printOnFail)).

  (* Asserts that a ChainState property holds on all step_block
     ChainStates in a ChainTrace *)
  Definition forAllBlocks {prop : Type}
                          `{Checkable prop}
                          (maxLength : nat)
                          (init_lc : ChainBuilder)
                          (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                          (pf : ChainState -> prop)
                          : Checker :=
    forAllShrink (gTrace init_lc maxLength) shrink
    (fun cb => ChainTrace_ChainTraceProp (builder_trace cb) pf).

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
        | Blockchain.step_block _ _ _ _ _ _ _ _ =>
          (* next_bstate has acts, bstate_before_step_block has no acts *)
          let '(bstate_before_step_block, next_bstate) := chainstep_states step in
          conjoin [(checker (pf next_bstate prev_bstate)); all_statepairs trace' bstate_before_step_block]
        | _ => all_statepairs trace' prev_bstate
          end
      | clnil => checker true
      end in
    forAllShrink (gTrace init_lc maxLength) shrink
    (fun cb => all_statepairs (builder_trace cb) (last_cstate (builder_trace cb))).

  (* Asserts that property holds on all action evaluations *)
  Definition forAllActionExecution {prop : Type}
                             `{Checkable prop}
                              (maxLength : nat)
                              (init_lc : ChainBuilder)
                              (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                              (pf : Action -> list Action -> ChainState -> ChainState -> prop)
                              : Checker :=
    let printOnFail x : Checker :=
    let '(action, new_acts, cs_from, cs_to) := x in
        whenFail (show cs_from) (checker (pf action new_acts cs_from cs_to)) in
    let trace_list cb := trace_states_step_action (builder_trace cb) in
    forAllShrink (gTrace init_lc maxLength) shrink
    (fun cb => discard_empty (trace_list cb) (conjoin_map printOnFail)).

  (* Asserts that a boolean predicate holds for at least one
     ChainState in the given ChainTrace *)
  Definition existsb_chaintrace {from to}
                                (pf : ChainState -> bool)
                                (trace : ChainTrace from to) : bool :=
    existsb pf (trace_states trace).

  (* Asserts that a ChainState satisfying a given predicate is
     reachable from the given trace generator. *)
  Definition reachableFromSized_chaintrace
                          (maxLength : nat)
                          (init_lc : ChainBuilder)
                          (gTrace : ChainBuilder -> nat -> G ChainBuilder )
                          (pf : ChainState -> bool)
                          : Checker :=
    existsP (gTrace init_lc maxLength) (fun cb =>
      existsb_chaintrace pf (builder_trace cb)).

  Definition reachableFrom_chaintrace init_lc gTrace pf : Checker :=
    sized (fun n => reachableFromSized_chaintrace n init_lc gTrace pf).

  (* This property states that if there is a reachable chainstate
     satisfying the reachable_prop predicate, then all succeeding
     chainstates must satisfy implied_prop *)
  Definition reachableFrom_implies_chaintracePropSized
                        {A prop : Type}
                       `{Checkable prop}
                        (maxLength : nat)
                        (init_cb : ChainBuilder)
                        (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                        (reachable_prop : ChainState -> option A)
                        (implied_prop : A -> list ChainState -> list ChainState -> prop)
                        : Checker :=
  forAllShrink (gTrace init_cb maxLength) shrink
  (fun cb =>
    let trace := builder_trace cb in
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

  Open Scope string_scope.
  (* if pre tests true, then post tests true, for all tested execution traces *)
  Definition pre_post_assertion {Msg State prop : Type}
                               `{Checkable prop}
                               `{Serializable Msg}
                               `{Serializable State}
                               `{Show Msg}
                                (maxLength : nat)
                                (init_chain : ChainBuilder)
                                (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                                (caddr : Address)
                                (pre : State -> Msg -> bool)
                                (post : Environment -> ContractCallContext -> State -> Msg -> option (State * list ActionBody) -> prop) : Checker :=
    let action_bodies actions := map (fun act => act.(act_body)) actions in
    let post_helper env cctx post_cstate new_acts cstate msg : Checker :=
      whenFail ("On Msg: " ++ show msg)
               (checker (post env cctx cstate msg (Some (post_cstate, action_bodies new_acts)))) in
    let stepProp (act : Action) (new_acts : list Action) (cs_from : ChainState) (cs_to : ChainState) :=
      let env_from : Environment := cs_from.(chain_state_env) in
      let env_to : Environment := cs_to.(chain_state_env) in
      let amount :=
        match act.(act_body) with
        | act_call _ amount _ => amount
        | _ => 0%Z
        end in
      let new_balance :=
        if (act.(act_from) =? caddr)%address then
          env_from.(env_account_balances) caddr
        else
          (env_from.(env_account_balances) caddr + amount)%Z in
      let cctx := build_ctx act.(act_origin) act.(act_from) caddr new_balance amount in
        match act.(act_body) with
        | act_call to _ ser_msg =>
          if address_eqb to caddr
          then
            match @deserialize Msg _ ser_msg with
            | Some msg =>
              match get_contract_state State env_from caddr with
              | Some cstate_from =>
                if pre cstate_from msg
                then
                  match get_contract_state State env_to caddr with
                  | Some cstate_to => (post_helper env_from cctx cstate_to new_acts cstate_from msg)
                  | None => checker true
                  end
                else checker true (* TODO: should be discarded!*)
              | None => checker true
              end
            | None => checker true
            end
          else checker true
        | _ => checker true
        end in
    forAllActionExecution maxLength init_chain gTrace stepProp.

  (* For any ChainState in a ChainTrace if pf tests true on all previous
     ChainStates in the ChainTrace then implied_prop tests true, for
     all tested execution traces*)
  Definition forAllChainState_implication {prop : Type}
                             `{Checkable prop}
                              (maxLength : nat)
                              (init_lc : ChainBuilder)
                              (gTrace : ChainBuilder -> nat -> G ChainBuilder)
                              (pf : ChainState -> bool)
                              (implied_prop : ChainState -> prop)
                              : Checker :=
    let printOnFail (cs : ChainState) : Checker := whenFail (show cs) (checker (implied_prop cs)) in
    let map_implication (states : list ChainState) : list Checker :=
       snd (fold_left (fun '(b, checkers) state =>
        (b && (pf state), (implication b (printOnFail state)) :: checkers)) states (true, [])) in
    forAllShrink (gTrace init_lc maxLength) shrink
    (fun cb => conjoin (map_implication (trace_states (builder_trace cb)))).

End TraceGens.
