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
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import Containers.
From ConCert Require Import ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import TestUtils ChainPrinters SerializablePrinters .

From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

From Coq Require Import ZArith Strings.String.
From Coq Require Import List Int BinInt FunInd.

Import BoundedN.Stdpp.

Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.

Definition LocalChainBase : ChainBase := TestUtils.LocalChainBase.

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

Definition next_header_lc (chain : @LocalChain AddrSize)  :=
    {| block_height := S (chain_height chain);
       block_slot := S (current_slot chain);
       block_finalized_height := finalized_height chain;
       block_creator := creator;
       block_reward := 50; |}.

(* Adds a new block with a given list of actions in that block. Uses next_header_lc to compute header info. *)
Definition my_add_block c acts :=
  match (add_block_exec true c (next_header_lc c) acts) with
  | Err _ => None
  | Ok r => Some r
  end.

Definition gAdd_block (lc : ChainBuilder)
                         (gActOptFromLCSized : LocalChain -> nat -> G (option Action))
                         (act_depth : nat)
                         (max_acts_per_block : nat)
                         : G (result ChainBuilder AddBlockError) :=
  acts <- optToVector max_acts_per_block (gActOptFromLCSized lc.(lcb_lc) act_depth) ;;
  (* TODO: handle case where length acts = 0 *)
  returnGen (add_block lc acts).

Definition gChain (init_lc : ChainBuilder)
                  (gActOptFromLCSized : LocalChain -> nat -> G (option Action))
                  (max_length act_depth : nat) 
                  (max_acts_per_block : nat)
                  : G (result ChainBuilder AddBlockError) := 
  let gAdd_block' lc := gAdd_block lc gActOptFromLCSized act_depth max_acts_per_block in
  let fix rec n (lc : ChainBuilder) : G (result ChainBuilder AddBlockError):=
    match n with
    | 0 => returnGen (Ok lc)
    | S n => lc' <- gAdd_block' lc ;;
             match lc' with
             | Ok lc' => rec n lc'
             | err => returnGen err
             end
    end in 
  rec max_length init_lc.


(* The representation of an execution step.
   A step can either add an empty new block, or add a new block with some actions to execute.
   The next_chain is assumed to be related to prev_chain with the 'my_add_block' function *)
Inductive LocalChainStep {AddrSize : N} : Type :=
| step_add_block : forall (prev_chain : @LocalChain AddrSize)
                          (header : BlockHeader)
                          (next_chain : @LocalChain AddrSize), LocalChainStep
| step_action : forall (prev_chain : @LocalChain AddrSize)
                       (header : BlockHeader)
                       (next_chain : @LocalChain AddrSize)
                       (acts : list Action), LocalChainStep.

(* Helper functions *)

Definition acts_of_lcstep (state : @LocalChainStep AddrSize) :=
  match state with
  | step_add_block _ _ _ => []
  | step_action _ _ _ acts => acts
  end.

Definition prev_lc_of_lcstep (state : @LocalChainStep AddrSize) :=
  match state with
  | step_add_block prev _ _ => prev
  | step_action prev _ _ _ => prev
  end.

Definition next_lc_of_lcstep (state : @LocalChainStep AddrSize) : LocalChain :=
  match state with
  | step_add_block _ _ next => next
  | step_action _ _ next _ => next
  end.
Close Scope string_scope.

(* Shallow Equality of LocalChains *)
Definition lc_shallow_eqb lc1 lc2 : bool :=
  (lc_height lc1 =? lc_height lc2)
  && (lc_slot lc1 =? lc_slot lc2)
  && (@lc_fin_height AddrSize lc1 =? @lc_fin_height AddrSize lc2).


Definition mk_basic_step_add_block c : option (LocalChain * LocalChainStep) :=
  let header := (next_header_lc c) in
  let next := add_block_exec true c header [] in
  match next with
  | Err _ => None
  | Ok c_next => Some (c_next, step_add_block c header c_next)
  end.

Definition mk_basic_step_action c acts : option (LocalChain * LocalChainStep) :=
  let header := (next_header_lc c) in
  let next := add_block_exec true c header acts in
  match next with
  | Ok c_next => Some (c_next, step_action c header c_next acts)
  | Err _ => None
  end.

Open Scope string_scope.
Instance showLocalChainStepVerbose {AddrSize : N} `{Show (@LocalChain AddrSize)} : Show (@LocalChainStep AddrSize) :=
{|
  show step := match step with
  | step_add_block prev header next =>
    "step_add_block{ prev_lc: " ++ show prev ++ sep ++ "header: " ++ show header ++ sep ++ "next_lc:" ++ show next ++ "}"
  | step_action prev header next acts =>
    "step_action{ prev_lc: " ++ show prev ++ sep ++ "header: " ++ show header ++ sep ++ "next_lc:" ++ show next ++ sep ++ "acts: " ++ show acts ++ "}"
  end
|}.

Instance showLocalChainStep {AddrSize : N} `{Show (@LocalChain AddrSize)} : Show (@LocalChainStep AddrSize) :=
{|
  show step := match step with
  | step_add_block prev header next =>
    "step_add_block{ ... }"
  | step_action prev header next acts =>
    "step_action{" ++ show acts ++ "}"
  end
|}.



Definition LocalChainTraceList {AddrSize : N} := list (@LocalChainStep AddrSize).
(* Main generator of execution traces, using a given generator for Actions. *)
(* Generates a trace up to some maximal length. It only contains traces that succeeded according to my_add_block. *)
Fixpoint gLocalChainTraceList_fix (prev_lc : LocalChain)
                              (gActOptFromLCSized : LocalChain -> nat -> G (option Action))
                              (length : nat)
                              (max_nr_acts_per_block : nat)
                              : G LocalChainTraceList :=
  match length with
  | 0 => returnGen []
  | S length =>
    lc_opt <- backtrack [
      (10,
          (* What we're essentially doing here trying twice and then discarding one - to increase robustness.  *)
          let try_twice g := backtrack [(1, g);(1, g)] in
          try_twice (
            acts <- optToVector max_nr_acts_per_block (gActOptFromLCSized prev_lc 2) ;;
            if 0 <? (List.length acts)
            then returnGen (mk_basic_step_action prev_lc acts)
            else returnGen None
          )
          (* acts <- liftM (shrinkListTo 1) (optToVector nr_retries ) ;; *)
          (* returnGen (mk_basic_step_action prev_lc acts) *)
          (* bindGenOpt (gActOptFromLCSized prev_lc 2) *)
          (* (fun act => returnGen (mk_basic_step_action prev_lc [act])) *)
      )
          (* match acts with
          | [] => returnGen None
          | _ => returnGen (mk_basic_step_action prev_lc acts)
          end) *)
      (* (1, returnGen (mk_basic_step_add_block prev_lc)) ; *)
      (* (3, liftM (mk_basic_step_action prev_lc ) (optToVector 1 (gDeployCongressActionFromLC prev_lc)))  *)
      ] ;;
    match lc_opt with
          | Some (lc, step) =>
            trace <- (gLocalChainTraceList_fix lc gActOptFromLCSized length max_nr_acts_per_block) ;;
            match trace with
            | [] => returnGen [step]
            | _ =>  returnGen (cons step trace)
            end
          | None => returnGen []
    end
  end.

Open Scope string_scope.
Instance showLocalChainList : Show LocalChainTraceList :=
{|
  show l := nl ++ "Begin Trace: " ++ nl ++ String.concat (";;" ++ nl) (map show l) ++ nl ++ "End Trace"
|}.
Close Scope string_scope.

(* -------------------- Checker combinators on traces --------------------  *)

(* Checks that a property holds on all states in all traces from a given trace generator *)
Definition forAllTraces {prop : Type}
                       `{Checkable prop}
                        {AddrSize : N}
                        (maxLength : nat)
                        (init_lc : @LocalChain AddrSize)
                        (gTrace : LocalChain -> nat -> G LocalChainTraceList)
                        (pf : LocalChain -> prop)
                        : Checker :=
  forAll (gTrace init_lc maxLength)
  (fun trace => match trace with
                | [] => false ==> true
                | _ => conjoin (map (checker o pf o next_lc_of_lcstep) trace)
                end).

(* A variant where the property is over the step *)
Definition forAllTraces_stepProp {prop : Type}
                       `{Checkable prop}
                        {AddrSize : N}
                        (maxLength : nat)
                        (init_lc : @LocalChain AddrSize)
                        (gTrace : LocalChain -> nat -> G LocalChainTraceList)
                        (pf : LocalChainStep -> prop)
                        : Checker :=
  forAll (gTrace init_lc maxLength)
  (fun trace => match trace with
                | [] => false ==> true
                | _ => conjoin (map (checker o pf) trace)
                end).

(* A variant where the property is over the whole trace *)
Definition forAllTraces_traceProp {prop : Type}
                       `{Checkable prop}
                        {AddrSize : N}
                        (maxLength : nat)
                        (init_lc : LocalChain)
                        (gTrace : (@LocalChain AddrSize) -> nat -> G LocalChainTraceList)
                        (pf : LocalChainTraceList -> prop)
                        : Checker :=
  forAll (gTrace init_lc maxLength)  pf.

Definition reachableFromSized {AddrSize : N}
                         (maxLength : nat)
                         (init_lc : LocalChain)
                         (gTrace : (@LocalChain AddrSize) -> nat -> G LocalChainTraceList)
                         (pf : LocalChainStep -> bool)
                         : Checker :=
  existsP (gTrace init_lc maxLength) (fun trace => existsb pf trace).

Definition reachableFrom {AddrSize : N} init_lc gTrace pf : Checker :=
  sized (fun n => @reachableFromSized AddrSize n init_lc gTrace pf).

Fixpoint cut_at_first_satisfying_fix {A : Type} (p : A -> bool) (l : list A) (acc : list A) : option (list A) :=
  match l with
  | [] => None
  | x::xs => if p x
             then Some (acc ++ [x])
             else (cut_at_first_satisfying_fix p xs (acc ++ [x]))
  end.

Definition cut_at_first_satisfying_ {A : Type} (p : A -> bool) (l : list A) := cut_at_first_satisfying_fix p l [] .

(* represents: if there is a state x, satisfying pf1, reachable from init_lc,
               then there is a state y, satisfyring pf2, reachable from state x. *)
Definition reachableFrom_implies_reachableSized
                         (maxLength : nat)
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                         (pf1 : LocalChain -> bool)
                         (pf2 : LocalChain -> bool)
                         : Checker :=
  expectFailure (forAll (gTrace init_lc maxLength)
    (fun trace =>
     match cut_at_first_satisfying_ (pf1 o next_lc_of_lcstep) trace with
      | None => checker true
      | Some trace_cut =>
        let new_init_lc := (List.last (map next_lc_of_lcstep trace_cut) init_lc) in
        expectFailure (forAll (gTrace new_init_lc maxLength)
        (fun new_trace => whenFail
          ("Success - found witnesses satisfying the predicates:" ++ nl ++
          "First trace:"  ++
          show trace_cut ++ nl ++
          "Second trace:" ++
          show new_trace ++ nl)
          ((checker o negb) (existsb pf2 (map (next_lc_of_lcstep) new_trace)))
        ))
      end)).

Definition reachableFrom_implies_reachable init_lc gTrace pf1 pf2 : Checker :=
  sized (fun n => reachableFrom_implies_reachableSized n init_lc gTrace pf1 pf2).

(* If a state satisfying pf1 is reachable from init_lc, then any trace from this state satisfies pf_trace  *)
Definition reachableFrom_implies_tracePropSized
                         {A prop : Type}
                        `{Checkable prop}
                         (maxLength : nat)
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                         (pf1 : LocalChainStep -> option A)
                         (pf_trace : A -> LocalChainTraceList -> prop)
                         : Checker :=
  forAll (gTrace init_lc maxLength)
  (fun trace =>
    let pf1_bool lc := match pf1 lc with Some _ => true | None => false end in
    match cut_at_first_satisfying_ pf1_bool trace with
    | Some (x::xs as trace_cut) =>
      let last_step := (List.last trace_cut x) in
      isSomeCheck (pf1 last_step)
        (fun a =>
          let new_init_lc := next_lc_of_lcstep last_step in
          (forAll (gTrace new_init_lc maxLength)
            (fun new_trace => (pf_trace a new_trace))
          )
        )
    | Some [] => checker false
    | _ => false ==> true
    end).

Definition reachableFrom_implies_traceProp {A : Type}
                                           (init_lc : (@LocalChain AddrSize))
                                           (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                                           (pf1 : LocalChainStep -> option A)
                                           (pf_trace : A -> LocalChainTraceList -> bool)
                                           : Checker :=
  sized (fun n => reachableFrom_implies_tracePropSized n init_lc gTrace pf1 pf_trace).

Fixpoint split_at_first_satisfying_fix {A : Type} (p : A -> bool) (l : list A) (acc : list A) : option (list A * list A) :=
  match l with
  | [] => None
  | x::xs => if p x
             then Some (acc ++ [x], xs)
             else (split_at_first_satisfying_fix p xs (acc ++ [x]))
  end.

Definition split_at_first_satisfying {A : Type} (p : A -> bool) (l : list A) : option (list A * list A) :=
  split_at_first_satisfying_fix p l [].

(* Compute (split_at_first_satisfying (fun x => x =? 2) [1;3;2;4;5]). *)

Definition reachableFrom_implies_tracePropSized_new
                         {A prop : Type}
                        `{Checkable prop}
                         (maxLength : nat)
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                         (pf1 : LocalChainStep -> option A)
                         (pf_trace : A -> LocalChainTraceList -> LocalChainTraceList -> prop)
                         : Checker :=
  forAll (gTrace init_lc maxLength)
  (fun trace =>
    let pf1_bool := isSome o pf1 in
    match split_at_first_satisfying pf1_bool trace with
    | Some ((x::xs) as pre, (y::ys) as post) =>
      let last_step := (List.last pre x) in
      isSomeCheck (pf1 last_step)
        (fun a => (pf_trace a pre post))
    | _ => false ==> true
    end).

(* if pre tests true, then post tests true, for all tested execution traces *)
Definition pre_post_assertion {Setup Msg State prop : Type}
                             `{Checkable prop}
                             `{Serializable Msg}
                             `{Serializable State}
                             `{Serializable Setup}
                              {AddrSize : N}
                              (maxLength : nat)
                              (init_lc : @LocalChain AddrSize)
                              (gTrace : LocalChain -> nat -> G LocalChainTraceList)
                              (c : Contract Setup Msg State)
                              (pre : State -> Msg -> bool)
                              (post : ContractCallContext -> State -> Msg -> option (State * list ActionBody) -> prop) : Checker :=
    let ContractType := Contract Setup Msg State in
    let contracts_of_step step : list (Address * State) :=
      let lc := prev_lc_of_lcstep step in
      FMap.elements (lc_contract_state_deserialized State lc) in
    let messages_of_step step := fold_right (fun act acc =>
        match act.(act_body) with
        | act_call _ _ ser_msg =>
          match @deserialize Msg _ ser_msg with
          | Some msg => (act, msg) :: acc
          | None => acc
          end
        | _ => acc
        end
      ) [] (acts_of_lcstep step) in
    let stepProp step :=
      let lc := prev_lc_of_lcstep step in
      let msgs := messages_of_step step in
      let contracts := contracts_of_step step in
      let execute_receive chain caddr cstate act msg :=
        let amount :=
          match act.(act_body) with
          | act_call _ amount _ => amount
          | _ => 0%Z
          end in
        let cctx := build_ctx act.(act_from) caddr amount in
        let new_state := c.(receive) chain cctx cstate (Some msg) in
        (cctx, new_state) in

      conjoin (map (fun '(caddr, cstate) =>
        (* test that executing receive on the messages that satisfy the precondition, also satisfy the postcondition *)
        conjoin (map (fun '(act, msg) =>
          let (cctx, post_state) := execute_receive lc caddr cstate act msg in
          pre cstate msg ==> post cctx cstate msg post_state
        ) msgs)
      ) contracts) in
    (* combine it all with the forAllTraces checker combinator *)
    forAllTraces_stepProp maxLength init_lc gTrace stepProp.
