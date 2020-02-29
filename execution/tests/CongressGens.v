From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters.

Require Import ZArith Strings.Ascii Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Require Import Containers.

Notation "f 'o' g" := (compose f g) (at level 50).

(* ChainGens for the types defined in the Congress contract *)

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.


Definition gRulesSized (n : nat) : G Rules :=
  vote_count <- gZPositiveSized n ;;
  margin <- liftM Z.of_nat (gIntervalNat n (2 * n)) ;;
  liftM (build_rules vote_count margin) arbitrary.  

Instance genRulesSized : GenSized Rules :=
{|
  arbitrarySized := gRulesSized
|}.

Instance genSetupSized : GenSized Setup := 
{|
  arbitrarySized n := liftM build_setup (arbitrarySized n)
|}.

Definition gCongressAction' {ctx : ChainContext LocalChainBase}
                           (gMsg : G SerializedValue) 
                           : G CongressAction :=
  (* We only want to generate positive amounts for now, but could be worth looking into *)
  freq [
    (1, liftM2 cact_transfer (ctx_gAccountAddr ctx) gZPositive);
    (1, liftM3 cact_call (ctx_gContractAddr ctx) gZPositive gMsg)
  ].

Sample (ctx <- @arbitrarySized _ genLocalChainContext 1 ;; @gCongressAction' ctx arbitrary).



Definition gMsgSimple (ctx : ChainContext LocalChainBase) : G Msg := 
  freq [
    (1, liftM transfer_ownership (ctx_gAccountAddr ctx)) ;
    (1, liftM change_rules arbitrary) ;
    (2, liftM add_member (ctx_gAccountAddr ctx)) ;
    (2, liftM remove_member (ctx_gAccountAddr ctx)) ;
    (2, liftM vote_for_proposal arbitrary) ;
    (2, liftM vote_against_proposal arbitrary) ;
    (2, liftM retract_vote arbitrary) ;
    (2, liftM finish_proposal arbitrary)
  ].
Definition gMsg' : G Msg := 
  ctx <- arbitrary ;; gMsgSimple ctx.

Sample gMsg'.


Sample (ctx <- @arbitrarySized _ genLocalChainContext 1 ;; 
        ctx_gAccountAddr ctx).


Fixpoint gMsgSized (ctx : ChainContext LocalChainBase) (n : nat) : G Msg :=
  let default := liftM add_member (ctx_gAccountAddr ctx) in
  match n with
    | 0 => gMsgSimple ctx
    | S n' => freq [
        (1,
        (* recurse. Msg is converted to a SerializedType using 'serialize' *)
        (* This makes it possible to create proposals about proposals about proposals etc... *)
        congressActions <- listOf (@gCongressAction' ctx (liftM serialize (gMsgSized ctx n'))) ;;
        returnGen (create_proposal congressActions)) ;
        (7, gMsgSimple ctx)
      ]
  end.

Sample (ctx <- arbitrary ;; @gMsgSized ctx 1).

Example ex_simple_msg : Msg := create_proposal [cact_call zero_address 1%Z (serialize 123)].
Example ex_msg : Msg := create_proposal [cact_call zero_address 0%Z (serialize ex_simple_msg)].
(* Currently kinda buggy: nested messages (with create_proposal) dont properly show the inner, serialized messages *)
(* Compute ((show o deserialize o serialize) ex_simple_msg). *)
(* Compute (show ex_msg).  *)

(* Generates semantically valid/well-formed messages *)
(* Examples of validity requirements: 
   - retract_vote can only be called on a proposal if it there exists a vote on this proposal 
*)
Definition gValidSimpleMsg (ctx : ChainContext LocalChainBase) 
                           (proposals : FMap nat Proposal) 
                           : G Msg  := 
  let proposals_pairlist := FMap.elements proposals in
  let proposalIds := map fst proposals_pairlist in
  let proposalIds_and_votes := map (fun p => (fst p, votes (snd p))) proposals_pairlist in
  let proposalIds_with_votes : list nat := fold_left (fun acc p => if FMap.size (snd p) =? 0 then acc else (fst p) :: acc) proposalIds_and_votes [] in 
  let retract_vote_weight := if length proposalIds_with_votes  =? 0 then 0 else 2 in
  let vote_proposal_weight := if length proposalIds =? 0 then 0 else 2 in
  default_pid <- arbitrary ;;
  freq [
    (1, liftM transfer_ownership (ctx_gAccountAddr ctx)) ;
    (1, liftM change_rules arbitrary) ;
    (2, liftM add_member (ctx_gAccountAddr ctx)) ;
    (2, liftM remove_member (ctx_gAccountAddr ctx)) ;
    (vote_proposal_weight, liftM vote_for_proposal (elems_ default_pid proposalIds)) ;
    (vote_proposal_weight, liftM vote_against_proposal (elems_ default_pid proposalIds)) ;
    (vote_proposal_weight, liftM finish_proposal (elems_ default_pid proposalIds)) ;
    (retract_vote_weight, 
      pid <- elems_ default_pid proposalIds_with_votes ;;
      returnGen (retract_vote pid))
  ].

Definition gCongressActionSized {ctx : ChainContext LocalChainBase}
                                (n : nat)
                                : G CongressAction 
                                := @gCongressAction' ctx (liftM serialize (@gMsgSized ctx n)).


Sample (ctx <- arbitrary ;; gMsgSized ctx 2).

Example ex_call_congress_action := ctx <- arbitrary ;; 
                                   liftM (cact_call zero_address 0%Z) (liftM serialize (gMsgSized ctx 2) ).
Sample ex_call_congress_action.

Open Scope Z_scope.

Definition gProposalSized {ctx : ChainContext LocalChainBase} 
                          (proposed_in : nat) (* obtained from the Chain *)
                          (nr_votes : nat)
                          (n : nat)
                                   : G Proposal :=
  bound <- arbitrarySized n ;;
  actions <- vectorOf bound (@gCongressActionSized ctx n) ;;
  vote_vals <- vectorOf nr_votes (elems [-1%Z; 1%Z]) ;; (* -1 = vote against, 1 = vote for*) 
  votes <- gFMapFromInput (ctx_accounts ctx) vote_vals ;;
  let vote_result := fold_left Z.add (FMap.values votes) 0%Z in
  (* vote_result <- choose (-(Z.of_nat nr_votes), Z.of_nat nr_votes);; *)
  returnGen (build_proposal actions votes vote_result proposed_in).

Sample (ctx <- arbitrary ;; @gProposalSized ctx 0 10 1).


Close Scope Z_scope.

Definition gStateSized {ctx : ChainContext LocalChainBase} 
                       (current_slot : nat) (* used to ensure that the generated proposals are never proposed at a later date *)
                       (n : nat) 
                       : G Congress.State :=
  let nr_accounts := length (ctx_accounts ctx) in
  default_addr <- (ctx_gAccountAddr ctx) ;;
  owner <- elems_ default_addr (ctx_accounts ctx) ;; (* owner is a member *)
  rules <- arbitrarySized n ;;
  proposalIds <- vectorOfCount 0 n ;;
  nr_votes <- choose (1, nr_accounts) ;;
  proposals <- vectorOf n (slot <- (arbitrarySized current_slot) ;; @gProposalSized ctx slot nr_votes  (n/2)) ;;
  proposals_map <- gFMapFromInput proposalIds proposals ;;
  next_proposal_id <- arbitrary ;; (* TODO: maybe just let it be 0*)
  unit_list <- (vectorOf nr_accounts (returnGen tt)) ;;
  members <- gFMapFromInput (ctx_accounts ctx) unit_list ;;
  returnGen (build_state owner rules proposals_map next_proposal_id members).

Definition gProposalIdFromState (state : Congress.State) : G ProposalId := 
  let pelems := FMap.elements (proposals state) in
  let pids := map fst pelems in
  (* Choose one proposal id at random. If empty, choose an arbitrary one. *)
  default_pid <- arbitrary ;; elems_ default_pid  pids.

Definition gProposalFromState {ctx : ChainContext LocalChainBase} 
                              (state : Congress.State)
                              (proposed_in : nat) 
                              : G Proposal := 
  let pelems := FMap.elements (proposals state) in
  let pids := map snd pelems in
  let max_nr_votes : nat := (length o FMap.elements) (members state) in
  (* Choose one proposal id at random. If empty, choose an arbitrary one. *)
  nr_votes <- arbitrarySized max_nr_votes ;;
  default_proposal <- @gProposalSized ctx proposed_in nr_votes 3 ;; 
  elems_ default_proposal pids.

Definition gCongressContract : G (Contract Setup Msg Congress.State) :=
  returnGen Congress.contract.
  
Sample gCongressContract.

Definition gValidContractCallContext {ctx : ChainContext LocalChainBase}
                                            (owner_addr : Address) 
                                            (msg : Msg)
                                            : G (@ContractCallContext LocalChainBase) := 
  match msg with
  (* these messages must be created by the owner of the congress *)
  | change_rules _ | add_member _ | remove_member _ | transfer_ownership _ => gContractCallContextWithOwner ctx owner_addr 
  | _ => gContractCallContext ctx 
  end.
  
(* Sample (ctx <-arbitrarySized 4 ;; state <- @gStateSized ctx 10 2 ;; msg <- gMsgSized ctx 3 ;; @gValidContractCallContextFromMsg ctx state msg). *)

Definition receive_is_some_P chain ctx state msg := 
  match (receive chain ctx state (Some msg)) with
  | Some _ => true
  | None => false
  end.
  
Definition check_receive_is_some_P := 
  forAll5
    (gLocalChainContext 4)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun ctx chain => @gStateSized ctx (current_slot chain) 2)
    (fun ctx cctx state => gValidSimpleMsg ctx (proposals state))
    (fun ctx _ state msg => @gValidContractCallContext ctx (owner state) msg)
    (fun _ chain state msg cctx => receive_is_some_P chain cctx state msg).


(* We expect to get fail this test at this point*)
(* QuickChick check_receive_is_some_P. *)
(* coqtop-stdout:ChainContext{...}
Chain{height: 2, current slot: 0, final height: 1}
State{owner: 7%256, rules: Rules{min_vote_count_permille: 2, margin_needed_permille: 2, debating_period_in_blocks: 4}, proposals: ["0-->Proposal{actions: [(transfer: 121%256, 4)], votes: [\"121%256-->-1\"], vote_result: 1, proposed_in: 0, }\n"; "1-->Proposal{actions: [(call: 179%256, 1, SerializedValue{(4,(((1,(161,(4,((8,(5,())),())))),((0,(111,(4,()))),((0,(8,(4,()))),()))),()))})], votes: [\"121%256-->-1\"], vote_result: 4, proposed_in: 0, }\n"], next_proposal_id: 5, members: ["7%256-->tt"; "121%256-->tt"; "125%256-->tt"; "110%256-->tt"]}
(finish_proposal 1)
ContractCallContext{ctx_from: 121%256, ctx_contract_addr: 143%256, ctx_amount: 5}
*** Failed after 13 tests and 0 shrinks. (0 discards) 
*)


Definition gActionOfCongress ctx n : G Action := 
  liftM2 (@build_act LocalChainBase) (ctx_gAccountAddr ctx) (liftM congress_action_to_chain_action (@gCongressActionSized ctx n)).

Definition gContractCallInfo := liftM3 build_call_info arbitrary arbitrary arbitrary.
  
Sample gContractCallInfo.
