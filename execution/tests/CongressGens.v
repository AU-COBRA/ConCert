From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters SerializablePrinters.

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

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.


Definition serializeMsg := serialize Msg _.


Notation "f 'o' g" := (compose f g) (at level 50).

(* ChainGens for the types defined in the Congress contract *)

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.


Definition gRulesSized (n : nat) : G Rules :=
  vote_count <- choose(1%Z, 1000%Z) ;;
  margin <- choose(1%Z, 1000%Z) ;;
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
  freq [
    (1, liftM2 cact_transfer (ctx_gAccountAddr ctx) gZPositive);
    (1, liftM3 cact_call (ctx_gContractAddr ctx) gZPositive gMsg)
  ].




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
Sample (ctx <- @arbitrarySized _ genLocalChainContext 1 ;; @gCongressAction' ctx (liftM serializeMsg (gMsgSimple ctx))).


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
        congressActions <- listOf (@gCongressAction' ctx (liftM serializeMsg (gMsgSized ctx n'))) ;;
        returnGen (create_proposal congressActions)) ;
        (7, gMsgSimple ctx)
      ]
  end.

Sample (ctx <- arbitrary ;; @gMsgSized ctx 1).

Example ex_simple_msg : Msg := create_proposal [cact_transfer zero_address 1%Z ].
Example ex_msg : Msg := create_proposal [cact_call zero_address 0%Z (serialize Msg _ ex_simple_msg)].
Compute ((show o (deserialize Msg _) o serializeMsg) ex_simple_msg).
Compute (show ex_msg). 

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
                                := @gCongressAction' ctx (liftM serializeMsg (@gMsgSized ctx n)).


Sample (ctx <- arbitrary ;; gMsgSized ctx 2).

Example ex_call_congress_action := ctx <- arbitrary ;; 
                                   liftM (cact_call zero_address 0%Z) (liftM serializeMsg (gMsgSized ctx 2) ).
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
  nr_votes <- choose (1, if nr_accounts =? 0 then 1 else nr_accounts) ;;
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
  
(* Sample gContractCallInfo. *)



(* ------------------------------------------------------ *)
(* generators of actions from the LocalChain context type *)

Definition allProposalsOfLC lc : FMap ProposalId Proposal := 
  let all_states := FMap.values (lc_contract_state_deserialized lc) in
  let proposals_list : list (ProposalId * Proposal):= fold_left (fun acc s => FMap.elements (proposals s) ++ acc ) all_states [] in
  FMap.of_list proposals_list.

Definition allProposalsWithVotes lc : FMap ProposalId Proposal :=
 filter_FMap (fun p => 0 <? FMap.size (votes (snd p))) (allProposalsOfLC lc).

Definition congressContractsMembers lc : FMap Address (list Address) := 
 map_values_FMap (fun state => map fst (FMap.elements (members state))) (lc_contract_state_deserialized lc).

 Definition congressContractsMembers_nonempty lc : FMap Address (list Address) := 
 let members_map := 
  map_values_FMap (fun state => map fst (FMap.elements (members state))) (lc_contract_state_deserialized lc) in
  filter_FMap (fun p => 0 <? length (snd p)) members_map. 

Definition congressContractsMembers_nonempty_nonowners lc : FMap Address (list Address) :=   
  map_filter_FMap (fun p =>
    let contract_addr := fst p in
    let state := snd p in
    let members := (map fst o FMap.elements) (members state) in
    let non_owner_members := filter (fun member => negb (address_eqb member (owner state))) members in
    if 0 <? length non_owner_members then Some non_owner_members else None
  ) (lc_contract_state_deserialized lc).

Definition gCongressMember (lc : LocalChain) 
                           (contract_addr : Address) 
                           : G (option Address) := 
  let members_map := (congressContractsMembers lc) in
  bindGenOpt (returnGen (FMap.find contract_addr members_map))
  (fun members => 
    match members with
    | [] => returnGen None
    | m::ms => liftM Some (elems_ m members)
    end).


Definition gCongressMember_without_caller (lc : LocalChain) 
                           (calling_addr : Address) 
                           (contract_addr : Address) 
                           : G (option Address) := 
  let members_map := (congressContractsMembers lc) in
  bindGenOpt (returnGen (FMap.find contract_addr members_map))
  (fun members => 
    let members_without_caller := List.remove address_eqdec calling_addr members in
    match members_without_caller with
    | [] => returnGen None
    | m::ms => liftM Some (elems_ m members_without_caller)
    end).


Fixpoint try_newCongressMember_fix (members : list Address) nr_attempts curr_nr : option Address  :=
  let fix aux nr_attempts curr_nr :=
  match nr_attempts with
  | 0 => None
  | S n' => match @BoundedN.of_nat AddrSize curr_nr with
            | Some addr_attempt => if List.existsb (address_eqb addr_attempt) members
                                   then aux n' (S curr_nr)
                                   else Some addr_attempt
            | None => None
            end
  end in aux nr_attempts curr_nr.

  
Definition try_newCongressMember (lc : LocalChain)
                                 (congress_addr : Address) 
                                 (nr_attempts : nat) : option Address := 
  let current_members_opt := FMap.find congress_addr (congressContractsMembers lc) in
  match current_members_opt with
  | Some current_members => try_newCongressMember_fix current_members nr_attempts 0
  | None => None
  end.

Definition bindCallerIsOwnerOpt {A : Type} 
                                (lc : LocalChain) 
                                (calling_addr : Address)
                                (contract_addr : Address)
                                (g : G (option A)) : G (option A) := 
  if address_eqb calling_addr contract_addr 
  then g 
  else let owner_opt := FMap.find contract_addr (lc_contract_owners lc) in
  match owner_opt with
  | None => returnGen None
  | Some owner => if address_eqb owner calling_addr
                  then g
                  else returnGen None
  end.

Definition try_gNewOwner lc calling_addr contract_addr : G (option Address):= 
  bindCallerIsOwnerOpt lc calling_addr contract_addr (gCongressMember_without_caller lc calling_addr contract_addr).


(* Sample (@gMsgSimpleFromLC lc_initial). *)
(* 
Definition optToList {A : Type} : (G (option A)) -> G (list A) :=
  fun g =>
  l <- listOf g ;;
  let l' := fold_left (fun acc aopt => match aopt with
                          | Some a => a :: acc
                          | None => acc
                          end) l []
  in returnGen l'. *)



Definition vote_proposal (contract_members_and_proposals : FMap Address (FMap Address (list ProposalId))) 
                         (mk_call : Address -> Address -> Msg -> G (option Action))
                         (vote : ProposalId -> Msg):= 
  bindGenOpt (sampleFMapOpt contract_members_and_proposals)
  (fun p =>
    let contract_addr := fst p in
    let members_and_proposals := snd p in
    bindGenOpt (sampleFMapOpt members_and_proposals)
    (fun p' =>
      let member := fst p' in
      let pids := snd p' in
      match pids with
      | (pid::_) => 
        pid <- elems_ pid pids ;;
        mk_call contract_addr member (vote pid)
      | _ => returnGen None
      end)).

(* Returns a mapping to proposals which have been discussed long enough, according to the
   current rules in the given LocalChain *)
Definition finishable_proposals (lc : LocalChain) 
                                : FMap Address (FMap ProposalId Proposal) := 
  let contracts_rules : FMap Address Rules := map_values_FMap state_rules (lc_contract_state_deserialized lc) in
  map_filter_FMap (fun p =>
    let caddr := fst p in
    let pids_map := snd p in
    match FMap.find caddr contracts_rules with
    | Some rules =>
      let pids_map_filtered := filter_FMap (fun p =>
        (snd p).(proposed_in) + rules.(debating_period_in_blocks) <=? lc.(lc_slot)  
      ) pids_map in
      if 0 <? FMap.size pids_map_filtered
      then Some pids_map_filtered
      else None
    | None => None
    end
  ) (lc_proposals lc)
.



Fixpoint gCongressActionNew (lc : LocalChain) (fuel : nat) : G (option Action) :=
  let mk_call contract_addr caller_addr msg := 
    amount <- match lc_account_balance lc caller_addr with
              | Some caller_balance => choose (0%Z, caller_balance)
              | None => returnGen 0%Z
              end ;;
    returnGen (Some (build_act caller_addr 
      (congress_action_to_chain_action (cact_call contract_addr amount (serializeMsg msg))))) in
  match fuel with
  | 0 => 
    let proposals_map := allProposalsOfLC lc in
    let proposals_with_votes := allProposalsWithVotes lc in
    (* let bindCallerIsOwner {T : Type} := @bindCallerIsOwnerOpt T lc calling_addr contract_addr in *)
    backtrack [
      (* transfer_ownership *)
      (1, bindGenOpt (sampleFMapOpt (congressContractsMembers_nonempty_nonowners lc))
          (fun contract_members_pair => 
          let contract_addr := fst contract_members_pair in
          let members := snd contract_members_pair in
          let owner_opt := FMap.find contract_addr (lc_contract_owners lc) in
          match owner_opt with
          | Some owner_addr =>
              bindGenOpt (try_gNewOwner lc owner_addr contract_addr) 
                (fun new_owner => mk_call contract_addr owner_addr (transfer_ownership new_owner))        
          | None => returnGen None
          end)
      ) ; 
      (* change_rules *)
      (1, bindGenOpt (sampleFMapOpt (lc_contract_owners lc))
          (fun p =>
          let contract_addr := fst p in
          let owner_addr := snd p in
          rules <- (gRulesSized 4) ;;
          (mk_call contract_addr owner_addr (change_rules rules)) 
          )
      ) ;
      (* add_member *)
      (2, bindGenOpt (sampleFMapOpt (lc_contract_owners lc))
          (fun p =>
          let contract_addr := fst p in
          let owner_addr := snd p in
          match (try_newCongressMember lc contract_addr 10) with
          | Some addr => mk_call contract_addr owner_addr (add_member addr)
          | None => returnGen None
          end)
      ) ;
      (* remove_member *)
      (1, bindGenOpt (sampleFMapOpt (congressContractsMembers_nonempty_nonowners lc))
          (fun contract_members_pair => 
          let contract_addr := fst contract_members_pair in
          let members := snd contract_members_pair in
          member <- elems_ contract_addr members ;;
          let owner_opt := FMap.find contract_addr (lc_contract_owners lc) in
          match owner_opt with
          | Some owner_addr =>
            mk_call contract_addr owner_addr (remove_member member)        
          | None => returnGen None
          end)
      ) ;
      (* vote_for_proposal *)
      (* Requirements:
         - contract with a proposal and members must exist
         - only members which have not already voted can vote again *)
      (2, vote_proposal (lc_contract_members_and_proposals_new_voters lc) 
                        mk_call vote_for_proposal ) ;
      (* vote_against_proposal *)
      (2, vote_proposal (lc_contract_members_and_proposals_new_voters lc) 
                        mk_call vote_against_proposal ) ;
      (* retract_vote *)
      (2, vote_proposal (lc_contract_members_and_proposals_with_votes lc) 
                        mk_call retract_vote) ;
      (* finish_proposal *)
      (* Requirements:
         - only contract owner can finish proposals
         - the debating period must have passed *)
      (2, bindGenOpt (sampleFMapOpt (finishable_proposals lc)) 
          (fun p => 
          let contract_addr := fst p in
          match FMap.find contract_addr (lc_contract_owners lc) with
          | Some owner_addr => bindGenOpt (sampleFMapOpt (snd p)) (fun p' =>
            let pid := fst p' in
            mk_call contract_addr owner_addr (finish_proposal pid)
          )
          | None => returnGen None
          end))
    ]
  | S fuel' => backtrack [
    (7, gCongressActionNew lc fuel') ;
    (* add_proposal *)
    (1, 
      (* recurse. Msg is converted to a SerializedType using 'serialize' *)
      (* This makes it possible to create proposals about proposals about proposals etc... *)
      (* TODO: currently we don't support having multiple actions in a proposal *)
      (* TODO: the way we recurse may be too restrictive - we fix a contract_addr, which may cause gCongressMember
               to return None even though it could have succeeded for another contract_addr.
               Maybe this is not a big issue, though. *)
      bindGenOpt (gCongressActionNew lc fuel')
      (fun act => 
        let caller_addr := act.(act_from) in
        match act.(act_body) with
        | act_call contract_addr amount msg => bindGenOpt (gCongressMember lc contract_addr)
          (fun member =>
          let ca := cact_call contract_addr amount msg in  
          mk_call contract_addr member (create_proposal [ca]))
        | _ => returnGen (Some act)
        end 
      ))
  ] 
  end.

Definition gDeployCongressActionFromLC lc : G (option Action) := 
  calling_addr_opt <- gAccountAddrFromLocalChain lc ;;
  setup <- arbitrary ;;
  deploy_act <- (gDeploymentAction Congress.contract setup) ;;
  match calling_addr_opt with
  | Some calling_addr => liftM Some (returnGen (@build_act LocalChainBase calling_addr deploy_act))
  | None => returnGen None
  end.
