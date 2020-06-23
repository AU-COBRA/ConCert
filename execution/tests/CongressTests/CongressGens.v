From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import TestUtils ChainPrinters CongressPrinters SerializablePrinters.

Require Import ZArith Strings.Ascii Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
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

Definition LocalChainBase : ChainBase := TestUtils.LocalChainBase.

Definition genToOpt {A : Type} (g : G A) : G (option A) :=
  a <- g ;;
  returnGenSome a.

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
  
(* generators of actions from the LocalChain context type *)

Definition allProposalsOfLC lc : FMap ProposalId Proposal := 
  let all_states := FMap.values (lc_contract_state_deserialized Congress.State lc) in
  let proposals_list : list (ProposalId * Proposal):= fold_left (fun acc s => FMap.elements (proposals s) ++ acc ) all_states [] in
  FMap.of_list proposals_list.

Definition allProposalsWithVotes lc : FMap ProposalId Proposal :=
 filter_FMap (fun p => 0 <? FMap.size (votes (snd p))) (allProposalsOfLC lc).

Definition congressContractsMembers lc : FMap Address (list Address) := 
 map_values_FMap (fun state => map fst (FMap.elements (members state))) (lc_contract_state_deserialized Congress.State lc).

 Definition congressContractsMembers_nonempty lc : FMap Address (list Address) := 
 let members_map := 
  map_values_FMap (fun state => map fst (FMap.elements (members state))) (lc_contract_state_deserialized Congress.State lc) in
  filter_FMap (fun p => 0 <? length (snd p)) members_map. 

Definition congressContractsMembers_nonempty_nonowners lc : FMap Address (list Address) :=   
  map_filter_FMap (fun p =>
    let contract_addr := fst p in
    let state := snd p in
    let members := (map fst o FMap.elements) (members state) in
    let non_owner_members := filter (fun member => negb (address_eqb member (owner state))) members in
    if 0 <? length non_owner_members then Some non_owner_members else None
  ) (lc_contract_state_deserialized Congress.State lc).

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
  p <- sampleFMapOpt contract_members_and_proposals ;;
  let contract_addr := fst p in
  let members_and_proposals := snd p in
  p' <- sampleFMapOpt members_and_proposals ;;
  let member := fst p' in
  let pids := snd p' in
  pid <- elems_opt pids ;;
  mk_call contract_addr member (vote pid).

(* Returns a mapping to proposals which have been discussed long enough, according to the
   current rules in the given LocalChain *)
Definition finishable_proposals (lc : LocalChain) 
                                : FMap Address (FMap ProposalId Proposal) := 
  let contracts_rules : FMap Address Rules := map_values_FMap state_rules (lc_contract_state_deserialized Congress.State lc) in
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
              | Some caller_balance => genToOpt (choose (0%Z, caller_balance))
              | None => returnGenSome 0%Z
              end ;;
    returnGenSome (build_act caller_addr 
      (congress_action_to_chain_action (cact_call contract_addr amount (serializeMsg msg)))) in
  match fuel with
  | 0 => 
    let proposals_map := allProposalsOfLC lc in
    let proposals_with_votes := allProposalsWithVotes lc in
    (* let bindCallerIsOwner {T : Type} := @bindCallerIsOwnerOpt T lc calling_addr contract_addr in *)
    backtrack [
      (* transfer_ownership *)
      (1, contract_members_pair <- sampleFMapOpt (congressContractsMembers_nonempty_nonowners lc) ;;
          let contract_addr := fst contract_members_pair in
          let members := snd contract_members_pair in
          let owner_opt := FMap.find contract_addr (lc_contract_owners lc) in
          match owner_opt with
          | Some owner_addr =>
            new_owner <- (try_gNewOwner lc owner_addr contract_addr) ;;
            mk_call contract_addr owner_addr (transfer_ownership new_owner) 
          | None => returnGen None
          end
      ) ; 
      (* change_rules *)
      (1, p <- sampleFMapOpt (lc_contract_owners lc) ;;
          let contract_addr := fst p in
          let owner_addr := snd p in
          rules <- genToOpt (gRulesSized 4) ;;
          (mk_call contract_addr owner_addr (change_rules rules)) 
      ) ;
      (* add_member *)
      (2, p <- sampleFMapOpt (lc_contract_owners lc) ;;
        let contract_addr := fst p in
        let owner_addr := snd p in
        match (try_newCongressMember lc contract_addr 10) with
        | Some addr => mk_call contract_addr owner_addr (add_member addr)
        | None => returnGen None
        end
      ) ;
      (* remove_member *)
      (1, contract_members_pair <- sampleFMapOpt (congressContractsMembers_nonempty_nonowners lc) ;;
          let contract_addr := fst contract_members_pair in
          let members := snd contract_members_pair in
          member <- elems_opt members ;;
          let owner_opt := FMap.find contract_addr (lc_contract_owners lc) in
          match owner_opt with
          | Some owner_addr =>
            mk_call contract_addr owner_addr (remove_member member)        
          | None => returnGen None
          end
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
      (2, p <- sampleFMapOpt (finishable_proposals lc) ;; 
        let contract_addr := fst p in
        match FMap.find contract_addr (lc_contract_owners lc) with
        | Some owner_addr => 
          p' <- sampleFMapOpt (snd p) ;;
          let pid := fst p' in
          mk_call contract_addr owner_addr (finish_proposal pid)
        | None => returnGen None
        end)
    ]
  | S fuel' => backtrack [
    (1, gCongressActionNew lc fuel') ;
    (* add_proposal *)
    (1, 
      (* recurse. Msg is converted to a SerializedType using 'serialize' *)
      (* This makes it possible to create proposals about proposals about proposals etc... *)
      (* TODO: currently we don't support having multiple actions in a proposal *)
      (* TODO: the way we recurse may be too restrictive - we fix a contract_addr, which may cause gCongressMember
               to return None even though it could have succeeded for another contract_addr.
               Maybe this is not a big issue, though. *)
      act <- gCongressActionNew lc fuel' ;;
      let caller_addr := act.(act_from) in
      match act.(act_body) with
      | act_call contract_addr amount msg => 
        member <- gCongressMember lc contract_addr ;;
        let ca := cact_call contract_addr amount msg in  
        mk_call contract_addr member (create_proposal [ca])
      | _ => returnGenSome act
      end)
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
