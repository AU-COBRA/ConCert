From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Congress Require Import Congress_Buggy.
From Coq Require Import ZArith.
From Coq Require Import List. Import ListNotations.
Import MonadNotation.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

Definition serializeMsg := serialize Msg _.

Definition gRulesSized (n : nat) : G Rules :=
  vote_count <- choose(1%Z, 1000%Z) ;;
  margin <- choose(1%Z, 1000%Z) ;;
  liftM (build_rules vote_count margin) arbitrary.

#[export]
Instance genRulesSized : GenSized Rules :=
{|
  arbitrarySized := gRulesSized
|}.

#[export]
Instance genSetupSized : GenSized Setup :=
{|
  arbitrarySized n := liftM build_setup (arbitrarySized n)
|}.

(* ------------------ generators of actions --------------------------- *)

Definition congressContractsMembers_nonowners state : list Address :=
    let members := (map fst o FMap.elements) (members state) in
    let non_owner_members := filter (fun member => address_neqb member (owner state)) members in
    non_owner_members.

Definition gCongressMember_without_caller (state : Congress_Buggy.State)
                           (calling_addr : Address)
                           (contract_addr : Address)
                           : GOpt Address :=
  let members := (map fst o FMap.elements) (members state) in
  let members_without_caller := List.remove address_eqdec calling_addr members in
  match members_without_caller with
  | [] => returnGen None
  | m ::ms => liftM Some (elems_ m members_without_caller)
  end.

Definition try_newCongressMember_fix (members : list Address)
                                   nr_attempts curr_nr
                                   : option Address :=
  let fix aux nr_attempts curr_nr :=
  match nr_attempts with
  | 0 => None
  | S n' =>
      match @BoundedN.of_nat AddrSize curr_nr with
      | Some addr_attempt =>
          if List.existsb (address_eqb addr_attempt) members
          then aux n' (S curr_nr)
          else Some addr_attempt
      | None => None
      end
  end in aux nr_attempts curr_nr.

Definition try_newCongressMember (state : Congress_Buggy.State)
                                 (congress_addr : Address)
                                 (nr_attempts : nat)
                                 : option Address :=
  let members := (map fst o FMap.elements) (members state) in
  try_newCongressMember_fix members nr_attempts 0.

Definition bindCallerIsOwnerOpt {A : Type}
                                (state : Congress_Buggy.State)
                                (calling_addr : Address)
                                (contract_addr : Address)
                                (g : GOpt A)
                                : GOpt A :=
  if address_eqb calling_addr contract_addr
  then g
  else if address_eqb state.(owner) calling_addr
       then g
       else returnGen None.

Definition try_gNewOwner state calling_addr contract_addr : GOpt Address :=
  bindCallerIsOwnerOpt state calling_addr contract_addr
    (gCongressMember_without_caller state calling_addr contract_addr).

Definition validate_addr (a : Address) : GOpt (address_is_contract a = false) :=
  match (Bool.bool_dec (address_is_contract a) true ) with
  | left _ => returnGen None
  | right p => returnGenSome (Bool.not_true_is_false _ p)
  end.

Definition vote_proposal (caddr : Address)
                         (members_and_proposals : FMap Address (list ProposalId))
                         (call : forall (caddr : Address) (origin : Address),
                             address_is_contract origin = false -> Msg -> GOpt Action)
                         (vote : ProposalId -> Msg) : GOpt Action :=
  '(member, pids) <-- sampleFMapOpt members_and_proposals ;;
  p <-- validate_addr member ;;
  pid <-- elems_opt pids ;;
  call caddr member p (vote pid).

(* Returns a mapping to proposals which have been discussed long enough, according to the
   current rules in the given congress' state *)
Definition finishable_proposals (state : Congress_Buggy.State)
                                (current_slot : nat)
                                : FMap ProposalId Proposal :=
  let pids_map_filtered := filter_FMap (fun '(_, proposal) =>
    proposal.(proposed_in) + state.(state_rules).(debating_period_in_blocks) <=? current_slot
  ) state.(proposals) in
  if 0 <? FMap.size pids_map_filtered
  then pids_map_filtered
  else FMap.empty.

Definition lc_contract_members_and_proposals_new_voters (state : Congress_Buggy.State)
                                                        : (FMap Address (list ProposalId)) :=
    let candidate_members := (map fst o FMap.elements) (members state) in
    let proposals_pairs := FMap.elements (proposals state) in
    if (0 <? length candidate_members) && (0 <? length proposals_pairs)
    then
      let voters_to_proposals : FMap Address (list ProposalId) :=
        List.fold_left (fun acc m =>
        let unvoted_proposals : list (ProposalId * Proposal) :=
          List.filter (fun p => match FMap.find m (votes (snd p)) with
                                | Some _ => false
                                | None => true
                                end) proposals_pairs in
        match List.map fst unvoted_proposals with
        | [] => acc
        | _ as ps => FMap.add m ps acc
        end
      ) candidate_members FMap.empty in
      voters_to_proposals
    else FMap.empty.

Definition lc_contract_members_and_proposals_with_votes (state : Congress_Buggy.State)
                                                        : FMap Address (list ProposalId) :=
    let members : list Address := (map fst o FMap.elements) (members state) in
    let proposals_map : FMap nat Proposal :=
      filter_FMap (fun p => 0 =? (FMap.size (votes (snd p)))) (proposals state) in
    if (0 <? length members) && (0 =? (FMap.size proposals_map))
    then (
      let propIds : list ProposalId := (map fst o FMap.elements) proposals_map in
      fold_left (fun acc m => FMap.add m propIds acc) members FMap.empty
    )
    else FMap.empty.

Fixpoint GCongressAction (env : Environment)
                         (fuel : nat)
                         (caddr : Address)
                         : GOpt Action :=
  let call contract_addr caller_addr caller_addr_is_user msg :=
    amount <- match env.(env_account_balances) caller_addr with
              | 0%Z => returnGen 0%Z
              | caller_balance => choose (0%Z, caller_balance)
              end ;;
    returnGenSome (build_act caller_addr caller_addr
      (congress_action_to_chain_action (cact_call contract_addr amount (serializeMsg msg)))) in
  congress_state <-- returnGen (get_contract_state Congress_Buggy.State env caddr) ;;
  let members := (map fst o FMap.elements) congress_state.(members) in
  let owner := congress_state.(owner) in
  match fuel with
  | 0 =>
    backtrack [
      (* transfer_ownership *)
      (1, members <-- elems_opt (congressContractsMembers_nonowners congress_state) ;;
          new_owner <-- (try_gNewOwner congress_state owner caddr) ;;
          p <-- validate_addr owner ;;
          call caddr owner p (transfer_ownership new_owner)
      ) ;
      (* change_rules *)
      (1, rules <- gRulesSized 4 ;;
          p <-- validate_addr owner ;;
          call caddr owner p (change_rules rules)
      ) ;
      (* add_member *)
      (2, addr <-- returnGen (try_newCongressMember congress_state caddr 10) ;;
          p <-- validate_addr owner ;;
          call caddr owner p (add_member addr)
      ) ;
      (* remove_member *)
      (1, member <-- elems_opt members ;;
          p <-- validate_addr owner ;;
          call caddr owner p (remove_member member)
      ) ;
      (* vote_for_proposal *)
      (* Requirements:
         - contract with a proposal and members must exist
         - only members which have not already voted can vote again *)
      (2, vote_proposal caddr (lc_contract_members_and_proposals_new_voters congress_state)
                        call vote_for_proposal ) ;
      (* vote_against_proposal *)
      (2, vote_proposal caddr (lc_contract_members_and_proposals_new_voters congress_state)
                        call vote_against_proposal ) ;
      (* retract_vote *)
      (2, vote_proposal caddr (lc_contract_members_and_proposals_with_votes congress_state)
                        call retract_vote) ;
      (* finish_proposal *)
      (* Requirements:
         - only contract owner can finish proposals
         - the debating period must have passed *)
      (2, '(pid, _) <-- sampleFMapOpt (finishable_proposals congress_state env.(current_slot)) ;;
          p <-- validate_addr owner ;;
          call caddr owner p (finish_proposal pid)
      )
    ]
  | S fuel' => backtrack [
    (3, GCongressAction env fuel' caddr) ;
    (* add_proposal *)
    (1,
      (* recurse. Msg is converted to a SerializedType using 'serialize' *)
      (* This makes it possible to create proposals about proposals about proposals etc... *)
      (* Note: currently we don't support having multiple actions in a proposal *)
      (* Note: the way we recurse may be too restrictive - we fix a caddr, which may cause gCongressMember
               to return None even though it could have succeeded for another caddr.
               Maybe this is not a big issue, though. *)
      act <-- GCongressAction env fuel' caddr ;;
      let caller_addr := act.(act_from) in
      match act.(act_body) with
      | act_call caddr amount msg =>
        member <-- elems_opt members ;;
        let ca := cact_call caddr amount msg in
        p <-- validate_addr member ;;
        call caddr member p (create_proposal [ca])
      | _ => returnGenSome act
      end)
  ]
  end.
