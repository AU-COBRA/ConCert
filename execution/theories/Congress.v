(* In this file we implement a Congress and prove it correct up to a
specification. The Congress is a simplified version of the DAO in
which members vote on proposals. We implement the contract in Gallina
and then show that it does not send out more transactions than
expected from the number of created proposals. *)

From Coq Require Import ZArith.
From Coq Require Import Morphisms.
From Coq Require Import Psatz.
From Coq Require Import Permutation.
Require Import Blockchain.
Require Import Serializable.
Require Import Monads.
Require Import Containers.
Require Import Automation.
Require Import Extras.
Require Import ChainedList.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.

Import ListNotations.
Import RecordSetNotations.

Section Congress.
Context {BaseTypes : ChainBase}.

Local Open Scope Z.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Definition ProposalId := nat.

Inductive CongressAction :=
  | cact_transfer (to : Address) (amount : Amount)
  | cact_call (to : Address) (amount : Amount) (msg : SerializedValue).

Record Proposal :=
  build_proposal {
    actions : list CongressAction;
    votes : FMap Address Z;
    vote_result : Z;
    proposed_in : nat;
  }.

Instance proposal_settable : Settable _ :=
  settable! build_proposal <actions; votes; vote_result; proposed_in>.

Record Rules :=
  build_rules {
    min_vote_count_permille : Z;
    margin_needed_permille : Z;
    debating_period_in_blocks : nat;
  }.

Record Setup :=
  build_setup {
    setup_rules : Rules;
  }.

Inductive Msg :=
  | transfer_ownership : Address -> Msg
  | change_rules : Rules -> Msg
  | add_member : Address -> Msg
  | remove_member : Address -> Msg
  | create_proposal : list CongressAction -> Msg
  | vote_for_proposal : ProposalId -> Msg
  | vote_against_proposal : ProposalId -> Msg
  | retract_vote : ProposalId -> Msg
  | finish_proposal : ProposalId -> Msg.

Record State :=
  build_state {
    owner : Address;
    state_rules : Rules;
    proposals : FMap nat Proposal;
    next_proposal_id : ProposalId;
    members : FMap Address unit;
  }.

Instance state_settable : Settable _ :=
  settable! build_state <owner; state_rules; proposals; next_proposal_id; members>.

Section Serialization.

Global Instance rules_serializable : Serializable Rules :=
  Derive Serializable Rules_rect <build_rules>.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance congress_action_serializable : Serializable CongressAction :=
  Derive Serializable CongressAction_rect <cact_transfer, cact_call>.

Global Instance proposal_serializable : Serializable Proposal :=
  Derive Serializable Proposal_rect <build_proposal>.

Global Instance msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <transfer_ownership, change_rules, add_member, remove_member,
                                create_proposal, vote_for_proposal, vote_against_proposal,
                                retract_vote, finish_proposal>.

Global Instance state_serializable : Serializable State :=
  Derive Serializable State_rect <build_state>.

End Serialization.

Definition validate_rules (rules : Rules) : bool :=
    (rules.(min_vote_count_permille) >=? 0)
        && (rules.(min_vote_count_permille) <=? 1000)
        && (rules.(margin_needed_permille) >=? 0)
        && (rules.(margin_needed_permille) <=? 1000)
        && (0 <=? rules.(debating_period_in_blocks))%nat.

Definition init
           (chain : Chain)
           (ctx : ContractCallContext)
           (setup : Setup) : option State :=
  if validate_rules setup.(setup_rules) then
    Some {| owner := ctx.(ctx_from);
            state_rules := setup.(setup_rules);
            proposals := FMap.empty;
            next_proposal_id := 1%nat;
            members := FMap.empty |}
  else
    None.

Definition add_proposal (actions : list CongressAction) (chain : Chain) (state : State) : State :=
  let id := state.(next_proposal_id) in
  let slot_num := chain.(current_slot) in
  let proposal := {| actions := actions;
                     votes := FMap.empty;
                     vote_result := 0;
                     proposed_in := slot_num |} in
  state<|proposals ::= FMap.add id proposal|>
       <|next_proposal_id ::= S|>.

Definition vote_on_proposal
           (voter : Address)
           (pid : ProposalId)
           (vote : Z)
           (state : State)
  : option State :=
  do proposal <- FMap.find pid state.(proposals);
  let old_vote := match FMap.find voter proposal.(votes) with
                 | Some old => old
                 | None => 0
                 end in
  let new_votes := FMap.add voter vote proposal.(votes) in
  let new_vote_result := proposal.(vote_result) - old_vote + vote in
  let new_proposal :=
      proposal<|votes := new_votes|>
              <|vote_result := new_vote_result|> in
  Some (state<|proposals ::= FMap.add pid new_proposal|>).

Definition do_retract_vote
           (voter : Address)
           (pid : ProposalId)
           (state : State)
  : option State :=
  do proposal <- FMap.find pid state.(proposals);
  do old_vote <- FMap.find voter proposal.(votes);
  let new_votes := FMap.remove voter proposal.(votes) in
  let new_vote_result := proposal.(vote_result) - old_vote in
  let new_proposal :=
      proposal<|votes := new_votes|>
              <|vote_result := new_vote_result|> in
  Some (state<|proposals ::= FMap.add pid new_proposal|>).

Definition congress_action_to_chain_action (act : CongressAction) : ActionBody :=
  match act with
  | cact_transfer to amt => act_transfer to amt
  | cact_call to amt msg => act_call to amt msg
  end.

Definition proposal_passed (proposal : Proposal) (state : State) : bool :=
  let rules := state.(state_rules) in
  let total_votes_for_proposal := Z.of_nat (FMap.size proposal.(votes)) in
  let total_members := Z.of_nat (FMap.size state.(members)) in
  let aye_votes := (proposal.(vote_result) + total_votes_for_proposal) / 2 in
  let vote_count_permille := total_votes_for_proposal * 1000 / total_members in
  let aye_permille := aye_votes * 1000 / total_votes_for_proposal in
  let enough_voters := vote_count_permille >=? rules.(min_vote_count_permille) in
  let enough_ayes := aye_permille >=? rules.(margin_needed_permille) in
  enough_voters && enough_ayes.

Definition do_finish_proposal
           (pid : ProposalId)
           (state : State)
           (chain : Chain)
  : option (State * list ActionBody) :=
  do proposal <- FMap.find pid state.(proposals);
  let rules := state.(state_rules) in
  let debate_end := (proposal.(proposed_in) + rules.(debating_period_in_blocks))%nat in
  let cur_slot := chain.(current_slot) in
  if (cur_slot <? debate_end)%nat then
    None
  else
    let response_acts :=
        if proposal_passed proposal state
        then proposal.(actions)
        else [] in
    let response_chain_acts := map congress_action_to_chain_action response_acts in
    let new_state := state<|proposals ::= FMap.remove pid|> in
    Some (new_state, response_chain_acts).

Definition receive
           (chain : Chain)
           (ctx : ContractCallContext)
           (state : State)
           (maybe_msg : option Msg)
  : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let is_from_owner := (sender =? state.(owner))%address in
  let is_from_member := FMap.mem sender state.(members) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
  match maybe_msg, is_from_owner, is_from_member with
  | Some (transfer_ownership new_owner), true, _ =>
    Some (state<|owner := new_owner|>, [])

  | Some (change_rules new_rules), true, _ =>
    if validate_rules new_rules then
      Some (state<|state_rules := new_rules|>, [])
    else
      None

  | Some (add_member new_member), true, _ =>
    Some (state<|members ::= FMap.add new_member tt|>, [])

  | Some (remove_member old_member), true, _ =>
    Some (state<|members ::= FMap.remove old_member|>, [])

  | Some (create_proposal actions), _, true =>
    Some (add_proposal actions chain state, [])

  | Some (vote_for_proposal pid), _, true =>
    without_actions (vote_on_proposal sender pid 1 state)

  | Some (vote_against_proposal pid), _, true =>
    without_actions (vote_on_proposal sender pid (-1) state)

  | Some (retract_vote pid), _, true =>
    without_actions (do_retract_vote sender pid state)

  | Some (finish_proposal pid), _, _ =>
    do_finish_proposal pid state chain

  (* Always allow people to donate money for the Congress to spend *)
  | None, _, _ => Some (state, [])

  | _, _, _ =>
        None

  end.

Ltac solve_contract_proper :=
  repeat
    match goal with
    | [|- @bind _ ?m _ _ _ _ = @bind _ ?m _ _ _ _] => unfold bind, m
    | [|- ?x _  = ?x _] => unfold x
    | [|- ?x _ _ = ?x _ _] => unfold x
    | [|- ?x _ _ _ = ?x _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ _ = ?x _ _ _ _ _] => unfold x
    | [|- Some _ = Some _] => f_equal
    | [|- pair _ _ = pair _ _] => f_equal
    | [|- (if ?x then _ else _) = (if ?x then _ else _)] => destruct x
    | [|- match ?x with | _ => _ end = match ?x with | _ => _ end ] => destruct x
    | [H: ChainEquiv _ _ |- _] => rewrite H in *
    | _ => subst; auto
    end.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) init.
Proof. repeat intro; solve_contract_proper. Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive.
Proof. repeat intro; solve_contract_proper. Qed.

Definition contract : Contract Setup Msg State :=
  build_contract init init_proper receive receive_proper.
Section Theories.
Local Open Scope nat.

(* The rules stored in the blockchain's state are always valid *)
Lemma rules_valid bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (Congress.contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate /\
    validate_rules cstate.(state_rules) = true.
Proof.
  assert (valid_after_recv:
            forall chain ctx prev_state msg new_state new_acts,
              receive chain ctx prev_state msg = Some (new_state, new_acts) ->
              validate_rules (state_rules prev_state) = true ->
              validate_rules (state_rules new_state) = true).
  {
    intros ? ? ? ? ? ? receive valid_prev.
    destruct msg as [[]|]; cbn in *;
      try solve [
            repeat
              match goal with
              | [H: Some ?x = Some ?y |- _] => inversion_clear H; auto
              | _ => try congruence; let H := fresh in destruct_match eqn:H in *
              end].
    + destruct_match in receive; try congruence.
      unfold vote_on_proposal in receive.
      destruct (FMap.find _ _); cbn in *; try congruence.
      now inversion_clear receive.
    + destruct_match in receive; try congruence.
      unfold vote_on_proposal in receive.
      destruct (FMap.find _ _); cbn in *; try congruence.
      now inversion_clear receive.
    + destruct_match in receive; try congruence.
      unfold do_retract_vote in receive.
      destruct (FMap.find _ _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      now inversion_clear receive.
    + now inversion receive; subst.
  }

  contract_induction; intros; cbn in *; auto.
  - unfold Congress.init in init_some.
    destruct_match eqn:validate_succeeds in init_some; try congruence.
    now inversion_clear init_some.
  - eauto.
  - eauto.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (CallFacts := fun _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    unset_all; subst.
    destruct step; auto.
    destruct a; auto.
Qed.

Definition num_acts_created_in_proposals (calls : list (ContractCallInfo Congress.Msg)) :=
  let count call :=
      match call_msg call with
      | Some (create_proposal acts) => length acts
      | _ => 0
      end in
  sumnat count calls.

Definition num_cacts_in_state state :=
  sumnat (fun '(k, v) => length (actions v)) (FMap.elements (proposals state)).

Lemma num_cacts_in_state_deployment chain ctx setup state :
  init chain ctx setup = Some state ->
  num_cacts_in_state state = 0.
Proof.
  intros init.
  unfold Congress.init in init.
  destruct (validate_rules _); try congruence.
  now inversion init.
Qed.

Ltac remember_new_proposal :=
  match goal with
  | [|- context[FMap.add _ ?p]] => remember p as new_proposal
  end.

Lemma add_proposal_cacts cacts chain state :
  num_cacts_in_state (add_proposal cacts chain state) <=
  num_cacts_in_state state + length cacts.
Proof.
  unfold add_proposal, num_cacts_in_state.
  cbn.
  destruct (FMap.find (next_proposal_id state) (proposals state)) as [proposal|] eqn:find.
  - remember_new_proposal.
    rewrite <- (FMap.add_remove (next_proposal_id state) new_proposal).
    Hint Resolve FMap.find_remove : core.
    rewrite <- (FMap.add_id _ _ _ find) at 2.
    rewrite <- (FMap.add_remove (next_proposal_id state) proposal).
    repeat rewrite FMap.elements_add; auto.
    subst.
    cbn.
    lia.
  - rewrite FMap.elements_add; auto.
    cbn.
    lia.
Qed.

Lemma vote_on_proposal_cacts_preserved addr pid vote_val state new_state :
  vote_on_proposal addr pid vote_val state = Some new_state ->
  num_cacts_in_state new_state = num_cacts_in_state state.
Proof.
  intros vote.
  unfold vote_on_proposal in vote.
  destruct (FMap.find _ _) eqn:found; cbn in *; try congruence.
  inversion vote.
  unfold num_cacts_in_state.
  cbn.
  remember_new_proposal.
  rewrite <- (FMap.add_id pid p (proposals state)) at 2; auto.
  rewrite <- (FMap.add_remove pid p).
  rewrite <- (FMap.add_remove pid new_proposal).
  repeat rewrite FMap.elements_add; try apply FMap.find_remove.
  subst; reflexivity.
Qed.

Lemma do_retract_vote_cacts_preserved addr pid state new_state :
  do_retract_vote addr pid state = Some new_state ->
  num_cacts_in_state new_state = num_cacts_in_state state.
Proof.
  intros retract.
  unfold do_retract_vote in retract.
  destruct (FMap.find _ _) eqn:found; cbn in *; try congruence.
  destruct (FMap.find addr _); cbn in *; try congruence.
  inversion retract.
  unfold num_cacts_in_state.
  cbn.
  remember_new_proposal.
  rewrite <- (FMap.add_id pid p (proposals state)) at 2; auto.
  rewrite <- (FMap.add_remove pid p).
  rewrite <- (FMap.add_remove pid new_proposal).
  Hint Resolve FMap.find_remove : core.
  repeat rewrite FMap.elements_add; auto.
  subst; reflexivity.
Qed.

Lemma remove_proposal_cacts pid state proposal :
  FMap.find pid (proposals state) = Some proposal ->
  num_cacts_in_state (state <|proposals ::= FMap.remove pid|>) +
  length (actions proposal) = num_cacts_in_state state.
Proof.
  intros find.
  unfold num_cacts_in_state.
  cbn.
  rewrite <- (FMap.add_id pid proposal (proposals state)) at 2; auto.
  rewrite <- FMap.add_remove.
  rewrite FMap.elements_add; auto.
  cbn.
  lia.
Qed.

(* The next lemma shows that when we send out transactions, the
state change will make up for number of outgoing actions queued. *)
Lemma receive_state_well_behaved
      chain ctx state msg new_state resp_acts :
  receive chain ctx state msg = Some (new_state, resp_acts) ->
  num_cacts_in_state new_state + length resp_acts <=
  num_cacts_in_state state +
  match msg with
  | Some (create_proposal ls) => length ls
  | _ => 0
  end.
Proof.
  intros receive.
  destruct msg as [[]|];
    cbn -[vote_on_proposal do_retract_vote do_finish_proposal] in *.
  - (* transfer_ownership *)
    destruct_address_eq; try congruence.
    inversion receive; auto.
  - (* change_rules *)
    destruct_address_eq; cbn in *; destruct (validate_rules r); inversion receive; auto.
  - (* add_member *)
    destruct_address_eq; cbn in *; inversion receive; auto.
  - (* remove_member *)
    destruct_address_eq; cbn in *; inversion receive; auto.
  - (* create_proposal *)
    destruct (FMap.mem _ _); inversion receive.
    cbn.
    rewrite <- plus_n_O.
    apply add_proposal_cacts.
  - (* vote_for_proposal *)
    destruct (FMap.mem _ _); try congruence.
    destruct (vote_on_proposal _ _ _ _) eqn:vote; cbn -[vote_on_proposal] in *; try congruence.
    inversion receive; subst.
    erewrite vote_on_proposal_cacts_preserved; eauto.
  - (* vote_against_proposal *)
    destruct (FMap.mem _ _); try congruence.
    destruct (vote_on_proposal _ _ _ _) eqn:vote; cbn -[vote_on_proposal] in *; try congruence.
    inversion receive; subst.
    erewrite vote_on_proposal_cacts_preserved; eauto.
  - (* retract_vote *)
    destruct (FMap.mem _ _); try congruence.
    destruct (do_retract_vote _ _ _) eqn:retract; cbn -[do_retract_vote] in *; try congruence.
    inversion receive; subst.
    erewrite do_retract_vote_cacts_preserved; eauto.
  - (* finish_proposal *)
    unfold do_finish_proposal in receive.
    destruct (FMap.find _ _) eqn:found; cbn in *; try congruence.
    match goal with
    | [H: (if ?a then _ else _) = Some _ |- _] => destruct a
    end; cbn in *; try congruence.
    inversion receive.
    rewrite <- (remove_proposal_cacts _ _ _ found), map_length.
    destruct (proposal_passed _ _); cbn.
    + (* I wonder why these asserts are necessary... *)
      assert (forall a b, a + b <= a + b + 0) by (intros; lia); auto.
    + assert (forall a b, a + 0 <= a + b + 0) by (intros; lia); auto.
  - inversion receive; subst; cbn; lia.
Qed.

Theorem congress_txs_well_behaved bstate caddr (trace : ChainTrace empty_state bstate) :
  env_contracts bstate caddr = Some (Congress.contract : WeakContract) ->
  exists (cstate : Congress.State) (inc_calls : list (ContractCallInfo Congress.Msg)),
    contract_state bstate caddr = Some cstate /\
    incoming_calls Msg trace caddr = Some inc_calls /\
    num_cacts_in_state cstate +
    length (outgoing_txs trace caddr) +
    length (outgoing_acts bstate caddr) <=
    num_acts_created_in_proposals inc_calls.
Proof.
  contract_induction; intros; cbn in *; auto; try lia.
  - erewrite num_cacts_in_state_deployment by eassumption.
    lia.
  - pose proof (receive_state_well_behaved _ _ _ _ _ _ receive_some) as fcorrect.
    fold (num_acts_created_in_proposals prev_inc_calls).
    rewrite app_length.
    lia.
  - pose proof (receive_state_well_behaved _ _ _ _ _ _ receive_some) as fcorrect.
    fold (num_acts_created_in_proposals prev_inc_calls).
    rewrite app_length.
    lia.
  - intros.
    now rewrite <- perm.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ => True).
    unset_all; subst.
    destruct step; auto.
    destruct a; auto.
Qed.

Corollary congress_txs_after_block
          {ChainBuilder : ChainBuilderType}
          prev new header acts :
  builder_add_block prev header acts = Some new ->
  forall caddr,
    env_contracts new caddr = Some (Congress.contract : WeakContract) ->
    exists inc_calls,
      incoming_calls Msg (builder_trace new) caddr = Some inc_calls /\
      length (outgoing_txs (builder_trace new) caddr) <=
      num_acts_created_in_proposals inc_calls.
Proof.
  intros add_block contract congress_at_addr.
  pose proof (congress_txs_well_behaved _ _ (builder_trace new) congress_at_addr)
       as general.
  destruct general as [? [inc_calls [? [? ?]]]].
  exists inc_calls.
  split; auto.
  cbn in *.
  lia.
Qed.
End Theories.
End Congress.
