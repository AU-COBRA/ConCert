(* In this file we implement a Congress and prove it correct up to a
specification. The Congress is a simplified version of the DAO in
which members vote on proposals. We implement the contract in Gallina
and then show that it does not send out more transactions than
expected from the number of created proposals. *)

From Coq Require Import ZArith.
From Coq Require Import Morphisms.
From Coq Require Import Psatz.
From Coq Require Import Permutation.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import Serializable.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Containers.
From SmartContracts Require Import Automation.
From SmartContracts Require Import Extras.
From SmartContracts Require Import ChainedList.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.

Import ListNotations.
Import RecordSetNotations.

Section Congress.
Context {BaseTypes : ChainBase}.

Local Open Scope Z.
Set Primitive Projections.

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

Definition deserialize_rules (v : SerializedValue) : option Rules :=
  do '(a, b, c) <- deserialize v;
  Some (build_rules a b c).

Global Program Instance rules_serializable : Serializable Rules :=
  {| serialize r := let (a, b, c) := r in serialize (a, b, c);
     (* Why does
     deserialize v :=
       do '((a, b), c) <- deserialize v;
       Some (build_rules a b c); |}.
       not work here? *)
     deserialize := deserialize_rules; |}.
Next Obligation.
  intros x. unfold deserialize_rules.
  rewrite deserialize_serialize.
  reflexivity.
Qed.

Global Program Instance setup_serializable : Serializable Setup :=
  {| serialize s := serialize s.(setup_rules);
     deserialize or :=
       do rules <- deserialize or;
       Some (build_setup rules); |}.
Next Obligation.
  intros x.
  cbn.
  rewrite deserialize_serialize.
  reflexivity.
Qed.

Definition deserialize_congress_action (v : SerializedValue) : option CongressAction :=
  do val <- deserialize v;
  Some (match val with
  | inl (to, amount) => cact_transfer to amount
  | inr (to, amount, msg) => cact_call to amount msg
  end).

Global Program Instance congress_action_serializable : Serializable CongressAction :=
  {| serialize ca :=
       serialize
         match ca with
         | cact_transfer to amount => inl (to, amount)
         | cact_call to amount msg => inr (to, amount, msg)
         end;
     deserialize := deserialize_congress_action; |}.
Next Obligation.
  intros ca.
  unfold deserialize_congress_action.
  rewrite deserialize_serialize.
  destruct ca; reflexivity.
Qed.

Definition deserialize_proposal (v : SerializedValue) : option Proposal :=
  do '(a, b, c, d) <- deserialize v;
  Some (build_proposal a b c d).

Global Program Instance proposal_serializable : Serializable Proposal :=
  {| serialize p :=
       let (a, b, c, d) := p in
       serialize (a, b, c, d);
     deserialize := deserialize_proposal;
  |}.
Next Obligation.
  intros p.
  unfold deserialize_proposal.
  rewrite deserialize_serialize.
  destruct p; reflexivity.
Qed.

Definition serialize_msg (m : Msg) : SerializedValue :=
  serialize
    match m with
    | transfer_ownership a => (0, serialize a)
    | change_rules r => (1, serialize r)
    | add_member a => (2, serialize a)
    | remove_member a => (3, serialize a)
    | create_proposal l => (4, serialize l)
    | vote_for_proposal pid => (5, serialize pid)
    | vote_against_proposal pid => (6, serialize pid)
    | retract_vote pid => (7, serialize pid)
    | finish_proposal pid => (8, serialize pid)
    end.

Definition deserialize_msg (v : SerializedValue) : option Msg :=
  do '(tag, v) <- deserialize v;
  match tag with
  | 0 => option_map transfer_ownership (deserialize v)
  | 1 => option_map change_rules (deserialize v)
  | 2 => option_map add_member (deserialize v)
  | 3 => option_map remove_member (deserialize v)
  | 4 => option_map create_proposal (deserialize v)
  | 5 => option_map vote_for_proposal (deserialize v)
  | 6 => option_map vote_against_proposal (deserialize v)
  | 7 => option_map retract_vote (deserialize v)
  | 8 => option_map finish_proposal (deserialize v)
  | _ => None
  end.

Global Program Instance msg_serializable : Serializable Msg :=
  {| serialize := serialize_msg; deserialize := deserialize_msg; |}.
Next Obligation.
  intros msg.
  unfold serialize_msg, deserialize_msg.
  destruct msg; repeat (cbn; rewrite deserialize_serialize); reflexivity.
Qed.

Definition serialize_state (s : State) : SerializedValue :=
  let (a, b, c, d, e) := s in
  serialize (a, b, c, d, e).

Definition deserialize_state (v : SerializedValue) : option State :=
  do '(a, b, c, d, e) <- deserialize v;
  Some (build_state a b c d e).

Global Program Instance state_serializable : Serializable State :=
  {| serialize := serialize_state; deserialize := deserialize_state; |}.
Next Obligation.
  unfold serialize_state, deserialize_state.
  destruct x; repeat (cbn; rewrite deserialize_serialize); reflexivity.
Qed.

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

  | _, _, _ =>
        None

  end.

Ltac solve_contract_proper :=
  repeat
    match goal with
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

Definition num_acts_created_in_proposals (txs : list Tx) :=
  let count tx :=
      match tx_body tx with
      | tx_call (Some msg) =>
        match deserialize msg with
        | Some (create_proposal acts) => length acts
        | _ => 0
        end
      | _ => 0
      end in
  sumnat count txs.

Definition num_cacts_in_state state :=
  sumnat (fun '(k, v) => length (actions v)) (FMap.elements (proposals state)).

Definition num_outgoing_acts l address :=
  let extract a :=
      if address_eqb (act_from a) address
      then 1
      else 0 in
  sumnat extract l.

Lemma num_outgoing_acts_app q1 q2 address :
  num_outgoing_acts (q1 ++ q2) address =
  num_outgoing_acts q1 address +
  num_outgoing_acts q2 address.
Proof.
  unfold num_outgoing_acts.
  now rewrite sumnat_app.
Qed.

Lemma num_outgoing_acts_block l contract :
  address_is_contract contract = true ->
  Forall act_is_from_account l ->
  num_outgoing_acts l contract = 0.
Proof.
  intros is_contract all.
  induction all; auto.
  cbn in *.
  destruct_address_eq; try congruence.
  fold (num_outgoing_acts l contract); auto.
Qed.

Lemma num_outgoing_acts_call l contract :
  num_outgoing_acts (map (build_act contract) l) contract = length l.
Proof.
  induction l; auto.
  cbn.
  destruct_address_eq; auto; congruence.
Qed.

Lemma num_outgoing_acts_call_ne to l contract :
  to <> contract ->
  num_outgoing_acts (map (build_act to) l) contract = 0.
Proof.
  intros neq.
  induction l; auto.
  cbn.
  destruct_address_eq; auto; congruence.
Qed.

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
    rewrite <- (FMap.add_remove _ (next_proposal_id state) new_proposal).
    Hint Resolve FMap.find_remove : core.
    rewrite <- (FMap.add_id _ _ _ find) at 2.
    rewrite <- (FMap.add_remove _ (next_proposal_id state) proposal).
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
  rewrite <- (FMap.add_id (proposals state) pid p) at 2; auto.
  rewrite <- (FMap.add_remove _ pid p).
  rewrite <- (FMap.add_remove _ pid new_proposal).
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
  rewrite <- (FMap.add_id (proposals state) pid p) at 2; auto.
  rewrite <- (FMap.add_remove _ pid p).
  rewrite <- (FMap.add_remove _ pid new_proposal).
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
  rewrite <- (FMap.add_id (proposals state) pid proposal) at 2; auto.
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
  msg <> None /\
  num_cacts_in_state new_state + length resp_acts <=
  num_cacts_in_state state +
  match msg with
  | Some (create_proposal ls) => length ls
  | _ => 0
  end.
Proof.
  intros receive.
  destruct msg as [msg|]; cbn in *; try congruence.
  destruct msg; cbn in *; try congruence.
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
    split; auto.
    apply add_proposal_cacts.
  - (* vote_for_proposal *)
    destruct (FMap.mem _ _); try congruence.
    destruct (vote_on_proposal _ _ _ _) eqn:vote; cbn in *; try congruence.
    inversion receive; subst.
    erewrite vote_on_proposal_cacts_preserved; eauto.
  - (* vote_against_proposal *)
    destruct (FMap.mem _ _); try congruence.
    destruct (vote_on_proposal _ _ _ _) eqn:vote; cbn in *; try congruence.
    inversion receive; subst.
    erewrite vote_on_proposal_cacts_preserved; eauto.
  - (* retract_vote *)
    destruct (FMap.mem _ _); try congruence.
    destruct (do_retract_vote _ _ _) eqn:retract; cbn in *; try congruence.
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
Qed.

Lemma undeployed_contract_no_out_queue_count contract (state : ChainState) :
  reachable state ->
  address_is_contract contract = true ->
  env_contracts state contract = None ->
  num_outgoing_acts (chain_state_queue state) contract = 0.
Proof.
  intros [trace] is_contract undeployed.
  pose proof undeployed_contract_no_out_queue as all; specialize_hypotheses.
  Hint Unfold reachable : core.
  induction all; auto.
  cbn.
  match goal with
  | [H: _ |- _] => now rewrite H; auto
  end.
Qed.

Lemma undeployed_contract_not_from_self contract (state : ChainState) act acts :
  reachable state ->
  address_is_contract contract = true ->
  env_contracts state contract = None ->
  chain_state_queue state = act :: acts ->
  act_from act <> contract.
Proof.
  intros trace is_contract no_contract_prev queue_eq.
  pose proof (
         undeployed_contract_no_out_queue
           _ _ trace is_contract no_contract_prev) as all.
  rewrite queue_eq in *.
  inversion all.
  destruct_address_eq; congruence.
Qed.

Arguments num_acts_created_in_proposals : simpl never.
Arguments num_cacts_in_state : simpl never.
Arguments num_cacts_in_state : simpl never.
Arguments num_outgoing_acts !l.

Local Ltac solve_single :=
  solve [
      repeat (progress subst; cbn in *; auto);
      unfold add_balance, num_cacts_in_state, num_acts_created_in_proposals, num_outgoing_acts;
      cbn;
      unfold set_chain_contract_state;
      cbn;
      try rewrite address_eq_refl;
      repeat rewrite address_eq_ne by auto;
      cbn;
      destruct_address_eq; congruence].

Local Ltac simpl_exp_invariant exp :=
  match exp with
  | context G[length (filter ?f (?hd :: ?tl))] =>
    let newexp := context G[S (length (filter f tl))] in
    replace exp with newexp by solve_single
  | context G[filter ?f (?hd :: ?tl)] =>
    let newexp := context G[filter f tl] in
    replace exp with newexp by solve_single
  | context G[add_new_block_to_env _ ?env] =>
    let newexp := context G[env] in
    replace exp with newexp by solve_single
  | context G[transfer_balance _ _ _ ?env] =>
    let newexp := context G[env] in
    replace exp with newexp by solve_single
  | context G[set_contract_state _ _ ?env] =>
    let newexp := context G[env] in
    replace exp with newexp by solve_single
  | context G[add_contract _ _ ?env] =>
    let newexp := context G[env] in
    replace exp with newexp by solve_single
  | context G[num_outgoing_acts (?a ++ ?b) _] =>
    rewrite num_outgoing_acts_app
  end.

(* This tactic performs various simplifications on the goal involving
expressions establishing the invariant. For instance, it tries to rewrite
num_cacts_in_state (add_tx tx env) -> num_cacts_in_state env using some
common tactics. *)
Local Ltac simpl_goal_invariant :=
  repeat
    match goal with
    | [|- context[num_cacts_in_state ?env ?addr]] =>
      simpl_exp_invariant constr:(num_cacts_in_state env addr)
    | [|- context[length ?txs]] =>
      simpl_exp_invariant constr:(length txs)
    | [|- context[num_outgoing_acts ?q ?addr]] =>
      simpl_exp_invariant constr:(num_outgoing_acts q addr)
    | [|- context[num_acts_created_in_proposals ?txs]] =>
      simpl_exp_invariant constr:(num_acts_created_in_proposals txs)
    end.

Local Ltac simpl_hyp_invariant :=
  repeat
    match goal with
    | [IH: context[num_outgoing_acts (?act :: ?acts) ?addr] |- _] =>
      replace (num_outgoing_acts (act :: acts) addr)
        with (S (num_outgoing_acts acts addr))
        in IH
        by solve_single
    | [IH: context[num_outgoing_acts (?act :: ?acts) ?addr] |- _] =>
      replace (num_outgoing_acts (act :: acts) addr)
        with (num_outgoing_acts acts addr)
        in IH
        by solve_single
    end.

Lemma contract_state_from_weak {A} `{Serializable A} env addr state state_strong :
  env_contract_states env addr = Some state ->
  deserialize state = Some state_strong ->
  contract_state env addr = Some state_strong.
Proof.
  intros weak deser.
  unfold contract_state.
  now rewrite weak.
Qed.

Theorem congress_txs_well_behaved bstate contract (trace : ChainTrace empty_state bstate) :
  env_contracts bstate contract = Some (Congress.contract : WeakContract) ->
  exists cstate,
    contract_state bstate contract = Some cstate /\
    num_cacts_in_state cstate +
    length (outgoing_txs trace contract) +
    num_outgoing_acts (chain_state_queue bstate) contract <=
    num_acts_created_in_proposals (incoming_txs trace contract).
Proof.
  intros congress_deployed.
  Hint Resolve contract_addr_format : core.
  assert (address_is_contract contract = true) as addr_format by eauto.
  destruct (deployed_contract_state_typed congress_deployed ltac:(auto))
    as [cstate state_eq].
  exists cstate; split; auto.
  revert cstate state_eq.
  (* Contract cannot have been deployed in empty trace so we solve that immediately. *)
  remember empty_state.
  induction trace as [|? ? ? steps IH step]; intros; subst; try solve_by_inversion.
  destruct_chain_step.
  - (* New block added, does not change any of the values *)
    (* so basically just use IH directly. *)
    rewrite queue_prev in *.
    rewrite_environment_equiv.
    cbn in *.
    rewrite num_outgoing_acts_block; auto.
  - (* Step *)
    unfold outgoing_txs, incoming_txs in *.
    cbn [trace_txs].
    rewrite queue_prev, queue_new in *.
    remember (chain_state_env prev).
    destruct_action_eval; subst; cbn [eval_tx].
    + (* Transfer step: cannot be to contract, but can come from contract. *)
      rewrite_environment_equiv.
      specialize_hypotheses.
      (* Handle from contract and not from contract separately. *)
      destruct (address_eqb_spec from contract);
        simpl_goal_invariant;
        simpl_hyp_invariant;
        cbn; lia.
    + (* Deployment. Can be deployment of contract, in which case we need to *)
      (* establish invariant. *)
      rewrite_environment_equiv.
      unfold contract_state in state_eq.
      cbn in state_eq, congress_deployed.
      destruct (address_eqb_spec contract to) as [<-|]; cycle 1.
      * (* Deployment of different contract. Holds both if from us or not. *)
        specialize_hypotheses.
        destruct (address_eqb_spec from contract);
          simpl_goal_invariant;
          simpl_hyp_invariant;
          cbn; lia.
      * (* This is deployment of this contract *)
        replace wc with (Congress.contract : WeakContract) in * by congruence.
        destruct (wc_init_strong ltac:(eassumption)) as [? [result [? [<- ?]]]].
        cbn in state_eq.
        rewrite deserialize_serialize in state_eq.
        replace result with cstate in * by auto with congruence.
        (* State starts at 0 *)
        erewrite num_cacts_in_state_deployment by eassumption.
        (* Outgoing actions in queue is 0 *)
        Hint Resolve undeployed_contract_no_out_queue_count : core.
        assert (num_outgoing_acts (chain_state_queue prev) contract = 0)
          as out_acts by auto.
        rewrite queue_prev in out_acts.
        remember (build_act from _) as act.
        assert (act_from act <> contract)
          by (eapply undeployed_contract_not_from_self; eauto).
        simpl_hyp_invariant.
        simpl_goal_invariant.
        (* Outgoing transactions is 0 *)
        fold (outgoing_txs steps contract).
        rewrite undeployed_contract_no_out_txs; auto.
        cbn. lia.
    + (* Call. *)
      rewrite_environment_equiv.
      unfold contract_state in state_eq.
      cbn in state_eq.
      destruct (address_eqb_spec contract to) as [<-|]; cycle 1.
      * (* Not to contract. Essentially same thing as transfer case above. *)
        simpl_goal_invariant.
        specialize_hypotheses.
        rewrite num_outgoing_acts_call_ne; auto.
        destruct (address_eqb_spec contract from);
          simpl_goal_invariant;
          simpl_hyp_invariant;
          cbn; lia.
      * (* To contract. This will run code. *)
        cbn in congress_deployed, state_eq.
        replace wc with (Congress.contract : WeakContract) in * by congruence.
        destruct (wc_receive_strong ltac:(eassumption))
          as [prev_state_strong [msg_strong [resp_state_strong [? [msg_eq [<- receive]]]]]].
        Hint Resolve contract_state_from_weak : core.
        specialize (IH ltac:(auto) ltac:(auto) prev_state_strong ltac:(eauto)).
        rewrite deserialize_serialize in state_eq.
        replace resp_state_strong with cstate in * by congruence.
        destruct (receive_state_well_behaved _ _ _ _ _ _ ltac:(eassumption)).
        simpl_goal_invariant.
        cbn.
        rewrite num_outgoing_acts_call.
        rewrite address_eq_refl.
        unfold num_acts_created_in_proposals in IH |- *.
        cbn.
        fold (incoming_txs steps contract) in *.
        fold (outgoing_txs steps contract) in *.
        fold (num_acts_created_in_proposals (incoming_txs steps contract)) in *.
        destruct msg_strong; try congruence.
        destruct msg; [|cbn in *; congruence].
        cbn in msg_eq.
        rewrite msg_eq.
        destruct (address_eqb_spec from contract);
          simpl_hyp_invariant;
          cbn; lia.
  - (* Permute queue *)
    unfold num_outgoing_acts.
    cbn.
    rewrite <- perm, prev_next in *; auto.
Qed.

Corollary congress_txs_after_block
          {ChainBuilder : ChainBuilderType}
          prev new header acts :
  builder_add_block prev header acts = Some new ->
  forall addr,
    env_contracts new addr = Some (Congress.contract : WeakContract) ->
    length (outgoing_txs (builder_trace new) addr) <=
    num_acts_created_in_proposals (incoming_txs (builder_trace new) addr).
Proof.
  intros add_block contract congress_at_addr.
  pose proof (congress_txs_well_behaved _ _ (builder_trace new) congress_at_addr).
  destruct H as [? [? ?]].
  cbn in *.
  lia.
Qed.
End Theories.
End Congress.
