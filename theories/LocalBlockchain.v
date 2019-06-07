From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import Morphisms.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Containers.
From SmartContracts Require Import Extras.
From SmartContracts Require Import Automation.
From SmartContracts Require Import BoundedN.
From SmartContracts Require Import Circulation.
From SmartContracts Require Import ChainedList.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
From Coq Require Import Psatz.
From stdpp Require countable.

Import RecordSetNotations.
Import ListNotations.

Section LocalBlockchain.
Local Open Scope bool.

Definition AddrSize : N := 2^128.
Definition ContractAddrBase : N := AddrSize / 2.

Global Instance LocalChainBase : ChainBase :=
  {| Address := BoundedN AddrSize;
     address_eqb := BoundedN.eqb;
     address_eqb_spec := BoundedN.eqb_spec;
     compute_block_reward n := 50%Z;
     address_is_contract a := (ContractAddrBase <=? BoundedN.to_N a)%N
  |}.

Record LocalChain :=
  build_local_chain {
    lc_header : BlockHeader;
    lc_account_balances : FMap Address Amount;
    lc_contract_state : FMap Address OakValue;
    lc_contracts : FMap Address WeakContract;
  }.

Instance local_chain_settable : Settable _ :=
  settable! build_local_chain
  <lc_header; lc_account_balances; lc_contract_state; lc_contracts>.

Definition lc_to_env (lc : LocalChain) : Environment :=
  {| env_chain :=
        {| block_header := lc_header lc;
           account_balance a := with_default 0%Z (FMap.find a (lc_account_balances lc));
           contract_state a := FMap.find a (lc_contract_state lc); |};
      env_contracts a := FMap.find a (lc_contracts lc); |}.

Global Coercion lc_to_env : LocalChain >-> Environment.

Section ExecuteActions.
  Local Open Scope Z.

  Definition add_balance (addr : Address) (amt : Amount) (lc : LocalChain) : LocalChain :=
    let update opt := Some (amt + with_default 0 opt) in
    let lc := lc<|lc_account_balances ::= FMap.partial_alter update addr|> in
    lc.

  Definition transfer_balance
            (from to : Address) (amount : Amount) (lc : LocalChain) : LocalChain :=
    add_balance to amount (add_balance from (-amount) lc).

  Definition get_new_contract_addr (lc : LocalChain) : option Address :=
    BoundedN.of_N (ContractAddrBase + N.of_nat (FMap.size (lc_contracts lc))).

  Definition add_contract
             (addr : Address)
             (wc : WeakContract)
             (lc : LocalChain) : LocalChain :=
    lc<|lc_contracts ::= FMap.add addr wc|>.

  Definition set_contract_state
             (addr : Address)
             (state : OakValue)
             (lc : LocalChain) : LocalChain :=
    lc<|lc_contract_state ::= FMap.add addr state|>.

  Definition send_or_call
             (from to : Address)
             (amount : Amount)
             (msg : option OakValue)
             (lc : LocalChain) : option (list Action * LocalChain) :=
    do if amount >? account_balance lc from then None else Some tt;
    match FMap.find to lc.(lc_contracts) with
    | None =>
      (* Fail if sending a message to address without contract *)
      do if address_is_contract to then None else Some tt;
      match msg with
        | None => Some ([], transfer_balance from to amount lc)
        | Some msg => None
      end
    | Some wc =>
      do state <- contract_state lc to;
      let lc := transfer_balance from to amount lc in
      let ctx := build_ctx from to amount in
      do '(new_state, new_actions) <- wc_receive wc  lc ctx state msg;
      let lc := set_contract_state to new_state lc in
      Some (map (build_act to) new_actions, lc)
    end.

  Definition deploy_contract
             (from : Address)
             (amount : Amount)
             (wc : WeakContract)
             (setup : OakValue)
             (lc : LocalChain)
    : option (list Action * LocalChain) :=
    do if amount >? account_balance lc from then None else Some tt;
    do contract_addr <- get_new_contract_addr lc;
    do match FMap.find contract_addr (lc_contracts lc) with
       | Some _ => None
       | None => Some tt
       end;
    let lc := transfer_balance from contract_addr amount lc in
    let ctx := build_ctx from contract_addr amount in
    do state <- wc_init wc lc ctx setup;
    let lc := add_contract contract_addr wc lc in
    let lc := set_contract_state contract_addr state lc in
    Some ([], lc).

  Local Open Scope nat.

  Definition execute_action (act : Action) (lc : LocalChain) :
    option (list Action * LocalChain) :=
    match act with
    | build_act from (act_transfer to amount) =>
      send_or_call from to amount None lc
    | build_act from (act_deploy amount wc setup) =>
      deploy_contract from amount wc setup lc
    | build_act from (act_call to amount msg) =>
      send_or_call from to amount (Some msg) lc
    end.

  Fixpoint execute_actions
           (count : nat)
           (acts : list Action)
           (lc : LocalChain)
           (depth_first : bool)
    : option LocalChain :=
    match count, acts with
    | _, [] => Some lc
    | 0, _ => None
    | S count, act :: acts =>
      do '(next_acts, lc) <- execute_action act lc;
      let acts := if depth_first
                  then next_acts ++ acts
                  else acts ++ next_acts in
      execute_actions count acts lc depth_first
    end.

  Lemma transfer_balance_equiv from to amount (lc : LocalChain) (env : Environment) :
    EnvironmentEquiv lc env ->
    EnvironmentEquiv
      (transfer_balance from to amount lc)
      (Blockchain.transfer_balance from to amount env).
  Proof.
    intros <-.
    apply build_env_equiv; auto.
    apply build_chain_equiv; auto.
    cbn.
    unfold Blockchain.add_balance.
    intros addr.
    unfold Amount in *.
    destruct_address_eq; subst;
      repeat
        (try rewrite FMap.find_partial_alter;
         try rewrite FMap.find_partial_alter_ne by auto;
         cbn); lia.
  Qed.

  Lemma set_contract_state_equiv addr state (lc : LocalChain) (env : Environment) :
    EnvironmentEquiv lc env ->
    EnvironmentEquiv
      (set_contract_state addr state lc)
      (Blockchain.set_contract_state addr state env).
  Proof.
    intros <-.
    apply build_env_equiv; auto.
    apply build_chain_equiv; auto.
    intros addr'.
    cbn.
    unfold set_chain_contract_state.
    destruct_address_eq.
    - subst. now rewrite FMap.find_add.
    - rewrite FMap.find_add_ne; auto.
  Qed.

  Lemma add_contract_equiv addr wc (lc : LocalChain) (env : Environment) :
    EnvironmentEquiv lc env ->
    EnvironmentEquiv
      (add_contract addr wc lc)
      (Blockchain.add_contract addr wc env).
  Proof.
    intros <-.
    apply build_env_equiv; auto.
    - apply build_chain_equiv; auto.
    - intros addr'.
      cbn.
      destruct_address_eq.
      + subst. now rewrite FMap.find_add.
      + rewrite FMap.find_add_ne; auto.
  Qed.

  Local Open Scope Z.
  Lemma gtb_le x y :
    x >? y = false ->
    x <= y.
  Proof.
    intros H.
    rewrite Z.gtb_ltb in H.
    apply Z.ltb_ge.
    auto.
  Qed.

  Lemma send_or_call_step from to amount msg act lc_before new_acts lc_after :
    send_or_call from to amount msg lc_before = Some (new_acts, lc_after) ->
    act = build_act from (match msg with
                          | None => act_transfer to amount
                          | Some msg => act_call to amount msg
                          end) ->
    ActionEvaluation lc_before act lc_after new_acts.
  Proof.
    intros sent act_eq.
    unfold send_or_call in sent.
    destruct (Z.gtb amount (account_balance lc_before from)) eqn:balance_enough;
      [cbn in *; congruence|].
    destruct (FMap.find to (lc_contracts lc_before)) as [wc|] eqn:to_contract.
    - (* there is a contract at destination, so do call *)
      destruct (contract_state _ _) as [prev_state|] eqn:prev_state_eq;
        [|cbn in *; congruence].
      cbn -[lc_to_env] in *.
      destruct (wc_receive wc _ _ _ _) eqn:receive;
        [|cbn in *; congruence].
      match goal with
      | [p: OakValue * list ActionBody |- _] => destruct p as [new_state resp_acts]
      end.
      Hint Resolve gtb_le : core.
      apply (eval_call from to amount wc msg prev_state new_state resp_acts);
        try solve [cbn in *; auto; congruence].
      + rewrite <- receive.
        apply wc_receive_proper; auto.
        symmetry.
        now apply transfer_balance_equiv.
      + inversion sent; subst;
          now apply set_contract_state_equiv, transfer_balance_equiv.
    - (* no contract at destination, so msg should be empty *)
      destruct (address_is_contract to) eqn:addr_format; simpl in *; try congruence.
      destruct msg; simpl in *; try congruence.
      assert (new_acts = []) by congruence; subst new_acts.
      apply (eval_transfer from to amount); auto.
      inversion sent; subst; now apply transfer_balance_equiv.
  Defined.

  Lemma get_new_contract_addr_is_contract_addr lc addr :
    get_new_contract_addr lc = Some addr ->
    address_is_contract addr = true.
  Proof.
    intros get.
    unfold get_new_contract_addr in get.
    pose proof (BoundedN.of_N_some get) as eq.
    destruct addr as [addr prf].
    cbn in *; rewrite eq.
    match goal with
    | [|- context[N.leb ?a ?b = true]] => destruct (N.leb_spec a b); auto; lia
    end.
  Qed.

  Lemma deploy_contract_step from amount wc setup act lc_before new_acts lc_after :
    deploy_contract from amount wc setup lc_before = Some (new_acts, lc_after) ->
    act = build_act from (act_deploy amount wc setup) ->
    ActionEvaluation lc_before act lc_after new_acts.
  Proof.
    intros dep act_eq.
    unfold deploy_contract in dep.
    destruct (Z.gtb amount (account_balance lc_before from)) eqn:balance_enough;
      [cbn in *; congruence|].
    destruct (get_new_contract_addr lc_before) as [contract_addr|] eqn:new_contract_addr;
      [|cbn in *; congruence].
    cbn -[incoming_txs] in dep.
    destruct (FMap.find _ _) eqn:no_contracts; [cbn in *; congruence|].
    destruct (wc_init _ _ _ _) as [state|] eqn:recv; [|cbn in *; congruence].
    cbn in dep.
    assert (new_acts = []) by congruence; subst new_acts.
    Hint Resolve get_new_contract_addr_is_contract_addr : core.
    apply (eval_deploy from contract_addr amount wc setup state); eauto.
    - rewrite <- recv.
      apply wc_init_proper; auto.
      now symmetry; apply transfer_balance_equiv.
    - inversion dep; subst lc_after.
      now apply set_contract_state_equiv, add_contract_equiv, transfer_balance_equiv.
  Defined.

  Lemma execute_action_step
        (act : Action)
        (new_acts : list Action)
        (lc_before : LocalChain)
        (lc_after : LocalChain) :
    execute_action act lc_before = Some (new_acts, lc_after) ->
    ActionEvaluation lc_before act lc_after new_acts.
  Proof.
    intros exec.
    unfold execute_action in exec.
    destruct act as [from body].
    Hint Resolve send_or_call_step deploy_contract_step : core.
    destruct body as [to amount|to amount msg|amount wc setup]; eauto.
  Defined.

  Lemma execute_actions_trace count acts (lc lc_final : LocalChain) df
        (trace : ChainTrace empty_state (build_chain_state lc acts)) :
    execute_actions count acts lc df = Some lc_final ->
    ChainTrace empty_state (build_chain_state lc_final []).
  Proof.
    revert acts lc lc_final trace.
    induction count as [| count IH]; intros acts lc lc_final trace exec; cbn in *.
    - destruct acts; congruence.
    - destruct acts as [|x xs]; try congruence.
      destruct (execute_action x lc) as [[new_acts lc_after]|] eqn:exec_once;
        cbn in *; try congruence.
      set (step := execute_action_step _ _ _ _ exec_once).
      Hint Constructors ChainStep : core.
      Hint Constructors ChainedList : core.
      Hint Unfold ChainTrace : core.
      refine (IH _ _ _ _ exec).
      destruct df.
      + (* depth-first case *)
        eauto.
      + (* breadth-first case. Insert permute step. *)
        assert (Permutation (new_acts ++ xs) (xs ++ new_acts)) by perm_simplify.
        cut (ChainTrace
              empty_state
              (build_chain_state lc_after (new_acts ++ xs))); eauto.
  Defined.
End ExecuteActions.

Definition lc_initial : LocalChain :=
  {| lc_header :=
       {| block_height := 0;
          slot_number := 0;
          finalized_height := 0; |};
     lc_account_balances := FMap.empty;
     lc_contract_state := FMap.empty;
     lc_contracts := FMap.empty; |}.

Record LocalChainBuilder :=
  build_local_chain_builder {
    lcb_lc : LocalChain;
    lcb_trace : ChainTrace empty_state (build_chain_state lcb_lc []);
  }.

Definition lcb_initial : LocalChainBuilder :=
  {| lcb_lc := lc_initial; lcb_trace := clnil |}.

Definition validate_header (new old : BlockHeader) : option unit :=
  let (prev_block_height, prev_slot_number, prev_finalized_height) := old in
  let (block_height, slot_number, finalized_height) := new in
  if (block_height =? S prev_block_height)
       && (prev_slot_number <? slot_number)
       && (finalized_height <=? prev_block_height)
       && (prev_finalized_height <=? finalized_height)
  then Some tt
  else None.

Lemma validate_header_valid (new old : BlockHeader) :
  validate_header new old = Some tt ->
  IsValidNextBlock new old.
Proof.
  intros valid.
  destruct new as [block_height slot_number fin_height];
  destruct old as [prev_block_height prev_slot_number prev_fin_height].
  unfold IsValidNextBlock.
  simpl in *.
  repeat
    match goal with
    | [H: context[Nat.eqb ?a ?b] |- _] => destruct (Nat.eqb_spec a b)
    | [H: context[Nat.ltb ?a ?b] |- _] => destruct (Nat.ltb_spec a b)
    | [H: context[Nat.leb ?a ?b] |- _] => destruct (Nat.leb_spec a b)
    end; simpl in *; intuition.
Qed.

Definition validate_actions (actions : list Action) : option unit :=
  if existsb (fun act => address_is_contract (act_from act)) actions
  then None
  else Some tt.

Lemma validate_actions_valid actions :
  validate_actions actions = Some tt ->
  Forall ActIsFromAccount actions.
Proof.
  intros valid.
  induction actions as [|x xs IH]; auto.
  unfold validate_actions in valid.
  cbn -[address_is_contract] in valid.
  destruct (address_is_contract _) eqn:eq1; try (cbn in *; congruence).
  destruct (existsb _) eqn:eq2; try (cbn in *; congruence).
  clear valid.
  unfold validate_actions in IH.
  rewrite eq2 in IH.
  auto.
Qed.

Definition add_new_block
           (header : BlockHeader)
           (baker : Address)
           (lc : LocalChain) : LocalChain :=
  let lc := add_balance baker (compute_block_reward (block_height header)) lc in
  let lc := lc<|lc_header := header|> in
  lc.

Lemma add_new_block_equiv header baker (lc : LocalChain) (env : Environment) :
  EnvironmentEquiv lc env ->
  EnvironmentEquiv
    (add_new_block header baker lc)
    (Blockchain.add_new_block header baker env).
Proof.
  intros eq.
  apply build_env_equiv; try apply eq.
  apply build_chain_equiv; try apply eq; auto.
  intros addr.
  cbn.
  unfold Blockchain.add_balance.
  destruct_address_eq.
  - subst. rewrite FMap.find_partial_alter.
    cbn.
    f_equal.
    apply eq.
  - rewrite FMap.find_partial_alter_ne; auto.
    apply eq.
Qed.

(* Adds a block to the chain by executing the specified chain actions.
   Returns the new chain if the execution succeeded (for instance,
   transactions need enough funds, contracts should not reject, etc. *)
Definition add_block
           (depth_first : bool)
           (lcb : LocalChainBuilder)
           (baker : Address)
           (actions : list Action)
           (slot_number : nat)
           (finalized_height : nat)
  : option LocalChainBuilder.
Proof.
  set (lcopt :=
         let lc := lcb_lc lcb in
         let new_header :=
             {| block_height := S (block_height (lc_header lc));
                slot_number := slot_number;
                finalized_height := finalized_height; |} in
         do validate_header new_header (lc_header lc);
         do validate_actions actions;
         let lc := add_new_block new_header baker lc in
         execute_actions 1000 actions lc depth_first).

  destruct lcopt as [lc|] eqn:exec; [|exact None].
  subst lcopt.
  cbn -[execute_actions] in exec.
  destruct (validate_header _) eqn:validate; [|simpl in *; congruence].
  destruct (validate_actions _) eqn:validate_actions; [|simpl in *; congruence].
  destruct_units.
  destruct lcb as [prev_lc_end prev_lcb_trace].
  refine (Some {| lcb_lc := lc; lcb_trace := _ |}).
  cbn -[execute_actions] in exec.

  refine (execute_actions_trace _ _ _ _ _ _ exec).
  refine (snoc prev_lcb_trace _).
  Hint Resolve validate_header_valid validate_actions_valid : core.
  eapply step_block; eauto.
  apply add_new_block_equiv.
  reflexivity.
Defined.

Global Instance LocalChainBuilderDepthFirst : ChainBuilderType :=
  {| builder_type := LocalChainBuilder;
     builder_initial := lcb_initial;
     builder_env lcb := lcb_lc lcb;
     builder_add_block := add_block true;
     builder_trace := lcb_trace; |}.

Definition LocalChainBuilderBreadthFirst : ChainBuilderType :=
  {| builder_type := LocalChainBuilder;
     builder_initial := lcb_initial;
     builder_env lcb := lcb_lc lcb;
     builder_add_block := add_block false;
     builder_trace := lcb_trace; |}.
End LocalBlockchain.
