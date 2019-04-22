From Coq Require Import Arith ZArith.
From Coq Require Import Permutation.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Containers.
From SmartContracts Require Import Extras.
From SmartContracts Require Import Automation.
From SmartContracts Require Import BoundedN.
From SmartContracts Require Import Circulation.
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

Global Instance LocalChainBaseTypes : ChainBaseTypes :=
  {| Address := BoundedN AddrSize;
     address_eqb := BoundedN.eqb;
     address_eqb_spec := BoundedN.eqb_spec;
     compute_block_reward n := 50%Z;
     address_is_contract a := (ContractAddrBase <=? BoundedN.to_N a)%N
  |}.

Record LocalChain :=
  build_local_chain {
    lc_header : BlockHeader;
    lc_incoming_txs : FMap Address (list Tx);
    lc_outgoing_txs : FMap Address (list Tx);
    lc_contract_state : FMap Address OakValue;
    lc_blocks_baked : FMap Address (list nat);
    lc_contracts : FMap Address WeakContract;
  }.

Instance local_chain_settable : Settable _ :=
  settable! build_local_chain
  < lc_header; lc_incoming_txs; lc_outgoing_txs;
    lc_contract_state; lc_blocks_baked; lc_contracts >.

Definition lc_to_env (lc : LocalChain) : Environment :=
  {| env_chain :=
        {| block_header := lc_header lc;
          incoming_txs a := with_default [] (FMap.find a (lc_incoming_txs lc));
          outgoing_txs a := with_default [] (FMap.find a (lc_outgoing_txs lc));
          contract_state a := FMap.find a (lc_contract_state lc);
          blocks_baked a := with_default [] (FMap.find a (lc_blocks_baked lc)); |};
      env_contracts a := FMap.find a (lc_contracts lc); |}.

Global Coercion lc_to_env : LocalChain >-> Environment.

Section ExecuteActions.
  Local Open Scope Z.

  Definition add_tx (tx : Tx) (lc : LocalChain) : LocalChain :=
    let add_tx opt := Some (cons tx (with_default [] opt)) in
    let lc := lc<|lc_incoming_txs ::= FMap.partial_alter add_tx (tx_to tx) |> in
    let lc := lc<|lc_outgoing_txs ::= FMap.partial_alter add_tx (tx_from tx) |> in
    lc.

  Arguments add_tx : simpl never.

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
        | None => Some ([], add_tx (build_tx from to amount tx_empty) lc)
        | Some msg => None
      end
    | Some wc =>
      let tx_body :=
          match msg with
          | None => tx_empty
          | Some msg => tx_call msg
          end in
      do state <- contract_state lc to;
      let lc := add_tx (build_tx from to amount tx_body) lc in
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
    do match incoming_txs lc contract_addr with
       | _ :: _ => None
       | [] => Some tt
       end;
    do match FMap.find contract_addr (lc_contracts lc) with
       | Some _ => None
       | None => Some tt
       end;
    let body := tx_deploy (build_contract_deployment (wc_version wc) setup) in
    let lc := add_tx (build_tx from contract_addr amount body) lc in
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

  Fixpoint execute_steps
           (gas : nat)
           (acts : list Action)
           (lc : LocalChain)
           (depth_first : bool)
    : option LocalChain :=
    match gas, acts with
    | _, [] => Some lc
    | 0, _ => None
    | S gas, act :: acts =>
      do '(next_acts, lc) <- execute_action act lc;
      let acts := if depth_first
                  then next_acts ++ acts
                  else acts ++ next_acts in
      execute_steps gas acts lc depth_first
    end.

  Ltac remember_tx :=
    match goal with
    | [H: context[add_tx ?a _] |- _] => remember a as tx
    end.

  Lemma add_tx_equiv tx (lc : LocalChain) (env : Environment) :
    EnvironmentEquiv lc env ->
    EnvironmentEquiv (add_tx tx lc) (Blockchain.add_tx tx env).
  Proof.
    intros eq.
    apply build_env_equiv; simpl in *; try apply eq.
    apply build_chain_equiv; simpl in *; try apply eq.
    - intros addr.
      unfold add_tx_to_map.
      destruct (address_eqb_spec addr (tx_to tx)) as [eq_to|neq_to].
      + subst; rewrite FMap.find_partial_alter; simpl.
        f_equal; apply eq.
      + rewrite (FMap.find_partial_alter_ne _ _ _ _ (not_eq_sym neq_to)).
        apply eq.
    - intros addr.
      unfold add_tx_to_map.
      destruct (address_eqb_spec addr (tx_from tx)) as [eq_from|neq_from].
      + subst; rewrite FMap.find_partial_alter; simpl.
        f_equal; apply eq.
      + rewrite (FMap.find_partial_alter_ne _ _ _ _ (not_eq_sym neq_from)).
        apply eq.
  Qed.

  Lemma set_contract_state_equiv addr state (lc : LocalChain) (env : Environment) :
    EnvironmentEquiv lc env ->
    EnvironmentEquiv
      (set_contract_state addr state lc)
      (Blockchain.set_contract_state addr state env).
  Proof.
    intros eq.
    apply build_env_equiv; simpl in *; try apply eq.
    apply build_chain_equiv; simpl in *; try apply eq.
    intros addr'.
    unfold set_chain_contract_state.
    destruct (address_eqb_spec addr' addr) as [eq_addrs|neq_addrs].
    - subst; now rewrite FMap.find_add.
    - rewrite FMap.find_add_ne; [apply eq|auto].
  Qed.

  Lemma add_contract_equiv addr wc (lc : LocalChain) (env : Environment) :
    EnvironmentEquiv lc env ->
    EnvironmentEquiv
      (add_contract addr wc lc)
      (Blockchain.add_contract addr wc env).
  Proof.
    intros eq.
    apply build_env_equiv; simpl in *; try apply eq.
    intros addr'.
    destruct (address_eqb_spec addr' addr) as [eq_addrs|neq_addrs].
    - subst; now rewrite FMap.find_add.
    - rewrite FMap.find_add_ne; [apply eq|auto].
  Qed.

  Lemma send_or_call_step from to amount msg act lc_before new_acts lc_after :
    send_or_call from to amount msg lc_before = Some (new_acts, lc_after) ->
    act = build_act from (match msg with
                          | None => act_transfer to amount
                          | Some msg => act_call to amount msg
                          end) ->
    exists tx, ChainStep lc_before act tx lc_after new_acts.
  Proof.
    intros sent act_eq.
    unfold send_or_call in sent.
    destruct (Z.gtb_spec amount (account_balance lc_before from)); [simpl in *; congruence|].
    destruct (FMap.find to (lc_contracts lc_before)) as [wc|] eqn:to_contract.
    - (* there is a contract at destination, so do call *)
      remember_tx.
      exists tx.
      destruct (contract_state _ _) as [prev_state|] eqn:prev_state_eq;
        cbn in *; try congruence.
      destruct (wc_receive _ _ _ _ _) eqn:receive; cbn in *; try congruence.
      match goal with
      | [p: OakValue * list ActionBody |- _] => destruct p as [new_state resp_acts]
      end.
      (* We record the steps different depending on whether this *)
      (* is a call with a message or without a message *)
      destruct msg as [msg|].
      1: apply (step_call_msg from to amount wc msg prev_state new_state resp_acts);
        try solve [simpl in *; congruence].
      3: apply (step_call_empty from to amount wc prev_state new_state resp_acts);
        try solve [simpl in *; congruence].
      1, 3:
        rewrite <- receive; unfold constructor;
        apply wc_receive_proper; auto;
          symmetry; now apply add_tx_equiv.
      1, 2:
        inversion sent; subst;
        now apply set_contract_state_equiv, add_tx_equiv.
    - (* no contract at destination, so msg should be empty *)
      destruct (address_is_contract to) eqn:addr_format; simpl in *; try congruence.
      destruct msg; simpl in *; try congruence.
      assert (new_acts = []) by congruence; subst new_acts.
      remember_tx.
      exists tx.
      apply (step_empty from to amount); auto.
      inversion sent; subst; now apply add_tx_equiv.
  Qed.

  Lemma get_new_contract_addr_is_contract_addr lc addr :
    get_new_contract_addr lc = Some addr ->
    address_is_contract addr = true.
  Proof.
    intros get.
    unfold get_new_contract_addr in get.
    pose proof (BoundedN.of_N_some get) as eq.
    destruct addr as [addr prf].
    simpl in *; rewrite eq.
    match goal with
    | [|- context[N.leb ?a ?b = true]] => destruct (N.leb_spec a b); auto; lia
    end.
  Qed.

  Lemma deploy_contract_step from amount wc setup act lc_before new_acts lc_after :
    deploy_contract from amount wc setup lc_before = Some (new_acts, lc_after) ->
    act = build_act from (act_deploy amount wc setup) ->
    exists tx, ChainStep lc_before act tx lc_after new_acts.
  Proof.
    intros dep act_eq.
    unfold deploy_contract in dep.
    destruct (Z.gtb_spec amount (account_balance lc_before from)); [cbn in *; congruence|].
    destruct (get_new_contract_addr lc_before) as [contract_addr|] eqn:new_contract_addr;
      [|cbn in *; congruence].
    cbn -[incoming_txs] in dep.
    remember_tx.
    destruct (incoming_txs _ _) eqn:no_txs; [|cbn in *; congruence].
    destruct (FMap.find _ _) eqn:no_contracts; [cbn in *; congruence|].
    destruct (wc_init _ _ _ _) as [state|] eqn:recv; [|cbn in *; congruence].
    cbn in dep.
    exists tx.
    assert (new_acts = []) by congruence; subst new_acts.
    Hint Resolve get_new_contract_addr_is_contract_addr : core.
    apply (step_deploy from contract_addr amount wc setup state); eauto.
    - rewrite <- recv.
      apply wc_init_proper; auto.
      now symmetry; apply add_tx_equiv.
    - inversion dep; subst lc_after.
      now apply set_contract_state_equiv, add_contract_equiv, add_tx_equiv.
  Qed.

  Lemma execute_action_step
        (act : Action)
        (new_acts : list Action)
        (lc_before : LocalChain)
        (lc_after : LocalChain) :
    execute_action act lc_before = Some (new_acts, lc_after) ->
    exists tx, ChainStep lc_before act tx lc_after new_acts.
  Proof.
    intros exec.
    unfold execute_action in exec.
    destruct act as [from body].
    Hint Resolve send_or_call_step deploy_contract_step : core.
    destruct body as [to amount|to amount msg|amount wc setup]; eauto.
  Qed.

  Lemma execute_steps_trace gas acts lc df lc_after :
    execute_steps gas acts lc df = Some lc_after ->
    BlockTrace lc acts lc_after [].
  Proof.
    revert acts lc lc_after.
    induction gas as [|gas IH]; intros acts lc lc_after exec.
    - unfold execute_steps in exec.
      destruct acts as [|x xs]; [|congruence].
      Hint Constructors BlockTrace : core.
      replace lc_after with lc by congruence; auto.
    - destruct acts as [|x xs]; simpl in *.
      + replace lc_after with lc by congruence; auto.
      + destruct (execute_action x lc) as [[acts lc_after_act]|] eqn:exec_once;
          simpl in *; [|congruence].
        specialize (IH _ _ _ exec); clear exec.
        destruct (execute_action_step _ _ _ _ exec_once) as [tx step]; clear exec_once.
        (* For breadth first case our IH is xs ++ acts ->* [] and we need to show *)
        (* x :: xs ->* [], so we will need to permute it first. *)
        assert (Permutation (xs ++ acts) (acts ++ xs)) by perm_simplify.
        destruct df; eauto.
  Qed.
End ExecuteActions.

Definition lc_initial : LocalChain :=
  {| lc_header :=
       {| block_height := 0;
          slot_number := 0;
          finalized_height := 0; |};
     lc_incoming_txs := FMap.empty;
     lc_outgoing_txs := FMap.empty;
     lc_contract_state := FMap.empty;
     lc_blocks_baked := FMap.empty;
     lc_contracts := FMap.empty; |}.

Record LocalChainBuilder :=
  build_local_chain_builder {
    lcb_lc : LocalChain;
    lcb_trace : ChainTrace lc_initial lcb_lc;
  }.

Definition lcb_initial : LocalChainBuilder.
Proof.
  refine
    {| lcb_lc := lc_initial; lcb_trace := _ |}.
  apply ctrace_initial.
  apply build_env_equiv; auto.
  apply build_chain_equiv; auto.
Defined.

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
  refine (
      let lcopt :=
         let lc := lcb_lc lcb in
         let new_header :=
             {| block_height := S (block_height (lc_header lc));
                slot_number := slot_number;
                finalized_height := finalized_height; |} in
         do validate_header new_header (lc_header lc);
         let lc := lc<|lc_header := new_header|> in
         let add_block o :=
             Some ((block_height new_header) :: (with_default [] o)) in
         let lc := lc<|lc_blocks_baked ::= FMap.partial_alter add_block baker|> in
         execute_steps 10 actions lc depth_first in
      _).

  destruct lcopt as [lc|] eqn:exec; [|exact None].
  subst lcopt.
  cbn -[execute_steps] in exec.
  destruct (validate_header _) eqn:validate; [|simpl in *; congruence].
  destruct_units.
  match goal with
  | [H: context[validate_header ?new _] |- _] => remember new as new_header
  end.
  unfold constructor in *.
  cbn -[execute_steps] in exec.

  destruct lcb as [prev_lc_end prev_lcb_trace].
  refine (Some {| lcb_lc := lc; lcb_trace := _ |}).
  match goal with
  | [H: context[execute_steps _ _ ?a] |- _] => remember a as lc_block_start
  end.
  Hint Resolve validate_header_valid execute_steps_trace : core.
  apply (ctrace_block lc_initial prev_lc_end new_header baker actions lc_block_start lc);
    eauto; clear validate.

  subst lc_block_start.
  simpl.
  apply build_env_equiv; auto.
  apply build_chain_equiv; auto.
  intros addr.
  simpl.
  destruct (address_eqb_spec addr baker) as [addrs_eq|addrs_neq].
  - subst.
    now rewrite FMap.find_partial_alter.
  - now rewrite FMap.find_partial_alter_ne; auto.
Defined.

Global Instance lcb_chain_builder_type : ChainBuilderType :=
  {| builder_type := LocalChainBuilder;
     builder_initial := lcb_initial;
     builder_env lcb := lcb_lc lcb;
     builder_add_block := add_block true;
     builder_trace := lcb_trace; |}.

Definition lcb_chain_builder_type_breadth_first : ChainBuilderType :=
  {| builder_type := LocalChainBuilder;
     builder_initial := lcb_initial;
     builder_env lcb := lcb_lc lcb;
     builder_add_block := add_block false;
     builder_trace := lcb_trace; |}.

End LocalBlockchain.
