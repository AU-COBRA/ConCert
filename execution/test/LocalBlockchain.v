(* This file gives two different implementations of the blockchain
execution layer defined in Blockchain.v. Both versions are execution
layers using std++'s finite maps and are thus relatively
efficient. They differ in execution order: one uses a depth-first
execution order, while the other uses a breadth-first execution order. *)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import List.
From Coq Require Import Psatz.

Import ListNotations.

Section LocalBlockchain.
  Local Open Scope bool.

  Context {AddrSize : N}.
  Context {DepthFirst : bool}.

  Definition ContractAddrBase : N := AddrSize / 2.

  Global Instance LocalChainBase : ChainBase :=
    {| Address := BoundedN AddrSize;
      address_eqb := BoundedN.eqb;
      address_eqb_spec := BoundedN.eqb_spec;
      address_is_contract a := (ContractAddrBase <=? BoundedN.to_N a)%N
    |}.

  Record LocalChain :=
    build_local_chain {
      lc_height : nat;
      lc_slot : nat;
      lc_fin_height : nat;
      lc_account_balances : FMap Address Amount;
      lc_contract_state : FMap Address SerializedValue;
      lc_contracts : FMap Address WeakContract;
    }.

  MetaCoq Run (make_setters LocalChain).

  Definition lc_to_env (lc : LocalChain) : Environment :=
    {| env_chain :=
          {| chain_height := lc_height lc;
            current_slot := lc_slot lc;
            finalized_height := lc_fin_height lc; |};
      env_account_balances a := with_default 0%Z (FMap.find a (lc_account_balances lc));
      env_contract_states a := FMap.find a (lc_contract_state lc);
      env_contracts a := FMap.find a (lc_contracts lc); |}.

  Global Coercion lc_to_env : LocalChain >-> Environment.

  Section ExecuteActions.
    Local Open Scope Z.

    Definition add_balance
                (addr : Address)
                (amt : Amount)
                (lc : LocalChain)
                : LocalChain :=
      let update opt := Some (amt + with_default 0 opt) in
      lc<|lc_account_balances ::= FMap.partial_alter update addr|>.

    Definition transfer_balance
                (from to : Address)
                (amount : Amount)
                (lc : LocalChain)
                : LocalChain :=
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
                (state : SerializedValue)
                (lc : LocalChain) : LocalChain :=
      lc<|lc_contract_state ::= FMap.add addr state|>.

    Definition weak_error_to_error_init
                (r : result SerializedValue SerializedValue)
                : result SerializedValue ActionEvaluationError :=
      bind_error (fun err => init_failed err) r.

    Definition weak_error_to_error_receive
                (r : result (SerializedValue * list ActionBody) SerializedValue)
                : result (SerializedValue * list ActionBody) ActionEvaluationError :=
      bind_error (fun err => receive_failed err) r.

    Definition send_or_call
                (origin : Address)
                (from to : Address)
                (amount : Amount)
                (msg : option SerializedValue)
                (lc : LocalChain)
                : result (list Action * LocalChain) ActionEvaluationError :=
      do if amount <? 0 then Err (amount_negative amount) else Ok tt;
      do if amount >? env_account_balances lc from then Err (amount_too_high amount) else Ok tt;
      match FMap.find to lc.(lc_contracts) with
      | None =>
        (* Fail if sending a message to address without contract *)
        do if address_is_contract to then Err (no_such_contract to) else Ok tt;
        match msg with
          | None => Ok ([], transfer_balance from to amount lc)
          | Some msg => Err (no_such_contract to)
        end
      | Some wc =>
        do state <- result_of_option (env_contract_states lc to) internal_error;
        let lc := transfer_balance from to amount lc in
        let ctx := build_ctx origin from to (env_account_balances lc to) amount in
        do '(new_state, new_actions) <- weak_error_to_error_receive (wc_receive wc lc ctx state msg);
        let lc := set_contract_state to new_state lc in
          Ok (map (build_act origin to) new_actions, lc)
      end.

    Definition deploy_contract
                (origin : Address)
                (from : Address)
                (amount : Amount)
                (wc : WeakContract)
                (setup : SerializedValue)
                (lc : LocalChain)
                : result (list Action * LocalChain) ActionEvaluationError :=
      do if amount <? 0 then Err (amount_negative amount) else Ok tt;
      do if amount >? env_account_balances lc from then Err (amount_too_high amount) else Ok tt;
      do contract_addr <- result_of_option (get_new_contract_addr lc) too_many_contracts;
      do match FMap.find contract_addr (lc_contracts lc) with
        | Some _ => Err internal_error
        | None => Ok tt
        end;
      let lc := transfer_balance from contract_addr amount lc in
      let ctx := build_ctx origin from contract_addr amount amount in
      do state <- weak_error_to_error_init (wc_init wc lc ctx setup);
      let lc := add_contract contract_addr wc lc in
      let lc := set_contract_state contract_addr state lc in
      Ok ([], lc).

    Local Open Scope nat.

    Definition execute_action
                (act : Action)
                (lc : LocalChain)
                : result (list Action * LocalChain) ActionEvaluationError :=
      match act with
      | build_act origin from (act_transfer to amount) =>
        send_or_call origin from to amount None lc
      | build_act origin from (act_deploy amount wc setup) =>
        deploy_contract origin from amount wc setup lc
      | build_act origin from (act_call to amount msg) =>
        send_or_call origin from to amount (Some msg) lc
      end.

    Fixpoint execute_actions
              (count : nat)
              (acts : list Action)
              (lc : LocalChain)
              (depth_first : bool)
              : result LocalChain AddBlockError :=
      match count, acts with
      | _, [] => Ok lc
      | 0, _ => Err action_evaluation_depth_exceeded
      | S count, act :: acts =>
        match execute_action act lc with
        | Ok (next_acts, lc) =>
          let acts := if depth_first
                      then next_acts ++ acts
                      else acts ++ next_acts in
          execute_actions count acts lc depth_first
        | Err act_err =>
          Err (action_evaluation_error act act_err)
        end
      end.

    Lemma transfer_balance_equiv
            (from to : Address)
            (amount : Amount)
            (lc : LocalChain)
            (env : Environment) :
      EnvironmentEquiv lc env ->
      EnvironmentEquiv
        (transfer_balance from to amount lc)
        (Blockchain.transfer_balance from to amount env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
      cbn.
      intros addr.
      unfold Amount in *.
      destruct_address_eq; subst;
        repeat
          (try rewrite FMap.find_partial_alter;
          try rewrite FMap.find_partial_alter_ne by auto;
          cbn); lia.
    Defined.

    Lemma set_contract_state_equiv addr state (lc : LocalChain) (env : Environment) :
      EnvironmentEquiv lc env ->
      EnvironmentEquiv
        (set_contract_state addr state lc)
        (Blockchain.set_contract_state addr state env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
      intros addr'.
      cbn.
      unfold set_chain_contract_state.
      destruct_address_eq.
      - subst. now rewrite FMap.find_add.
      - rewrite FMap.find_add_ne; auto.
    Defined.

    Lemma add_contract_equiv addr wc (lc : LocalChain) (env : Environment) :
      EnvironmentEquiv lc env ->
      EnvironmentEquiv
        (add_contract addr wc lc)
        (Blockchain.add_contract addr wc env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
      intros addr'.
      cbn.
      destruct_address_eq.
      - subst. now rewrite FMap.find_add.
      - rewrite FMap.find_add_ne; auto.
    Defined.

    Local Open Scope Z.
    Lemma gtb_le x y :
      x >? y = false ->
      x <= y.
    Proof.
      intros H.
      rewrite Z.gtb_ltb in H.
      apply Z.ltb_ge.
      auto.
    Defined.

    Lemma ltb_ge x y :
      x <? y = false ->
      x >= y.
    Proof.
      intros H.
      apply Z.ltb_ge in H.
      lia.
    Defined.

    Local Hint Resolve gtb_le ltb_ge : core.

    Lemma send_or_call_step origin from to amount msg act lc_before new_acts lc_after :
      send_or_call origin from to amount msg lc_before = Ok (new_acts, lc_after) ->
      act = build_act origin from (match msg with
                                  | None => act_transfer to amount
                                  | Some msg => act_call to amount msg
                                  end) ->
      ActionEvaluation lc_before act lc_after new_acts.
    Proof.
      intros sent act_eq.
      unfold send_or_call in sent.
      destruct (Z.ltb amount 0) eqn:amount_nonnegative;
        [cbn in *; congruence|].
      destruct (Z.gtb amount (env_account_balances lc_before from)) eqn:balance_enough;
        [cbn in *; congruence|].
      destruct (FMap.find to (lc_contracts lc_before)) as [wc|] eqn:to_contract.
      - (* there is a contract at destination, so do call *)
        destruct (env_contract_states _ _) as [prev_state|] eqn:prev_state_eq;
          [|cbn in *; congruence].
        cbn -[lc_to_env] in *.
        destruct (wc_receive wc _ _ _ _) as [[new_state resp_acts]|] eqn:receive;
          [|cbn in *; congruence].
        apply (eval_call origin from to amount wc msg prev_state new_state resp_acts);
          try solve [cbn in *; auto; congruence].
        + cbn in sent.
          inversion_clear sent.
          rewrite <- receive.
          auto.
        + inversion sent; subst;
            now apply set_contract_state_equiv, transfer_balance_equiv.
      - (* no contract at destination, so msg should be empty *)
        destruct (address_is_contract to) eqn:addr_format; cbn in *; try congruence.
        destruct msg; cbn in *; try congruence.
        assert (new_acts = []) by congruence; subst new_acts.
        apply (eval_transfer origin from to amount); auto.
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
    Defined.

    Local Hint Resolve get_new_contract_addr_is_contract_addr : core.
    Lemma deploy_contract_step origin from amount wc setup act lc_before new_acts lc_after :
      deploy_contract origin from amount wc setup lc_before = Ok (new_acts, lc_after) ->
      act = build_act origin from (act_deploy amount wc setup) ->
      ActionEvaluation lc_before act lc_after new_acts.
    Proof.
      intros dep act_eq.
      unfold deploy_contract in dep.
      destruct (Z.ltb amount 0) eqn:amount_nonnegative;
        [cbn in *; congruence|].
      destruct (Z.gtb amount (env_account_balances lc_before from)) eqn:balance_enough;
        [cbn in *; congruence|].
      destruct (get_new_contract_addr lc_before) as [contract_addr|] eqn:new_contract_addr;
        [|cbn in *; congruence].
      cbn -[incoming_txs] in dep.
      destruct (FMap.find _ _) eqn:no_contracts; [cbn in *; congruence|].
      destruct (wc_init _ _ _ _) as [state|] eqn:recv; [|cbn in *; congruence].
      cbn in dep.
      assert (new_acts = []) by congruence; subst new_acts.
      apply (eval_deploy origin from contract_addr amount wc setup state); eauto.
      inversion dep; subst lc_after.
      now apply set_contract_state_equiv, add_contract_equiv, transfer_balance_equiv.
    Defined.

    Local Hint Resolve send_or_call_step deploy_contract_step : core.
    Lemma execute_action_step
          (act : Action)
          (new_acts : list Action)
          (lc_before : LocalChain)
          (lc_after : LocalChain) :
      execute_action act lc_before = Ok (new_acts, lc_after) ->
      ActionEvaluation lc_before act lc_after new_acts.
    Proof.
      intros exec.
      unfold execute_action in exec.
      destruct act as [orig from body].
      destruct body as [to amount|to amount msg|amount wc setup]; eauto.
    Defined.

    Hint Constructors ChainStep : core.
    Hint Constructors ChainedList : core.
    Hint Unfold ChainTrace : core.

    Lemma execute_actions_trace count acts (lc lc_final : LocalChain) df
          (trace : ChainTrace empty_state (build_chain_state lc acts)) :
      execute_actions count acts lc df = Ok lc_final ->
      ChainTrace empty_state (build_chain_state lc_final []).
    Proof.
      revert acts lc lc_final trace.
      induction count as [| count IH]; intros acts lc lc_final trace exec; cbn in *.
      - destruct acts; congruence.
      - destruct acts as [|x xs]; try congruence.
        destruct (execute_action x lc) as [[new_acts lc_after]|] eqn:exec_once;
          cbn in *; try congruence.
        set (step := execute_action_step _ _ _ _ exec_once).
        refine (IH _ _ _ _ exec).
        destruct df.
        + (* depth-first case *)
          eauto.
        + (* breadth-first case. Insert permute step. *)
          assert (Permutation (new_acts ++ xs) (xs ++ new_acts)) by perm_simplify.
          cut (ChainTrace
                empty_state
                (build_chain_state lc_after (new_acts ++ xs))); eauto.
          intros.
          econstructor; eauto.
          constructor; eauto.
          constructor; eauto.
    Defined.
  End ExecuteActions.

  Definition lc_initial : LocalChain :=
    {| lc_height := 0;
      lc_slot := 0;
      lc_fin_height := 0;
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

  Definition validate_header (header : BlockHeader) (chain : Chain) : bool :=
    (block_height header =? S (chain_height chain))
    && (current_slot chain <? block_slot header)
    && (finalized_height chain <=? block_finalized_height header)
    && (block_finalized_height header <? block_height header)
    && address_not_contract (block_creator header)
    && (block_reward header >=? 0)%Z.

  Lemma validate_header_valid header chain :
    validate_header header chain = true ->
    IsValidNextBlock header chain.
  Proof.
    intros valid.
    unfold validate_header in valid.
    repeat
      (match goal with
      | [H: context[Nat.eqb ?a ?b] |- _] => destruct (Nat.eqb_spec a b)
      | [H: context[Nat.ltb ?a ?b] |- _] => destruct (Nat.ltb_spec a b)
      | [H: context[Nat.leb ?a ?b] |- _] => destruct (Nat.leb_spec a b)
      | [H: context[Z.geb ?a ?b] |- _] => destruct (Z.geb_spec a b)
      end; [|repeat rewrite Bool.andb_false_r in valid; cbn in valid; congruence]).
    destruct (address_not_contract (block_creator header)) eqn:to_acc;
      [|cbn in valid; congruence].
    apply Bool.negb_true_iff in to_acc.
    apply build_is_valid_next_block; cbn; auto.
    lia.
  Defined.

  Definition find_origin_neq_from (actions : list Action) : option Action :=
    find (fun act => address_neqb (act_origin act) (act_from act)) actions.

  Lemma validate_origin_neq_from_valid actions :
    find_origin_neq_from actions = None ->
    Forall (fun act => address_eqb (act_origin act) (act_from act) = true) actions.
  Proof.
    intros find_none.
    unfold find_origin_neq_from in find_none.
    specialize (List.find_none _ _ find_none) as all_nin.
    cbn in *.
    assert (all_nin0 : forall x, In x actions -> (act_origin x =? act_from x)%address = true).
    { intros. now apply ssrbool.negbFE. }
    now apply Forall_forall in all_nin0.
  Defined.

  Definition find_invalid_root_action (actions : list Action) : option Action :=
    find (fun act => address_is_contract (act_from act)) actions.

  Lemma validate_actions_valid actions :
    find_invalid_root_action actions = None ->
    Forall (fun act => act_is_from_account act) actions.
  Proof.
    intros find_none.
    unfold find_invalid_root_action in find_none.
    specialize (List.find_none _ _ find_none) as all_nin.
    unfold act_is_from_account.
    now apply Forall_forall in all_nin.
  Defined.

  Definition add_new_block (header : BlockHeader) (lc : LocalChain) : LocalChain :=
    let lc := add_balance (block_creator header) (block_reward header) lc in
    lc<|lc_height := block_height header|>
      <|lc_slot := block_slot header|>
      <|lc_fin_height := block_finalized_height header|>.

  Lemma add_new_block_equiv header (lc : LocalChain) (env : Environment) :
    EnvironmentEquiv lc env ->
    EnvironmentEquiv
      (add_new_block header lc)
      (Blockchain.add_new_block_to_env header env).
  Proof.
    intros eq.
    apply build_env_equiv; try apply eq; auto.
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
  Defined.

  (* The computational bits of adding a block *)
  Definition add_block_exec
            (depth_first : bool)
            (lc : LocalChain)
            (header : BlockHeader)
            (actions : list Action) : result LocalChain AddBlockError :=
    do (if validate_header header lc then Ok tt else Err (invalid_header header));
    do (match find_origin_neq_from actions with
        | Some act => Err (origin_from_mismatch act)
        | None => Ok tt
        end);
    do (match find_invalid_root_action actions with
        | Some act => Err (invalid_root_action act)
        | None => Ok tt
        end);
    let lc := add_new_block header lc in
    execute_actions 1000 actions lc depth_first.

  Local Hint Resolve validate_header_valid validate_actions_valid validate_origin_neq_from_valid : core.

  (* Adds a block to the chain by executing the specified chain actions.
    Returns the new chain if the execution succeeded (for instance,
    transactions need enough funds, contracts should not reject, etc. *)
  Definition add_block
            (depth_first : bool)
            (lcb : LocalChainBuilder)
            (header : BlockHeader)
            (actions : list Action) : result LocalChainBuilder AddBlockError.
  Proof.
    set (lcopt := add_block_exec depth_first (lcb_lc lcb) header actions).
    unfold add_block_exec in lcopt.
    destruct lcopt as [lc|e] eqn:exec; [|exact (Err e)].
    subst lcopt.
    destruct (validate_header _) eqn:validate; [|cbn in exec; congruence].
    destruct (find_origin_neq_from _) eqn:no_origin_neq_from; [cbn in exec; congruence|].
    destruct (find_invalid_root_action _) eqn:no_invalid_root_act; [cbn in exec; congruence|].
    destruct lcb as [prev_lc_end prev_lcb_trace].
    refine (Ok {| lcb_lc := lc; lcb_trace := _ |}).
    cbn -[execute_actions] in exec.

    refine (execute_actions_trace _ _ _ _ _ _ exec).
    refine (snoc prev_lcb_trace _).
    apply (step_block _ _ header); auto.
    apply add_new_block_equiv.
    reflexivity.
  Defined.

  Definition LocalChainBuilderImpl : ChainBuilderType :=
    {| builder_type := LocalChainBuilder;
      builder_initial := lcb_initial;
      builder_env lcb := lcb_lc lcb;
      builder_add_block := add_block DepthFirst;
      builder_trace := lcb_trace; |}.

End LocalBlockchain.

Arguments LocalChainBase : clear implicits.
Arguments LocalChainBuilder : clear implicits.
Arguments LocalChainBuilderImpl : clear implicits.
Arguments lcb_initial : clear implicits.
