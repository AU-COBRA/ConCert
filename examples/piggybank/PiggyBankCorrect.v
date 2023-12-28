(** * Piggybank contract *)
(** Proofs for Piggybank contract defined in [ConCert.Examples.piggybank.piggybank]. *)

From ConCert.Examples.PiggyBank Require Import PiggyBank.

From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import BuildUtils.

From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith_base.
From Coq Require Import Lia.

(** A few tactics to make the proofs more manageable and more transparent *)
Ltac insert_reduce :=
  match goal with
  | H : insert ?state ?ctx = _ |- _ =>
    unfold insert in H;
    destruct (ctx_amount ctx <? 0)%Z eqn:Epos in H; try discriminate;
    destruct (is_smashed state) eqn:Esmash in H; try discriminate
  end.

Ltac smash_reduce :=
  match goal with
  | H : smash ?state ?ctx = _ |- _ =>
    unfold smash in H;
    destruct (is_smashed state) eqn:Esmash in H; try discriminate;
    destruct (address_neqb ctx.(ctx_from) state.(owner)) eqn:Eowner in H; try discriminate
  end.

(** ** Functional properties *)
Section FunctionalProperties.
  Context `{BaseTypes : ChainBase}.
  Open Scope Z.

  (** If insert runs then it inserts the correct amount to the correct account *)
  Lemma insert_inserts_correct (prev_state next_state : State)
                               (ctx : ContractCallContext)
                               (acts : list ActionBody) :
    insert prev_state ctx = Ok (next_state, acts) ->
    acts = [] /\
    Z.add ctx.(ctx_amount) prev_state.(balance) = next_state.(balance).
  Proof.
    intros Hinsert.
    insert_reduce.
    now inversion Hinsert.
  Qed.

  (** If smash runs successfully the resulting state is smashed and the amount in the PiggyBank
      is transfered to the owner *)
  Lemma smash_transfers_correctly (prev_state next_state : State)
                                  (ctx : ContractCallContext)
                                  (acts : list ActionBody) :
    smash prev_state ctx = Ok (next_state, acts) ->
    next_state.(piggyState) = Smashed /\
    next_state.(balance) = 0 /\
    acts = [act_transfer prev_state.(owner) (prev_state.(balance) + ctx.(ctx_amount))].
  Proof.
    intros Hsmash.
    smash_reduce.
    now inversion Hsmash.
  Qed.

  Lemma receive_is_correct (chain : Chain)
                           (ctx : ContractCallContext)
                           (prev_state next_state : State)
                           (msg : option Msg)
                           (acts : list ActionBody) :
    PiggyBank.receive chain ctx prev_state msg = Ok (next_state, acts) ->
    match msg with
      | Some Insert => acts = [] /\ Z.add ctx.(ctx_amount) prev_state.(balance) = next_state.(balance)
      | Some Smash => next_state.(piggyState) = Smashed /\ next_state.(balance) = 0
                      /\ acts = [act_transfer prev_state.(owner) (prev_state.(balance) + ctx.(ctx_amount))]
      | None => False
    end.
  Proof.
    intros Hreceive. unfold PiggyBank.receive in Hreceive.
    destruct msg; try discriminate.
    destruct m;
    [apply insert_inserts_correct | apply smash_transfers_correctly];
    apply Hreceive.
  Qed.
End FunctionalProperties.

(** ** Safety properties *)
Section SafetyProperties.
  Context `{BaseTypes : ChainBase}.
  Open Scope Z.

  (** Contract never calls itself *)
  Lemma no_self_calls bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    Forall (fun act_body =>
      match act_body with
      | act_transfer to _ => (to =? caddr)%address = false
      | _ => False
      end) (outgoing_acts bstate caddr).
  Proof.
    contract_induction; intros; auto.
    - now inversion IH.
    - apply Forall_app; split; auto.
      clear IH. simpl in *.
      destruct msg; try discriminate.
      destruct m; unfold PiggyBank.receive in receive_some;
      [insert_reduce | smash_reduce];
      inversion receive_some; eauto.
      apply address_neqb_eq in Eowner. rewrite Eowner in from_other.
      now apply address_eq_ne in from_other.
    - inversion_clear IH as [|? ? head_not_me tail_not_me].
      apply Forall_app; split; auto; clear tail_not_me.
      destruct head; try contradiction.
      destruct action_facts as [? _].
      destruct_address_eq; congruence.
    - now rewrite <- perm.
    - solve_facts.
  Qed.

  (** This is already proved above and not really a safety property *)
  Lemma receive_produces_no_calls_when_running_insert (chain : Chain)
                                                      (ctx : ContractCallContext)
                                                      (cstate new_cstate : State)
                                                      (acts : list ActionBody) :
   PiggyBank.receive chain ctx cstate (Some Insert) = Ok (new_cstate, acts) ->
   acts = [].
  Proof.
    intros Hreceive. subst.
    unfold PiggyBank.receive in Hreceive.
    now apply insert_inserts_correct in Hreceive as [<- _].
  Qed.

  (** The owner never changes between states *)
  Lemma owner_remains (chain : Chain)
                      (ctx : ContractCallContext)
                      (prev_state next_state : State)
                      (msg : option Msg)
                      (acts : list ActionBody) :
    PiggyBank.receive chain ctx prev_state msg = Ok (next_state, acts) ->
    prev_state.(owner) = next_state.(owner).
  Proof.
    intros Hreceive. unfold PiggyBank.receive in Hreceive.
    destruct msg; try discriminate.
    destruct m;
    [insert_reduce | smash_reduce];
    now inversion Hreceive.
  Qed.

  (** The owner at any state is the same as the original owner *)
  Lemma owner_correct bstate caddr (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    exists cstate dep,
      deployment_info Setup trace caddr = Some dep /\
      contract_state bstate caddr = Some cstate /\
      cstate.(owner) = dep.(deployment_from).
  Proof.
    contract_induction; intros; auto;
    try (specialize owner_remains with chain ctx prev_state new_state msg new_acts;
      intros; specialize (H receive_some); rewrite H in IH; assumption).
    - cbn in init_some. unfold PiggyBank.init in init_some.
      destruct result. now inversion init_some.
    - solve_facts.
  Qed.

  (** When smashed the PiggyBank stays smashed *)
  Lemma stay_smashed {prev_state msg chain ctx} :
    prev_state.(piggyState) = Smashed ->
      exists e : Error, PiggyBank.receive chain ctx prev_state msg = Err e.
  Proof.
    intros state_smashed. unfold PiggyBank.receive.
    destruct msg, prev_state. cbn in *.
    rewrite state_smashed. cbn.
    - destruct_match; eauto.
      destruct_match; eauto.
      destruct_match; eauto.
    - eauto.
  Qed.

  (** The total amount in an intact PiggyBank can only increase *)
  Lemma if_intact_then_balance_can_only_increase (prev_state next_state : State)
                                                 (ctx : ContractCallContext)
                                                 (chain : Chain)
                                                 (new_acts : list ActionBody) :
    prev_state.(piggyState) = Intact ->
    PiggyBank.receive chain ctx prev_state (Some Insert) = Ok (next_state, new_acts) ->
    Z.le prev_state.(balance) next_state.(balance).
  Proof.
    intros state_intact Hreceive.
    unfold PiggyBank.receive in Hreceive.
    destruct prev_state; cbn in *; rewrite state_intact in Hreceive.
    destruct (ctx_amount ctx <? 0) eqn:E; try discriminate.
    inversion Hreceive; cbn; lia.
  Qed.

  (** Initializes to correct state *)
  Lemma initializes_correctly (chain : Chain)
                              (ctx : ContractCallContext)
                              (setup : Setup)
                              (new_state : State) :
    PiggyBank.init chain ctx setup = Ok new_state ->
      new_state.(piggyState) = Intact.
  Proof.
    intros Hinit. unfold PiggyBank.init in Hinit. now inversion Hinit.
  Qed.

  (** We need this little lemma for the next property *)
  Lemma neq_false_eq : forall x y : Z, negb (x =? y) = false <-> x = y.
  Proof. split; lia. Qed.

  (** Balance in PiggyBank is correct on the blockchain *)
  Lemma balance_on_chain' :
    forall (bstate : ChainState) caddr,
    let effective_balance := (env_account_balances bstate caddr - sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr))%Z in
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      effective_balance = cstate.(balance).
  Proof.
    intros.
    subst effective_balance.
    contract_induction; intros; auto; cbn in *.
    - unfold PiggyBank.init in init_some. inversion init_some. cbn. lia.
    - lia.
    - unfold PiggyBank.receive in receive_some.
      destruct msg; try discriminate. destruct m;
      [insert_reduce | smash_reduce];
      inversion receive_some; cbn; lia.
    - unfold PiggyBank.receive in receive_some.
      destruct msg; try discriminate. destruct m;
      [insert_reduce | smash_reduce];
      inversion receive_some; destruct head; cbn in *; lia.
    - now erewrite sumZ_permutation in IH by eauto.
    - solve_facts.
  Qed.

  Lemma balance_on_chain :
    forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      env_account_balances bstate caddr = cstate.(balance).
  Proof.
    intros * reach deployed.
    edestruct balance_on_chain' as (cstate & balance); eauto.
    intros Hact. rewrite Hact in balance. cbn in *.
    now exists cstate.
  Qed.

  Lemma no_outgoing_actions_when_intact :
    forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      (cstate.(piggyState) = Intact -> outgoing_acts bstate caddr = []).
  Proof.
    intros * reach deployed.
    contract_induction; intros; auto.
    - now specialize (IH H).
    - cbn in *. unfold PiggyBank.receive in receive_some.
      destruct msg; try discriminate. destruct m;
      [insert_reduce | smash_reduce];
      inversion receive_some.
      + unfold is_smashed in Esmash.
        cbn. now subst.
      + destruct new_state. inversion H1. rewrite <- H5 in H. discriminate H.
    - instantiate (CallFacts := fun _ ctx prev_state queue _ =>
      ctx_from ctx <> ctx_contract_address ctx).
      now destruct fact.
    - specialize (IH H). rewrite IH in perm.
      now eapply Permutation.Permutation_nil in perm.
    - solve_facts.
      apply trace_reachable in from_reachable.
      pose proof (no_self_calls bstate_from to_addr ltac:(assumption) ltac:(assumption))
           as all.
      unfold outgoing_acts in *.
      rewrite queue_prev in *.
      cbn in all.
      destruct_address_eq; cbn in *; auto.
      inversion_clear all as [|? ? hd _].
      destruct msg.
      + contradiction.
      + rewrite address_eq_refl in hd.
        congruence.
  Qed.

  (** When the PiggyBank is smashed its balance needs to remain zero *)
  Lemma balance_is_zero_when_smashed' :
    forall (bstate : ChainState) caddr,
    let effective_balance := (env_account_balances bstate caddr - sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr))%Z in
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      (cstate.(piggyState) = Smashed -> effective_balance = 0).
  Proof.
    intros.
    subst effective_balance.
    contract_induction; intros; auto; cbn in *.
    - unfold PiggyBank.init in init_some. inversion init_some.
      destruct result. inversion H1. rewrite <- H4 in H. discriminate H.
    - specialize (IH H). lia.
    - unfold PiggyBank.receive in receive_some.
      destruct msg; try discriminate. destruct m;
      [insert_reduce | smash_reduce];
      inversion receive_some.
      + unfold is_smashed in Esmash. destruct prev_state, new_state.
        inversion H1. cbn in *. now subst.
      + instantiate (CallFacts := fun _ ctx prev_state queue _ =>
        (prev_state.(piggyState) = Intact -> ctx_contract_balance ctx - ctx_amount ctx = balance prev_state) /\
        (prev_state.(piggyState) = Intact -> queue = [])
        /\ ctx_from ctx <> ctx_contract_address ctx).
        destruct facts as [Hamount [Hqueue _]].
        unfold is_smashed in Esmash. destruct prev_state.(piggyState) eqn:Estate; try discriminate.
        rewrite Hqueue, <- Hamount; try reflexivity. cbn. lia.
    - now destruct facts.
    - now erewrite sumZ_permutation in IH by eauto.
    - solve_facts.
      repeat split; rewrite deployed in *;
      match goal with
      | H : Some ?x = Some _ |- _ => inversion H; subst x; clear H
      end.
      + rewrite address_eq_refl. intros state_intact.
        edestruct balance_on_chain' as (state1 & construct1 & balance); eauto.
        now constructor.
        edestruct no_outgoing_actions_when_intact as (state2 & [construct2 act]); eauto.
        now constructor.
        unfold contract_state in *.
        destruct (env_contract_states bstate_from to_addr); try discriminate.
        inversion construct1 as [some_s_is_state1]. inversion construct2 as [some_s_is_state2].
        rewrite deployed_state0 in *.
        inversion some_s_is_state1 as [cstate_is_state1]. inversion some_s_is_state2 as [cstate_is_state2].
        rewrite <- cstate_is_state2 in act.
        specialize (act state_intact). rewrite act in balance. rewrite <- balance.
        destruct (to_addr =? from_addr)%address eqn:addr.
        * apply trace_reachable in from_reachable.
        pose proof (no_self_calls bstate_from to_addr ltac:(assumption) ltac:(assumption))
             as all.
        unfold outgoing_acts in *.
        rewrite queue_prev in *.
        cbn in all.
        destruct_address_eq; cbn in *; auto.
        inversion_clear all as [|? ? hd _].
        destruct msg.
        ** contradiction.
        ** rewrite address_eq_refl in hd.
          congruence.
        ** discriminate.
        * cbn. lia.
      + edestruct no_outgoing_actions_when_intact as (? & ?); eauto.
        * now constructor.
        * intros intact. destruct H.
          unfold contract_state in *.
          destruct (env_contract_states bstate_from to_addr); try discriminate.
          inversion H as [s_is_some_x]. rewrite deployed_state0 in s_is_some_x.
          inversion s_is_some_x as [cstate_eq_x].
          now subst.
      + apply trace_reachable in from_reachable.
        pose proof (no_self_calls bstate_from to_addr ltac:(assumption) ltac:(assumption))
             as all.
        unfold outgoing_acts in *.
        rewrite queue_prev in *.
        cbn in all.
        destruct_address_eq; cbn in *; auto.
        inversion_clear all as [|? ? hd _].
        destruct msg.
        * contradiction.
        * rewrite address_eq_refl in hd.
          congruence.
  Qed.

  Lemma balance_is_zero_when_smashed :
    forall (bstate : ChainState) caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      (cstate.(piggyState) = Smashed ->
      (env_account_balances bstate caddr = 0)%Z).
  Proof.
    intros * reach deployed act.
    edestruct balance_is_zero_when_smashed' as (cstate & deploy & balance); eauto.
    rewrite act, Z.sub_0_r in balance.
    exists cstate.
    split; eauto.
  Qed.

  Lemma balance_on_pos :
    forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      0 <= cstate.(balance).
  Proof.
    intros * reach deployed Hact.
    edestruct balance_on_chain as (cstate & balance); eauto.
    exists cstate.
    destruct balance as [H <-].
    split; auto.
    apply Z.ge_le.
    now apply account_balance_nonnegative.
  Qed.

  Definition serializeState state := (@serialize State _) state.

  Lemma smash_poss : forall bstate (reward : Amount) (caddr creator : Address),
    address_is_contract creator = false ->
    (reward >= 0)%Z ->
    reachable bstate ->
    emptyable (chain_state_queue bstate) ->
    (exists cstate,
      env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) /\
      env_contract_states bstate caddr = Some (serializeState cstate)) ->
        exists bstate',
          reachable_through bstate bstate' /\
          emptyable (chain_state_queue bstate') /\
          exists cstate',
            env_contracts bstate' caddr = Some (PiggyBank.contract : WeakContract) /\
            env_contract_states bstate' caddr = Some (serializeState cstate') /\
            (env_account_balances bstate' caddr = 0)%Z.
  Proof.
    intros * Hcreator Hreward bstate_reachable bstate_queue H.
    empty_queue H; destruct H as (cstate & contract_deployed & contract_state);
      (* Prove that H is preserved after transfers, discarding invalid actions, calling other contracts and deploying contracts *)
      only 3: destruct (address_eqdec caddr to_addr);
      try (now eexists; rewrite_environment_equiv; repeat split; eauto;
          cbn; destruct_address_eq; try easy).
    - (* Prove that H is preserved after calls to the contract *)
      subst.
      rewrite contract_deployed in deployed.
      inversion deployed. subst.
      rewrite contract_state in deployed_state.
      inversion deployed_state. subst.
      clear deployed_state deployed.
      apply wc_receive_strong in receive_some as
        (prev_state' & msg' & new_state' & serialize_prev_state & _ & serialize_new_state & receive_some).
      setoid_rewrite deserialize_serialize in serialize_prev_state.
      inversion serialize_prev_state. subst.
      exists new_state'.
      rewrite_environment_equiv; cbn; repeat split; eauto;
      cbn; destruct_address_eq; try easy.
    - update_all.
      (* Check if piggybank is already smashed *)
      destruct (is_smashed cstate) eqn:smashed.
      + (* Case: smashed *)
        (* In this case the balance should already be zero *)
        edestruct balance_is_zero_when_smashed as (cstate' & deploy & balance); eauto.
        * unfold outgoing_acts.
          now rewrite queue.
        * cbn in deploy.
          rewrite contract_state in deploy.
          unfold serializeState in deploy.
          rewrite deserialize_serialize in deploy.
          inversion deploy. subst. clear deploy.
          unfold is_smashed in smashed.
          destruct_match in smashed; try discriminate.
          exists bstate0.
          split; auto.
          split; try now rewrite queue.
          exists cstate'.
          split; auto.
      + (* Case: intact *)
        (* In this case we can smash the piggybank *)
        add_block [(build_act (owner cstate) (owner cstate) (act_call caddr 0 ((@serialize Msg _) Smash)))] 1%nat; eauto.
        admit.
        apply list.Forall_singleton, address_eq_refl.
        update_all.
        evaluate_action contract; try easy.
        * (* Prove that there is enough balance to evaluate action *)
          now apply account_balance_nonnegative.
        * (* Prove that receive action returns Some *)
          cbn; unfold address_neqb.
          rewrite address_eq_refl; cbn.
          rewrite smashed; cbn.
          eauto.
        * cbn in *.
          clear contract_state smashed.
          update_all.
          edestruct balance_on_chain' as (cstate' & deploy & balance); eauto.
          cbn in deploy.
          rewrite deployed_state in deploy.
          unfold serializeState in deploy.
          rewrite deserialize_serialize in deploy.
          inversion deploy. subst. clear deploy.
          cbn in balance.
          unfold outgoing_acts in balance.
          rewrite queue in balance.
          cbn in balance.
          rewrite address_eq_refl in balance.
          cbn in balance.
          specialize account_balance_nonnegative as H.
          apply H with (addr := caddr) in reach as balance_pos; clear H.
          rewrite !Z.add_0_r in balance.
          apply Zminus_eq in balance.
          
          (* Finally we need to evaluate the new transfer action that finalize produced *)
          evaluate_transfer; try easy.
          -- lia.
          -- lia.
          -- admit.
          -- update (env_account_balances bstate caddr = 0) in balance.
              { rewrite_environment_equiv. cbn. rewrite address_eq_refl.
                destruct_address_eq.
                admit.
                lia.
              }
              clear balance_pos.
              update_all. 
              exists bstate.
              split; auto.
              split; try now rewrite queue0.
              eexists.
              split; auto.
              split; eauto.
  Admitted.

End SafetyProperties.
