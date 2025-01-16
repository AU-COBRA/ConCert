(** * Integration with the execution framework, properties of [crowdfunding] *)
From ConCert.Embedding Require Import Misc.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICtoTemplate.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Examples.Crowdfunding Require Import Crowdfunding.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingData.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingCorrect.

From Coq Require Import String.
From Coq Require Import Basics.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import ssrbool.
From Coq Require Import Program.Tactics.

From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.

Import ListNotations.

Open Scope list.

Import AcornBlockchain CrowdfundingContract CrowdfundingProperties.

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Global Program Instance CB : ChainBase :=
  build_chain_base nat Nat.eqb _ _ _ _ Nat.odd. (* Odd addresses are addresses of contracts :) *)
Next Obligation.
  eapply Nat.eqb_spec.
Defined.

Definition to_chain (sc : SimpleChain_coq) : Chain :=
  let '(Build_chain_coq h s fh) := sc in build_chain h s fh.

Definition of_chain (c : Chain) : SimpleChain_coq :=
  let '(build_chain h s fh) := c in Build_chain_coq h s fh.

Definition to_action_body (sab : SimpleActionBody_coq) : ActionBody :=
  match sab with
  | Act_transfer addr x => act_transfer addr x
  end.

Definition to_contract_call_context (scc : SimpleContractCallContext_coq) : ContractCallContext :=
  let '(Build_ctx_coq origin from contr_addr contr_bal am) := scc in
  build_ctx origin from contr_addr contr_bal am.

Definition of_contract_call_context (cc : ContractCallContext) : SimpleContractCallContext_coq :=
  let '(build_ctx origin from contr_addr contr_bal am) := cc in
  Build_ctx_coq origin from contr_addr contr_bal am.

Import Serializable Prelude.Maps.

Section Serialize.
  Hint Rewrite to_list_of_list of_list_to_list : hints.
  Global Program Instance addr_map_serialize : Serializable addr_map_coq :=
    {| serialize m := serialize (to_list m);
       deserialize l := option_map of_list (deserialize l); |}.
  Next Obligation.
    intros. cbn. rewrite deserialize_serialize. cbn.
    now autorewrite with hints.
  Defined.

  Global Instance State_serializable : Serializable State_coq :=
    Derive Serializable State_coq_rect<mkState_coq>.

  Global Instance Msg_serializable : Serializable Msg_coq :=
    Derive Serializable Msg_coq_rect<Donate_coq, GetFunds_coq, Claim_coq>.

End Serialize.

(** ** Wrappers *)
Section Wrappers.
  Definition Setup := (nat * Z)%type.

  Definition init_wrapper (f : SimpleContractCallContext_coq -> nat -> Z -> State_coq)
                          : Chain -> ContractCallContext -> Setup -> result State_coq unit :=
    fun c cc setup => Ok (f (of_contract_call_context cc) (fst setup) (snd setup)).

  Definition wrapped_init : Chain -> ContractCallContext -> Setup -> result State_coq unit :=
    init_wrapper Init.init.

  Definition receive_wrapper
             (f : SimpleChain_coq ->
                  SimpleContractCallContext_coq ->
                   Msg_coq -> State_coq -> option (State_coq * list SimpleActionBody_coq)) :
    Chain -> ContractCallContext ->
    State_coq -> option Msg_coq -> result (State_coq * list ActionBody) unit :=
    fun ch cc st msg =>
      match msg with
      | Some msg' =>
        let res := option_map (fun '(st0,acts) => (st0, map to_action_body acts))
                              (f (of_chain ch) (of_contract_call_context cc) msg' st) in
        result_of_option res tt
      | None => Err tt
      end.

  Definition wrapped_receive
            : Chain -> ContractCallContext -> State_coq -> option Msg_coq
             -> result (State_coq * list ActionBody) unit :=
    receive_wrapper Receive.receive.

End Wrappers.

Definition cf_contract : Contract Setup Msg_coq State_coq unit :=
  build_contract wrapped_init wrapped_receive.

Definition cf_state (env : Environment) (address : Blockchain.Address) : option State_coq :=
  match (env_contract_states env address) with
  | Some sv => deserialize sv
  | None => None
  end.

Import Lia.

Lemma Current_slot_of_chain_eq ch :
  Current_slot (of_chain ch) = current_slot ch.
Proof.
  now destruct ch.
Qed.

Theorem cf_balance_consistent_deadline bstate caddr lstate :
  reachable bstate ->
  env_contracts bstate caddr = Some (cf_contract : WeakContract) ->
  cf_state bstate caddr = Some lstate ->
  consistent_balance_deadline (Current_slot (of_chain bstate)) lstate.
Proof.
  intros Hr Hc.

  assert (Hreceive:
            forall chain ctx prev_state msg new_state new_acts,
              wrapped_receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
              consistent_balance_deadline (current_slot chain) prev_state ->
              consistent_balance_deadline (current_slot chain) new_state).
  {
    intros chain ctx prev_state msg new_state new_acts receive IH.
    destruct msg as [msg | ]; tryfalse; cbn in receive.
    destruct (Receive.receive _ _ _ _) as [[? ?] | ] eqn:Hreceive; tryfalse; cbn in *.
    specialize (contract_backed (of_chain chain) (of_contract_call_context ctx) msg)
      as Hnew_consistent.
    rewrite Current_slot_of_chain_eq in *.
    specialize (Hnew_consistent _ IH).
    destruct Hnew_consistent as [fin [out [Hrun Hcon]]].
    unfold run in Hrun.
    rewrite Hreceive in Hrun.
    replace new_state with fin by congruence.
    auto.
  }

  enough (H: exists lstate',
             cf_state bstate caddr = Some lstate' /\
             consistent_balance_deadline (Current_slot (of_chain bstate)) lstate').
  { intros. destruct H as [lstate' [? ?]].
    now replace lstate with lstate' by congruence. }

  rewrite Current_slot_of_chain_eq.

  contract_induction; intros; cbn in *; auto.
  - intro before_deadline.
    apply IH.
    instantiate (AddBlockFacts := fun _ old_slot _ _ new_slot _ => new_slot > old_slot);
      subst AddBlockFacts; cbn in facts.
    unfold deadline_passed in *. unfold is_true in *.
    rewrite Bool.negb_true_iff in *. propify. lia.
  - intros before_deadline.
    inversion_clear init_some.
    reflexivity.
  - eauto using Hreceive.
  - eauto using Hreceive.
  - instantiate (DeployFacts := fun _ _ => Logic.True).
    instantiate (CallFacts := fun _ _ _ _ _ => Logic.True).
    unset_all; subst; cbn in *.
    destruct_chain_step; auto.
    + inversion valid_header; lia.
    + destruct eval; auto.
Qed.

(** ** Contract balance in the local state consistent with the sum of individual contributions *)
Lemma cf_balance_consistent bstate cf_addr lstate :
  reachable bstate ->
  env_contracts bstate cf_addr = Some (cf_contract : WeakContract) ->
  cf_state bstate cf_addr = Some lstate ->
  consistent_balance lstate.
Proof.
  intros reachable deployed state_eq.
  enough (H: exists lstate',
             cf_state bstate cf_addr = Some lstate' /\
             consistent_balance lstate').
  { destruct H as [lstate' [lstate'_eq lstate'_consistent]].
    now replace lstate with lstate' by congruence. }
  contract_induction; intros; cbn in *; auto.
  - intro not_done.
    inversion_clear init_some.
    reflexivity.
  - destruct msg as [msg| ]; cbn in *; try congruence.
    remember (of_chain _) as simple_chain.
    remember (of_contract_call_context _) as simple_ctx.
    destruct (contract_state_consistent simple_chain simple_ctx
                                          msg prev_state IH)
      as [fin [out [Hrun Hcon]]].
    unfold run in Hrun.
    destruct (Receive.receive _ _ _ _)
      as [[resp_state resp_acts]| ] eqn:Hreceive; tryfalse.
    cbn in *.
    now replace new_state with fin by congruence.
  - destruct msg as [msg| ]; cbn in *; try congruence.
    remember (of_chain _) as simple_chain.
    remember (of_contract_call_context _) as simple_ctx.
    destruct (contract_state_consistent simple_chain simple_ctx
                                          msg prev_state IH)
      as [fin [out [Hrun Hcon]]].
    unfold run in Hrun.
    destruct (Receive.receive _ _ _ _)
      as [[resp_state resp_acts]| ] eqn:Hreceive; tryfalse.
    cbn in *.
    now replace new_state with fin by congruence.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => Logic.True).
    instantiate (DeployFacts := fun _ _ => Logic.True).
    instantiate (CallFacts := fun _ _ _ _ _ => Logic.True).
    unset_all; subst.
    destruct step; auto.
    destruct a; auto.
Qed.

Lemma undeployed_balance_0 (bstate : ChainState) addr :
  reachable bstate ->
  address_is_contract addr = true ->
  env_contracts bstate addr = None ->
  (env_account_balances bstate addr = 0%Z).
Proof.
  intros [trace] is_contract no_contract.
  rewrite (account_balance_trace _ trace); auto.
  rewrite undeployed_contract_no_out_txs, undeployed_contract_no_in_txs,
          contract_no_created_blocks; auto.
Qed.

Lemma cf_not_sending_deploy_or_call (bstate : ChainState) addr :
  reachable bstate ->
  env_contracts bstate addr = Some (cf_contract : WeakContract) ->
  Forall (fun a => ~~is_deploy a && ~~is_call a) (outgoing_acts bstate addr).
Proof.
  assert (receive_only_transfer:
            forall chain ctx cstate msg new_cstate acts,
              wrapped_receive chain ctx cstate msg = Ok (new_cstate, acts) ->
              Forall (fun a => ~~ is_deploy a && ~~ is_call a) acts).
  {
    intros ? ? ? ? ? ? receive_some.
    destruct msg as [msg | ]; tryfalse; cbn in *.
    destruct (Receive.receive _ _ _ _) as [[? ?] | ] eqn:Hreceive; tryfalse; cbn in *.
    replace acts with (map to_action_body l) by congruence.
    destruct msg.
    + (* donate *)
      cbn in *.
      destruct_match in Hreceive; tryfalse.
      destruct_match in Hreceive; inversion_clear Hreceive; cbn; easy.
    + (* get_funds *)
      cbn in *.
      destruct_match in Hreceive; tryfalse.
      inversion_clear Hreceive.
      cbn.
      auto.
    + (* claim *)
      cbn in *.
      destruct_match in Hreceive; tryfalse.
      destruct_match in Hreceive; tryfalse.
      inversion_clear Hreceive.
      cbn.
      auto.
  }

  intros Hr Hc.
  contract_induction; intros; cbn in *; auto.
  - inversion_clear IH; auto.
  - apply Forall_app.
    split; auto.
    eauto using receive_only_transfer.
  - apply Forall_app.
    inversion_clear IH.
    split; auto.
    eauto using receive_only_transfer.
  - now rewrite <- perm.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => Logic.True).
    instantiate (DeployFacts := fun _ _ => Logic.True).
    instantiate (CallFacts := fun _ _ _ _ _ => Logic.True).
    unset_all; subst.
    destruct step; auto.
    destruct a; auto.
Qed.

Local Open Scope nat.
Lemma lookup_map_sum_map_leq m k z :
  map_forallb (Z.leb 0) m ->
  lookup_map m k = Some z ->
  (z <= sum_map m)%Z.
Proof.
  revert k z.
  induction m; intros k z0 Hsum Hlook; tryfalse.
  simpl in *. unfold is_true in *; repeat rewrite Bool.andb_true_iff in *.
  destruct Hsum as [H1 H2].
  destruct (k =? n).
  + simpl in *. inversion Hlook; subst.
    unfold is_true in *; repeat rewrite Bool.andb_true_iff in *.
    rewrite <- Zle_is_le_bool in *.
    assert (sum_map m >=0)%Z by now eapply all_non_neg_sum_map. lia.
  + specialize_hypotheses.
    assert (sum_map m >=0)%Z by now eapply all_non_neg_sum_map.
    rewrite <- Zle_is_le_bool in *.
    lia.
Qed.

Lemma crowfunding_donations_non_negative bstate cf_addr lstate :
  reachable bstate ->
  env_contracts bstate cf_addr = Some (cf_contract : WeakContract) ->
  cf_state bstate cf_addr = Some lstate ->
  donations_non_neg lstate.
Proof.
  intros reachable deployed state_eq.
  enough (H: exists lstate',
             cf_state bstate cf_addr = Some lstate' /\
             donations_non_neg lstate').
  { destruct H as [lstate' [lstate'_eq lstate'_consistent]].
    now replace lstate with lstate' by congruence. }

  contract_induction; intros; cbn in *; auto.
  - inversion_clear init_some.
    reflexivity.
  - destruct msg as [msg| ]; cbn in *; try congruence.
    instantiate
      (CallFacts := fun _ ctx _ _ _ => (0 <= Ctx_amount (of_contract_call_context ctx))%Z);
      subst CallFacts; cbn in *.
    remember (of_chain _) as simple_chain.
    remember (of_contract_call_context _) as simple_ctx.
    destruct (contract_state_donation_non_neg
                simple_chain simple_ctx msg ltac:(auto) prev_state IH)
      as [fin [out [Hrun Hcon]]].
    unfold run in Hrun.
    destruct (Receive.receive _ _ _ _) as [[resp_state resp_acts]| ]; tryfalse.
    cbn in *.
    now replace fin with new_state in * by congruence.
  - destruct msg as [msg| ]; cbn in *; try congruence.
    subst CallFacts; cbn in *.
    remember (of_chain _) as simple_chain.
    remember (of_contract_call_context _) as simple_ctx.
    destruct (contract_state_donation_non_neg
                simple_chain simple_ctx msg ltac:(auto) prev_state IH)
      as [fin [out [Hrun Hcon]]].
    unfold run in Hrun.
    destruct (Receive.receive _ _ _ _) as [[resp_state resp_acts]| ]; tryfalse.
    cbn in *.
    now replace fin with new_state in * by congruence.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => Logic.True).
    instantiate (DeployFacts := fun _ _ => Logic.True).
    unset_all; subst; cbn in *.
    destruct step; auto.
    destruct a; auto.
    intros; lia.
Qed.

Lemma cf_transfer_cases {sch sctx msg init fin acts} :
  map_forallb (Z.leb 0) (donations_coq init) ->
  consistent_balance init ->
  Receive.receive sch sctx msg init = Some (fin, acts) ->

  ((Ctx_amount sctx + init.(balance_coq) = fin.(balance_coq))%Z /\ acts = [])

  \/ ((fin.(balance_coq) = 0%Z) /\ acts = [Act_transfer (Ctx_from sctx) init.(balance_coq)])

  \/ (exists v, acts = [Act_transfer sctx.(Ctx_from) v] /\
          (v <= init.(balance_coq))%Z /\ (fin.(balance_coq) = init.(balance_coq) - v)%Z).
Proof.
  intros Hpos Hbalance Hcall.
  destruct msg eqn:Hmsg.
  + simpl in *.
    destruct (_ <=? _); tryfalse.
    destruct (lookup_map _);
      inversion Hcall; tauto.
  + simpl in *.
    destruct (_ && _ && _); tryfalse.
    inversion Hcall; tauto.
  + simpl in *.
    destruct (_ && _ && _) eqn:Hcond; tryfalse.
    destruct (lookup_map _) eqn:Hlook; tryfalse.
    inversion Hcall. repeat rewrite Bool.andb_true_iff in *.
    destruct Hcond as [[? ?] Hdone].
    specialize (Hbalance Hdone).
    assert (z <= balance_coq init)%Z.
    { rewrite <- Hbalance. eapply lookup_map_sum_map_leq; eauto. }
    right. right. eexists; split; eauto.
Qed.

Local Open Scope Z.
#[local]
Hint Resolve cf_balance_consistent crowfunding_donations_non_negative : core.
(** ** The actual contract balance is consistent with the local state *)
Theorem cf_backed bstate cf_addr lstate :
  let acts := chain_state_queue bstate in
  reachable bstate ->
  env_contracts bstate cf_addr = Some (cf_contract : WeakContract) ->
  cf_state bstate cf_addr = Some lstate ->
  (env_account_balances bstate cf_addr >=
   balance_coq lstate + sumZ act_body_amount (outgoing_acts bstate cf_addr)).
Proof.
  cbn in *.
  intros is_reachable is_deployed.
  revert lstate.
  enough (H: exists lstate',
             cf_state bstate cf_addr = Some lstate' /\
             (env_account_balances bstate cf_addr >=
              balance_coq lstate' + sumZ act_body_amount (outgoing_acts bstate cf_addr))).
  { intros. destruct H as [lstate' [? ?]].
    now replace lstate with lstate' by congruence. }
  contract_induction; intros; cbn in *; auto.
  - inversion_clear init_some.
    cbn.
    instantiate (DeployFacts := fun _ ctx => ctx_amount ctx >= 0);
      subst DeployFacts; cbn in *.
    lia.
  - lia.
  - destruct msg as [msg| ]; tryfalse.
    cbn in receive_some.
    destruct (Receive.receive _ _ _ _) as [[? ?]| ] eqn:Hreceive; tryfalse.
    cbn in receive_some.
    replace s with new_state in * by congruence.
    replace new_acts with (map to_action_body l) in * by congruence.

    instantiate (CallFacts := fun _ ctx cstate _ _ => ctx_amount ctx >= 0 /\
                                        consistent_balance cstate /\
                                        donations_non_neg cstate);
      subst CallFacts; cbn in *.
    destruct facts as [Hamt_non_neg [Hconsistent Hpos]].
    specialize (cf_transfer_cases Hpos Hconsistent Hreceive) as cf_cases.
    clear receive_some Hreceive.
    destruct cf_cases as [H | [H | H]].
    + (* donate *)
      destruct H; subst; cbn in *.
      replace (Ctx_amount (of_contract_call_context ctx)) with (ctx_amount ctx)
        in * by (now destruct ctx).
      lia.
    + (* get funds *)
      destruct H; subst; cbn in *.
      lia.
    + (* claim *)
      destruct H as [? [? [? ?]]]; subst; cbn in *.
      lia.
  - destruct msg as [msg| ]; tryfalse.
    cbn in receive_some.
    destruct (Receive.receive _ _ _ _) as [[? ?]| ] eqn:Hreceive; tryfalse.
    cbn in receive_some.
    replace s with new_state in * by congruence.
    replace new_acts with (map to_action_body l) in * by congruence.

    subst CallFacts; cbn in *.
    destruct facts as [Hamt_non_neg [Hconsistent Hpos]].
    specialize (cf_transfer_cases Hpos Hconsistent Hreceive) as cf_cases.
    clear receive_some Hreceive.
    destruct head; try solve [destruct_conjs; congruence].
    destruct cf_cases as [H | [H | H]].
    + (* donate *)
      destruct H; subst; cbn in *.
      replace (Ctx_amount (of_contract_call_context ctx)) with (ctx_amount ctx)
        in * by (now destruct ctx).
      cbn in *.
      lia.
    + (* get funds *)
      destruct H; subst; cbn in *.
      lia.
    + (* claim *)
      destruct H as [? [? [? ?]]]; subst; cbn in *.
      lia.
  - now rewrite <- perm.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => Logic.True);
      unset_all; subst; cbn in *.
    destruct step; auto.
    destruct a; auto.
    intros.
    apply trace_reachable in from_reachable.
    split; eauto.
Qed.

Corollary cf_backed_after_block {ChainBuilder : ChainBuilderType}
          prev hd acts new cf_addr lstate :
  builder_add_block prev hd acts = Ok new ->
  env_contracts new cf_addr = Some (cf_contract : WeakContract) ->
  cf_state new cf_addr = Some lstate ->
  (env_account_balances new cf_addr >= balance_coq lstate)%Z.
Proof.
  intros Hnew Hcf Hst.
  destruct ChainBuilder; cbn in *.
  pose (builder_trace new) as tr.
  cbn in *.
  assert (Hr : reachable {| chain_state_env := builder_env new; chain_state_queue := [] |}) by
      (constructor; eauto).
  specialize (cf_backed _ _ _ Hr Hcf Hst) as Hbacked.
  cbn in *. lia.
Qed.

(** ** The actual contract balance is consistent with the sum of individual contributions *)
Corollary cf_donations_backed_after_block {ChainBuilder : ChainBuilderType}
          prev hd acts new cf_addr lstate :
  builder_add_block prev hd acts = Ok new ->
  env_contracts new cf_addr = Some (cf_contract : WeakContract) ->
  cf_state new cf_addr = Some lstate ->
  ~~ lstate.(done_coq) ->
  (env_account_balances new cf_addr >= sum_map (lstate.(donations_coq)))%Z.
Proof.
  intros Hnew Hcf Hst Hdone.
  destruct ChainBuilder; cbn in *.
  pose (builder_trace new) as tr.
  cbn in *.
  assert (Hr : reachable {| chain_state_env := builder_env new; chain_state_queue := [] |}) by
      (constructor; eauto).
  specialize (cf_balance_consistent _ _ _ Hr Hcf Hst Hdone) as Hconsistent.
  rewrite Hconsistent.
  specialize (cf_backed _ _ _ Hr Hcf Hst) as Hbacked.
  cbn in *. lia.
Qed.
