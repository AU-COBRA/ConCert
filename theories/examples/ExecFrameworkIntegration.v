(** * Integration with the execution framework, properties of [crowdfunding] *)
Require Import String Basics ZArith.
From ConCert Require Import Misc Notations PCUICtoTemplate
     PCUICTranslate CustomTactics.

From ConCert Require Import Crowdfunding CrowdfundingData SimpleBlockchain Prelude.

Require Import List.
Require Import PeanoNat.
Require Import Coq.ssr.ssrbool.
Require Import Morphisms.

From SmartContracts Require Import Blockchain Congress Automation.

Import ListNotations.

Open Scope list.

Import AcornBlockchain CrowdfundingContract CrowdfundingProperties.

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

Global Program Instance CB : ChainBase :=
  build_chain_base nat Nat.eqb _ _ _ _ Nat.odd. (* Odd addresses are addresses of contracts :) *)
Next Obligation.
  eapply NPeano.Nat.eqb_spec.
Defined.

Definition to_chain (sc : SimpleChain) : Chain :=
  let '(Build_chain h s fh ab) := sc in build_chain h s fh ab.

Definition of_chain (c : Chain) : SimpleChain :=
  let '(build_chain h s fh ab) := c in Build_chain h s fh ab.

Definition to_action_body (sab : SimpleActionBody) : ActionBody :=
  match sab with
  | Act_transfer addr x => act_transfer addr x
  end.

Definition to_contract_call_context (scc : SimpleContractCallContext) : ContractCallContext :=
  let '(Build_ctx from contr_addr am) := scc in build_ctx from contr_addr am.

Definition of_contract_call_context (cc : ContractCallContext) : SimpleContractCallContext :=
  let '(build_ctx from contr_addr am) := cc in Build_ctx from contr_addr am.

Definition of_state (st : State_coq) : Z * addr_map * nat * nat * bool * Z :=
  let '(mkState_coq b d o dl d' g):= st in (b,d,o,dl,d',g).

Definition to_state (p : Z * addr_map * nat * nat * bool * Z) :=
  let '(b,d,o,dl,d',g) := p in mkState_coq b d o dl d' g.

Lemma of_state_to_state p : of_state (to_state p) = p.
Proof. now destruct p. Qed.

Lemma to_state_of_state st : to_state (of_state st) = st.
Proof. now destruct st. Qed.

Import Serializable.

Section Serialize.

  Hint Rewrite to_list_of_list of_list_to_list : hints.
  Global Program Instance addr_map_serialize : Serializable addr_map :=
    {| serialize m := serialize (to_list m);
       deserialize l := option_map of_list (deserialize l); |}.
  Next Obligation.
    intros. cbn. rewrite deserialize_serialize. cbn.
    now autorewrite with hints.
  Defined.

    Global Program Instance State_serializable : Serializable State_coq :=
    {| serialize st := serialize (of_state st);
       deserialize p := option_map to_state (deserialize p); |}.
  Next Obligation.
    intros. cbn. rewrite deserialize_serialize. now destruct x.
  Defined.

  Definition of_msg (msg : Msg_coq) : unit + (unit + unit) :=
    match msg with
    | Donate_coq => inl tt
    | GetFunds_coq => inr (inl tt)
    | Claim_coq => (inr (inr tt))
    end.

  Definition to_msg (s : unit + (unit + unit)) : Msg_coq :=
    match s with
    | inl _ => Donate_coq
    | inr (inl _) => GetFunds_coq
    | inr (inr _) => Claim_coq
    end.

  Lemma of_msg_to_msg s : of_msg (to_msg s) = s.
  Proof. destruct s as [ | s'];try destruct s';destruct u;simpl;easy. Qed.

  Lemma to_msg_of_msg msg : to_msg (of_msg msg) = msg.
  Proof. destruct msg;easy. Qed.

  Global Program Instance Msg_serializable : Serializable Msg_coq :=
    {| serialize msg := serialize (of_msg msg);
       deserialize s := option_map to_msg (deserialize s); |}.
  Next Obligation.
    intros. cbn. rewrite deserialize_serialize. now destruct x.
  Defined.


End Serialize.

(** ** Wrappers *)
Section Wrappers.
  Definition Setup := (nat * Z)%type.

  Definition init_wrapper (f : SimpleContractCallContext -> nat -> Z -> State_coq):
    Chain (BaseTypes:=CB) -> ContractCallContext (BaseTypes:=CB) -> Setup -> option State_coq
    := fun c cc setup => Some (f (of_contract_call_context cc) (fst setup) (snd setup)).

  Definition wrapped_init
    : Chain -> ContractCallContext -> Setup -> option State_coq
    := init_wrapper Init.init.

    Definition receive_wrapper
             (f : SimpleChain ->
                  SimpleContractCallContext ->
                   Msg_coq -> State_coq -> option (State_coq * list SimpleActionBody)) :
    Chain -> ContractCallContext ->
    State_coq -> option Msg_coq -> option (State_coq * list ActionBody) :=
    fun ch cc st msg => match msg with
                       Some msg' => option_map (fun '(st0,acts) => (st0, map to_action_body acts)) (f (of_chain ch) (of_contract_call_context cc) msg' st)
                     | None => None
                     end.

  Definition wrapped_receive
    : Chain -> ContractCallContext -> State_coq -> option Msg_coq -> option (State_coq * list ActionBody)
    := receive_wrapper Receive.receive.

End Wrappers.

(** Taken from [Congress] *)
Ltac solve_contract_proper :=
  repeat
    match goal with
    | [ |- ?x _  = ?x _] => unfold x
    | [ |- ?x _ _ = ?x _ _] => unfold x
    | [ |- ?x _ _ _ = ?x _ _ _] => unfold x
    | [ |- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [ |- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [ |- ?x _ _ _ _ _ = ?x _ _ _ _ _] => unfold x
    | [ |- Some _ = Some _] => f_equal
    | [ |- pair _ _ = pair _ _] => f_equal
    | [ |- (if ?x then _ else _) = (if ?x then _ else _)] => destruct x
    | [ |- match ?x with | _ => _ end = match ?x with | _ => _ end ] => destruct x
    | [H: ChainEquiv _ _ |- _] => rewrite H in *
    | _ => subst; auto
    end.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) wrapped_init.
Proof. repeat intro; solve_contract_proper. Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) wrapped_receive.
Proof.
  repeat intro. unfold wrapped_receive,receive_wrapper.
  subst. destruct y2;auto.
  f_equal.
  unfold Receive.receive. destruct x,y;simpl in *.
  inversion H;cbn in *;subst.
  destruct m;solve_contract_proper.
Qed.

Definition cf_contract : Contract Setup Msg_coq State_coq :=
  build_contract wrapped_init init_proper wrapped_receive receive_proper.

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

Theorem cf_balance_consistent_deadline to contract state:
  reachable to ->
  env_contracts to contract = Some (cf_contract : WeakContract) ->
  cf_state to contract = Some state ->
  consistent_balance_deadline (Current_slot (of_chain to)) state.
Proof.
  intros Hr Hc Hst.
  cbn in *.
  assert (address_is_contract contract = true) as addr_format by now eapply contract_addr_format.
  unfold reachable in *. destruct Hr as [tr].
  remember empty_state eqn:eq.
  revert dependent state. revert dependent contract.
  induction tr as [ |? ? ? steps IH step];intros contract Hc Ha state Hst; subst;try solve_by_inversion.
  destruct_chain_step.
  + (* add new block *)
    cbn in *. intro H. unfold cf_state in *. rewrite env_eq in Hst. cbn in Hst.
    rewrite Current_slot_of_chain_eq in *.
    rewrite_environment_equiv.
    inversion valid_header.
    eapply IH;eauto.
    unfold deadline_passed in *. unfold is_true in *.
    rewrite Bool.negb_true_iff in *. leb_ltb_to_prop. cbn in *. lia.
  + (* Step *)
    remember (chain_state_env prev).
    destruct_action_eval; subst.
    * (* Transfer step *)
      rewrite_environment_equiv.
      unfold cf_state in *. cbn in *.
      intro H. eapply IH;eauto. rewrite Current_slot_of_chain_eq in *.
      inversion e2. erewrite current_slot_eq in H by eauto. easy.
    * (* Deployment *)
      simpl in *.
      rewrite_environment_equiv.
      cbn in *. unfold cf_state in *.
      cbn in *. unfold set_chain_contract_state in Hst.
      intro H. destruct ((contract =? to)%address) eqn:Heq.
      ** (* Executing the init method *)
         replace wc with (cf_contract : WeakContract) in * by congruence.
         cbn in e3. unfold Init.init in *. cbn in e3.
         unfold Monads.option_bind in *.
         destruct (deserialize setup);tryfalse. inversion e3;subst;clear e3.
         rewrite deserialize_serialize in Hst. inversion Hst. subst.
         easy.
      ** rewrite Current_slot_of_chain_eq in *.
         inversion e4. erewrite current_slot_eq in H by eauto.
         cbn in H.
         eapply IH;eauto.
    * (* Call *)
      rewrite_environment_equiv.
      destruct (address_eqb_spec contract to).
      ** (* To our contract, runs the [receive] function *)
        subst. cbn in *.
        replace wc with (cf_contract : WeakContract) in * by congruence.
        cbn in e3.
        unfold Monads.option_bind in e3.
        destruct (deserialize prev_state) as [p_local_state | ] eqn:Hps;tryfalse.
        destruct msg as [serialized_msg | ];tryfalse.
        destruct (deserialize serialized_msg) as [msg | ];tryfalse.
        destruct (option_map _ _) eqn:Hopt;tryfalse.
        destruct p as [local_state actions].
        inversion e3;subst;clear e3.
        unfold option_map in Hopt.
        destruct (Receive.receive _ _ _ _) eqn:Hreceive;tryfalse.
        destruct p. inversion Hopt. subst. clear Hopt.
        unfold cf_state in *.
        cbn in *. unfold set_chain_contract_state in Hst.
        replace (to =? to)%address with true in * by (symmetry;apply Nat.eqb_refl).
        rewrite deserialize_serialize in Hst. inversion Hst. subst.
        assert (Hprev_consistent: consistent_balance_deadline (Current_slot (of_chain prev)) p_local_state) by
            (eapply IH;eauto;now rewrite e1).
        remember (Build_ctx from to _) as ctx.

        (* we use one of the functional correctness properties here *)
        specialize (contract_backed _ ctx msg _ Hprev_consistent) as Hnew_consistent.
        destruct Hnew_consistent as [fin [out [Hrun Hcon]]].
        unfold run in Hrun.
        remember (Build_chain _ _ _ _) as ch.
        assert (Hreceive' : Receive.receive (of_chain prev) ctx msg p_local_state = Some (state, l0)).
        { destruct prev, chain_state_env,env_chain;cbn in *.
          subst. erewrite receive_blockchain_state;eauto. }
        rewrite Hreceive' in Hrun. inversion Hrun;subst.
        rewrite Current_slot_of_chain_eq in *.
        now rewrite_environment_equiv.
      ** (* Not to our contract *)
        cbn in *. unfold cf_state in *.
        cbn in *. unfold set_chain_contract_state in Hst.
        replace ((contract =? to)%address) with false in Hst by (symmetry;now apply Nat.eqb_neq).
        rewrite Current_slot_of_chain_eq in *.
        inversion e5. erewrite current_slot_eq by eauto.
        cbn in *.
        eapply IH;eauto.
  + (* Permute queue *)
    now rewrite prev_next in *.
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
  clear state_eq lstate.
  revert reachable deployed.
  apply lift_functional_correctness with (DeployFacts := fun _ _ => Coq.Init.Logic.True)
                                         (CallFacts := fun _ _ => Coq.Init.Logic.True).
  - now intros; destruct eval.
  - intros chain ctx setup result _ init H.
    cbn in *.
    inversion init.
    reflexivity.
  - intros chain ctx prev_state msg new_state new_acts _ prev_consistent receive.
    destruct msg as [msg| ]; cbn in *; try congruence.
    remember (of_chain _) as simple_chain.
    remember (of_contract_call_context _) as simple_ctx.
    destruct (contract_state_consistent simple_chain simple_ctx
                                          msg prev_state prev_consistent)
      as [fin [out [Hrun Hcon]]].
    unfold run in Hrun.
    destruct (Receive.receive _ _ _ _)
      as [[resp_state resp_acts]| ] eqn:Hreceive;tryfalse.
    cbn in *.
    now replace new_state with fin by congruence.
Qed.

Fixpoint sum_trans (addr : Blockchain.Address) (acts : list Blockchain.Action) : Z :=
  match acts with
  | nil => 0
  | cons a acts' => let '(build_act from abody) := a in
                   if (addr =? from)%address then
                     match abody with
                     | act_transfer _ v => (v + sum_trans addr acts')%Z
                     | act_call _ v _ => (v + sum_trans addr acts')%Z
                     | _ => sum_trans addr acts'
                     end
                   else sum_trans addr acts'
  end.

Lemma sum_trans_permute addr acts1 acts2 :
  Permutation.Permutation acts1 acts2 ->
  sum_trans addr acts1 = sum_trans addr acts2.
Proof.
  intros Hperm.
  induction Hperm.
  + easy.
  + destruct x;simpl;destruct_address_eq;destruct act_body;auto;lia.
  + destruct x;destruct y;simpl;destruct_address_eq;destruct act_body;destruct act_body0;lia.
  + easy.
Qed.

Lemma sum_trans_app acts1 acts2 addr :
  sum_trans addr (acts1 ++ acts2) = (sum_trans addr acts1 + sum_trans addr acts2)%Z.
Proof.
  revert acts2.
  induction acts1;intros;auto.
  destruct a;simpl in *.
  destruct ((_ =? _)%address);destruct act_body;auto;
    rewrite IHacts1;lia.
Qed.

Lemma act_is_from_account_sum_trans_0 queue caddr :
  address_is_contract caddr ->
  Forall act_is_from_account queue -> sum_trans caddr queue = 0%Z.
Proof.
  intros Hcontr Hfa.
  induction Hfa.
  + easy.
  + destruct x;simpl in *. inversion H.
    destruct ((caddr =? act_from)%address) eqn:Heq;destruct act_body;auto;
      rewrite Nat.eqb_eq in *;subst;tryfalse.
Qed.

Lemma not_in_queue_sum_trans_0 acts addr:
  Forall (fun act : Blockchain.Action => (act_from act =? addr)%address = false)
         acts ->
  sum_trans addr acts = 0%Z.
Proof.
  revert addr.
  induction acts;intros addr H.
  + easy.
  + destruct a;simpl in *.
    inversion H.  subst. cbn in *. rewrite address_eq_sym. rewrite H2.
    easy.
Qed.

Lemma sum_trans_before_deploy (bstate : ChainState) addr :
  reachable bstate ->
  address_is_contract addr = true ->
  env_contracts bstate addr = None ->
  sum_trans addr (chain_state_queue bstate) = 0%Z.
Proof.
  intros.
  assert (Forall (fun act : Blockchain.Action => (act_from act =? addr)%address = false)
                 (chain_state_queue bstate)) by (eapply undeployed_contract_no_out_queue;eauto).
  now eapply not_in_queue_sum_trans_0.
Qed.

Lemma undeployed_balance_0 (bstate : ChainState) addr :
  reachable bstate ->
  address_is_contract addr = true ->
  env_contracts bstate addr = None ->
  (account_balance bstate addr = 0%Z).
Proof.
  intros [trace] is_contract no_contract.
  rewrite (account_balance_trace _ trace); auto.
  rewrite undeployed_contract_no_out_txs, undeployed_contract_no_in_txs,
          contract_no_created_blocks; auto.
Qed.

Definition is_deploy (ac : ActionBody) : bool :=
  match ac with
  | act_transfer to amount => false
  | act_call to amount msg => false
  | act_deploy amount c setup => true
  end.

Definition is_call (ac : ActionBody) : bool :=
  match ac with
  | act_transfer to amount => false
  | act_call to amount msg => true
  | act_deploy amount c setup => false
  end.

Lemma cf_not_sending_deploy_or_call (bstate : ChainState) addr :
  reachable bstate ->
  env_contracts bstate addr = Some (cf_contract : WeakContract) ->
  Forall (fun act : Blockchain.Action => (~~ (act_from act =? addr)%address ||
          ~~ (is_deploy (act_body act) || is_call (act_body act))%address))
         (chain_state_queue bstate).
Proof.
  intros Hr Hc.
  assert (Haddr: address_is_contract addr = true) by eauto using contract_addr_format.
  unfold reachable in *. destruct Hr as [tr].
  remember empty_state eqn:eq.
  revert dependent addr.
  induction tr as [ |? ? ? steps IH step];intros addr Haddr Hc; subst;tryfalse.
  destruct_chain_step.
  + (* add new block *)
    rewrite_environment_equiv. cbn in *.
    eapply Forall_impl_inner. eapply acts_from_accs.
    eapply Forall_forall. intros x Hin Hacc.
    unfold act_is_from_account in Hacc.
    destruct_address_eq;subst; simpl in *;tryfalse;auto.
  + (* Step *)
    remember (chain_state_env prev).
    destruct_action_eval; subst.
    * (* Transfer step *)
      rewrite_environment_equiv. cbn in *.
      specialize_hypotheses.
      rewrite queue_prev in *.
      inversion IH;subst;eauto.
    * (* Deployment *)
      rewrite_environment_equiv. simpl in *.
      destruct_address_eq.
      ** subst. inversion Hc;subst.
         assert (H : Forall (fun act : Blockchain.Action => (act_from act =? to)%address = false)
                        (chain_state_queue prev)).
         { eapply undeployed_contract_no_out_queue;eauto. constructor;auto. }
         rewrite queue_prev in H. inversion H as [  | a ? ? H' ].
         eapply Forall_impl_inner. eapply H'.
         eapply Forall_forall. intros x Hin Heq. now rewrite Heq.
      ** specialize_hypotheses.
         rewrite queue_prev in *.
         inversion IH;easy.
    * (* Call *)
       rewrite_environment_equiv.
       subst.
       destruct (address_eqb_spec addr to).
      ** (* To our contract, runs the [receive] function *)
        subst. cbn in *.
        replace wc with (cf_contract : WeakContract) in * by congruence.
        cbn in e3.
        unfold Monads.option_bind in e3.
        destruct (deserialize prev_state) as [p_local_state | ] eqn:Hps;tryfalse.
        destruct msg as [serialized_msg | ];tryfalse.
        destruct (deserialize serialized_msg) as [msg | ];tryfalse.
        destruct (option_map _ _) eqn:Hopt;tryfalse.
        destruct p as [local_state actions].
        inversion e3;subst;clear e3.
        unfold option_map in Hopt.
        destruct (Receive.receive _ _ _ _) eqn:Hreceive;tryfalse.
        destruct p. inversion Hopt. subst. clear Hopt.
        destruct msg.
        *** (* donate *)
          simpl in *.
          destruct (_ <=? _);tryfalse;
          destruct (lookup_map _); inversion Hreceive; subst; simpl in *;
          specialize_hypotheses;rewrite queue_prev in IH;
          inversion IH;simpl in *;subst; easy.
        *** (* claim *)
          simpl in *.
          destruct (_ && _ && _);tryfalse.
          inversion Hreceive. subst. simpl in *.
          rewrite queue_new.
          specialize_hypotheses;rewrite queue_prev in IH;
            inversion IH;simpl in *;subst.
          constructor;simpl;auto. now rewrite address_eq_refl.
        *** simpl in *.
            destruct (_ && _ && _) eqn:Hcond;tryfalse.
            destruct (lookup_map _) eqn:Hlook;tryfalse.
            inversion Hreceive. subst.
            subst. simpl in *.
            rewrite queue_new.
            specialize_hypotheses;rewrite queue_prev in IH;
              inversion IH;simpl in *;subst.
            constructor;simpl;auto. now rewrite address_eq_refl.
      ** (* Not to our contract *)
        specialize_hypotheses;rewrite queue_prev in IH.
        inversion IH;simpl in *;subst.
        rewrite queue_new.
        apply utils.app_Forall.
        ***
        assert (Forall (fun a : Blockchain.Action => (act_from a =? addr)%address = false) (map (build_act to) resp_acts)) by now eapply new_acts_no_out_queue with (addr2:=to).
        eapply Forall_impl_inner. eapply H.
        eapply Forall_forall. intros x Hin Heq. now rewrite Heq.
        *** easy.
  + (* Permutation *)
    rewrite prev_next in *.
    eapply Extras.forall_respects_permutation;eauto.
Qed.

Lemma lookup_map_sum_map_leq m k z:
  map_forallb (Z.leb 0) m ->
  lookup_map m k = Some z ->
  (z <= sum_map m)%Z.
Proof.
  revert k z.
  induction m;intros k z0 Hsum Hlook;tryfalse.
  simpl in *. unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
  destruct Hsum as [H1 H2].
  destruct (k =? n).
  + simpl in *. inversion Hlook;subst.
    unfold is_true in *;repeat rewrite Bool.andb_true_iff in *.
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
  clear state_eq lstate.
  revert reachable deployed.
  apply lift_functional_correctness with
      (DeployFacts := fun _ _ => Coq.Init.Logic.True)
      (CallFacts := fun _ ctx => (0 <= Ctx_amount (of_contract_call_context ctx))%Z).
  - intros.
    destruct_action_eval; auto.
    cbn in *.
    lia.
  - intros chain ctx setup result _ init.
    inversion init.
    reflexivity.
  - intros chain ctx prev_state msg new_state new_acts nonnegative forall_prev receive.
    destruct msg as [msg| ]; cbn in *; try congruence.
    remember (of_chain _) as simple_chain.
    remember (of_contract_call_context _) as simple_ctx.
    destruct (contract_state_donation_non_neg
                simple_chain simple_ctx msg ltac:(auto) prev_state forall_prev)
      as [fin [out [Hrun Hcon]]].
    unfold run in Hrun.
    destruct (Receive.receive _ _ _ _) as [[resp_state resp_acts]| ]; tryfalse.
    cbn in *.
    now replace fin with new_state in * by congruence.
Qed.

Lemma cf_transfer_cases {sch sctx msg init fin acts}:
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
    destruct (_ <=? _);tryfalse.
    destruct (lookup_map _);
      inversion Hcall; tauto.
  + simpl in *.
    destruct (_ && _ && _);tryfalse.
    inversion Hcall; tauto.
  + simpl in *.
    destruct (_ && _ && _) eqn:Hcond;tryfalse.
    destruct (lookup_map _) eqn:Hlook;tryfalse.
    inversion Hcall. repeat rewrite Bool.andb_true_iff in *.
    destruct Hcond as [[? ?] Hdone].
    specialize (Hbalance Hdone).
    assert (z <= balance_coq init)%Z.
    { rewrite <- Hbalance. eapply lookup_map_sum_map_leq;eauto. }
    right. right. eexists;split;eauto.
Qed.

(** ** The actual contract balance is consistent with the local state *)
Theorem cf_backed bstate cf_addr lstate:
  let acts := chain_state_queue bstate in
  reachable bstate ->
  env_contracts bstate cf_addr = Some (cf_contract : WeakContract) ->
  cf_state bstate cf_addr = Some lstate ->
  (account_balance (env_chain bstate) cf_addr >= balance_coq lstate + sum_trans cf_addr acts)%Z.
Proof.
  cbn in *.
  intros Hr Hc Hst.
  assert (address_is_contract cf_addr = true) as addr_format by now eapply contract_addr_format.
  unfold reachable in *. destruct Hr as [tr].
  remember empty_state eqn:eq.
  revert dependent lstate. revert dependent cf_addr.
  induction tr as [ |? ? ? steps IH step];intros contract Hc Ha state Hst; subst;tryfalse.
  destruct_chain_step.
  + (* add new block *)
    cbn in *. intro H. unfold cf_state in *. rewrite env_eq in Hst. cbn in Hst.
    rewrite_environment_equiv.
    inversion valid_header. rewrite Z.compare_lt_iff in *. rewrite queue_prev in *.
    assert (Hsum : sum_trans contract (chain_state_queue next) = 0%Z) by
        now apply act_is_from_account_sum_trans_0.
    rewrite Hsum in H.
    eapply IH;simpl;eauto. rewrite Z.compare_lt_iff in *. cbn in *.
    unfold add_balance in *.
    destruct ((contract =? block_creator header)%address) eqn:Heq;lia.
  + (* Step *)
    remember (chain_state_env prev).
    destruct_action_eval; subst.
    * (* Transfer step *)
      rewrite_environment_equiv.
      cbn in *. unfold cf_state in *.
      cbn in *.
      intro H. eapply IH;eauto. rewrite Z.compare_lt_iff in *. cbn in *. unfold add_balance in *.
      rewrite queue_prev. simpl.
      inversion e2;subst.
      destruct_address_eq;tryfalse;lia.
    * (* Deployment *)
      simpl in *.
      rewrite_environment_equiv.
      cbn in *. unfold cf_state in *.
      cbn in *. unfold set_chain_contract_state in Hst.
      unfold add_balance in *.
      destruct_address_eq.
      ** subst to.
         remember (build_act _ _) as act.
         assert (act_from act <> contract) by
             (eapply undeployed_contract_not_from_self;try constructor;eauto).
         subst;cbn in *;tryfalse.
      ** (* Executing the init method *)
         replace wc with (cf_contract : WeakContract) in * by congruence.
         cbn in e3; unfold Init.init in *. cbn in e3.
         unfold Monads.option_bind in e3.
         destruct (deserialize setup);tryfalse. inversion e3;subst;clear e3.
         rewrite deserialize_serialize in Hst. inversion Hst. subst.
         cbn in *.
         assert (Htrans : sum_trans to (chain_state_queue prev)%Z = 0%Z).
         {  rewrite sum_trans_before_deploy;auto. constructor; auto. }
         rewrite queue_prev in Htrans. cbn in Htrans.
         destruct_address_eq;tryfalse.
         rewrite Htrans.
         replace (account_balance prev to) with 0%Z in * by
             (symmetry;eapply undeployed_balance_0;try constructor;eauto).
         lia.
      ** assert (H : Forall (fun act : Blockchain.Action => ~~ (act_from act =? contract)%address || ~~ (is_deploy (act_body act) || is_call (act_body act))) (chain_state_queue prev)) by
         (eapply cf_not_sending_deploy_or_call;try constructor;eauto).
         rewrite queue_prev in H. inversion H as [ | ? ? Hdeploy];subst;clear H.
         cbn in Hdeploy. rewrite address_eq_refl in Hdeploy;tryfalse.
      ** rewrite queue_prev in *. subst.
         specialize_hypotheses.
         simpl in *.
         now destruct_address_eq.
    * (* Call *)
      rewrite_environment_equiv.
      subst. simpl in *.
      unfold add_balance.
      destruct (address_eqb_spec contract to).
      ** (* To our contract, runs the [receive] function *)

        (* here goes a lot of boilerplate code *)
         subst. cbn in *.
         replace wc with (cf_contract : WeakContract) in * by congruence.
         cbn in e3.
         unfold Monads.option_bind in e3.
         destruct (deserialize prev_state) as [p_local_state | ] eqn:Hps;tryfalse.
         destruct msg as [serialized_msg | ];tryfalse.
         destruct (deserialize serialized_msg) as [msg | ];tryfalse.
         destruct (option_map _ _) eqn:Hopt;tryfalse.
         destruct p as [local_state actions].
         inversion e3;subst;clear e3.
         unfold option_map in Hopt.
         destruct (Receive.receive _ _ _ _) eqn:Hreceive;tryfalse.
         destruct p. inversion Hopt. subst. clear Hopt.
         unfold cf_state in *.
         cbn in *. unfold set_chain_contract_state in Hst.
         rewrite (address_eq_refl to) in *.
         rewrite deserialize_serialize in Hst. inversion Hst. subst.

         assert (Hconsistent : consistent_balance p_local_state).
         { (eapply cf_balance_consistent;eauto).
           constructor. auto. unfold cf_state. now rewrite e1.  }

         assert (Hpos : map_forallb (Z.leb 0) (donations_coq p_local_state)).
         { eapply crowfunding_donations_non_negative;eauto.
           constructor. auto. unfold cf_state. now rewrite e1. }
         specialize (cf_transfer_cases Hpos Hconsistent Hreceive) as cf_cases.
         destruct cf_cases as [H | [H | H]].
         *** (* donate *)
             destruct H as [H1 H2]. subst. simpl in *. unfold add_balance.
             rewrite queue_new. cbn.
             specialize (IH eq_refl to ltac:(auto) Ha p_local_state).
             rewrite e1 in IH. specialize_hypotheses.
             rewrite queue_prev in IH. cbn in IH.
             destruct (address_eqb_spec to from).
             **** rewrite <- H1. subst.
                  assert (H : Forall (fun act : Blockchain.Action => ~~ (act_from act =? from)%address || ~~ (is_deploy (act_body act) || is_call (act_body act))) (chain_state_queue prev)) by
                      (eapply cf_not_sending_deploy_or_call;try constructor;eauto).
                  rewrite queue_prev in H. inversion H;subst;cbn in *.
                  rewrite address_eq_refl in H3;tryfalse.
             **** subst;lia.
         *** (* get funds *)
             destruct H as [H1 H2]. subst. rewrite H1.
             simpl in *. unfold add_balance.
             rewrite queue_new. cbn.
             rewrite address_eq_refl.
             specialize (IH eq_refl to ltac:(auto) Ha p_local_state).
             rewrite e1 in IH. specialize_hypotheses.
             rewrite queue_prev in IH. cbn in IH.
             destruct (address_eqb_spec to from);subst;lia.
         *** (* claim *)
             destruct H as [z [H1 [H2 H3]]]. subst. rewrite H3.
             simpl in *. unfold add_balance.
             rewrite queue_new. cbn.
             rewrite address_eq_refl.
             specialize (IH eq_refl to ltac:(auto) Ha p_local_state).
             rewrite e1 in IH. specialize_hypotheses.
             rewrite queue_prev in IH. cbn in IH.
             destruct (address_eqb_spec to from);subst;lia.
      ** (* not to our contract *)
        cbn in *. unfold cf_state in *.
        cbn in *. unfold set_chain_contract_state in Hst.
        replace ((contract =? to)%address) with false in Hst by (symmetry;now apply Nat.eqb_neq).
        specialize_hypotheses.
        rewrite queue_prev in IH. cbn in IH.
        rewrite queue_new. cbn.
        assert (Forall (fun a : Blockchain.Action => (act_from a =? contract)%address = false) (map (build_act to) resp_acts)) by now eapply new_acts_no_out_queue with (addr2:=to).
        assert (Hsum0 : sum_trans contract (map (build_act to) resp_acts) = 0%Z) by now eapply not_in_queue_sum_trans_0.
        rewrite sum_trans_app.
        rewrite Hsum0.
        destruct (address_eqb_spec contract from).
        *** destruct msg;lia.
        *** lia.
  + (* Permute queue *)
    rewrite prev_next in *.
    specialize_hypotheses.
    erewrite <- sum_trans_permute;eauto.
Qed.


Corollary cf_backed_after_block {ChainBuilder : ChainBuilderType}
          prev hd acts new cf_addr lstate :
  builder_add_block prev hd acts = Some new ->
  env_contracts new cf_addr = Some (cf_contract : WeakContract) ->
  cf_state new cf_addr = Some lstate ->
  (account_balance (env_chain new) cf_addr >= balance_coq lstate)%Z.
Proof.
  intros Hnew Hcf Hst.
  destruct ChainBuilder;cbn in *.
  pose (builder_trace new) as tr.
  cbn in *.
  assert (Hr : reachable {| chain_state_env := builder_env new; chain_state_queue := [] |}) by
      (constructor;eauto).
  specialize (cf_backed _ _ _ Hr Hcf Hst) as Hbacked.
  cbn in *. lia.
Qed.

(** ** The actual contract balance is consistent the sum of individual contributions *)
Corollary cf_donations_backed_after_block {ChainBuilder : ChainBuilderType}
          prev hd acts new cf_addr lstate :
  builder_add_block prev hd acts = Some new ->
  env_contracts new cf_addr = Some (cf_contract : WeakContract) ->
  cf_state new cf_addr = Some lstate ->
  ~~ lstate.(done_coq) ->
  (account_balance (env_chain new) cf_addr >= sum_map (lstate.(donations_coq)))%Z.
Proof.
  intros Hnew Hcf Hst Hdone.
  destruct ChainBuilder;cbn in *.
  pose (builder_trace new) as tr.
  cbn in *.
  assert (Hr : reachable {| chain_state_env := builder_env new; chain_state_queue := [] |}) by
      (constructor;eauto).
  specialize (cf_balance_consistent _ _ _ Hr Hcf Hst Hdone) as Hconsistent.
  rewrite Hconsistent.
  specialize (cf_backed _ _ _ Hr Hcf Hst) as Hbacked.
  cbn in *. lia.
Qed.


Print Assumptions cf_backed.