Require Import String ZArith.
From ConCert Require Import TCTranslate ExecFrameworkExamples CustomTactics.
Require Import List.
Require Import PeanoNat.
Require Import Coq.ssr.ssrbool.
Require Import Morphisms.

From SmartContracts Require Import Blockchain Congress Automation.
(* From RecordUpdate Require Import RecordUpdate. *)
Import ListNotations.
Open Scope list.

Import AcornBlockchain CrowdfundingContract.

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

(* Taken from [Congress], because otherwise it is not visible after import *)
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

Import FunctionalExtensionality.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) wrapped_init.
Proof. repeat intro; solve_contract_proper. Qed.

Lemma of_chain_proper :
  Proper (ChainEquiv ==> eq) of_chain.
Proof. repeat intro. unfold of_chain. destruct x,y;cbn in *. inversion H.
       cbn in *;subst. f_equal. now apply functional_extensionality.
Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) wrapped_receive.
Proof.
  repeat intro. unfold wrapped_receive,receive_wrapper.
  subst. destruct y2;auto.
  f_equal.
  (* TODO : chnage this to avoid funext *)
  (* unfold Receive.receive. repeat solve_contract_proper. *)
  f_equal. destruct x,y;solve_contract_proper;cbn.
  inversion H.
  cbn in *;subst. solve_contract_proper. solve_contract_proper. f_equal.
  now apply functional_extensionality.
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

Theorem crowdfunding_balance_consistent to contract state:
  reachable to ->
  env_contracts to contract = Some (cf_contract : WeakContract) ->
  cf_state to contract = Some state ->
  consistent_balance (Current_slot (of_chain to)) state.
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
    destruct_action_eval; subst pre; cbn [eval_tx].
    * (* Transfer step *)
      rewrite_environment_equiv.
      cbn in *. unfold cf_state in *. erewrite contract_states_eq in Hst by eauto.
      cbn in *.
      intro H. eapply IH;eauto. rewrite Current_slot_of_chain_eq in *.
      inversion e2. erewrite current_slot_eq in H by eauto. easy.
    * (* Deployment *)
      simpl in *.
      rewrite_environment_equiv.
      cbn in *. unfold cf_state in *. erewrite contract_states_eq in Hst by eauto.
      cbn in *. unfold set_chain_contract_state in Hst.
      intro H. destruct ((contract =? to)%address) eqn:Heq.
      ** (* Executing the init method *)
         replace wc with (cf_contract : WeakContract) in * by congruence.
         cbn in e3. unfold Init.init in *. cbn in e3.
         unfold Monads.option_bind in e3.
         destruct (deserialize setup);tryfalse. inversion e3;subst;clear e3.
         rewrite deserialize_serialize in Hst. inversion Hst. subst.
         easy.
      ** rewrite Current_slot_of_chain_eq in *.
         inversion e4. erewrite current_slot_eq in H by eauto.
         cbn in H.
         eapply IH;eauto.
    * (* Call *)
      rewrite_environment_equiv.
      subst new_acts.
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
        inversion e3. subst;clear e3.
        unfold option_map in Hopt.
        destruct (Receive.receive _ _ _ _) eqn:Hreceive;tryfalse.
        destruct p. inversion Hopt. subst. clear Hopt.
        unfold cf_state in *. erewrite contract_states_eq in Hst by eauto.
        cbn in *. unfold set_chain_contract_state in Hst.
        rewrite Nat.eqb_refl in Hst.
        rewrite deserialize_serialize in Hst. inversion Hst. subst.
        assert (Hprev_consistent: consistent_balance (Current_slot (of_chain prev)) p_local_state) by
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
        cbn in *. unfold cf_state in *. erewrite contract_states_eq in Hst by eauto.
        cbn in *. unfold set_chain_contract_state in Hst.
        replace ((contract =? to)%address) with false in Hst by (symmetry;now apply Nat.eqb_neq).
        rewrite Current_slot_of_chain_eq in *.
        inversion e5. erewrite current_slot_eq by eauto.
        cbn in *.
        eapply IH;eauto.
  + (* Permute queue *)
    now rewrite prev_next in *.
Qed.

Theorem crowdfunding_balance_consistent_done to contract state:
  reachable to ->
  env_contracts to contract = Some (cf_contract : WeakContract) ->
  cf_state to contract = Some state ->
  consistent_balance_done state.
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
    rewrite_environment_equiv.
    inversion valid_header.
    eapply IH;eauto.
  + (* Step *)
    remember (chain_state_env prev).
    destruct_action_eval; subst pre; cbn [eval_tx].
    * (* Transfer step *)
      rewrite_environment_equiv.
      cbn in *. unfold cf_state in *. erewrite contract_states_eq in Hst by eauto.
      cbn in *.
      intro H. eapply IH;eauto.
    * (* Deployment *)
      simpl in *.
      rewrite_environment_equiv.
      cbn in *. unfold cf_state in *. erewrite contract_states_eq in Hst by eauto.
      cbn in *. unfold set_chain_contract_state in Hst.
      intro H. destruct ((contract =? to)%address) eqn:Heq.
      ** (* Executing the init method *)
         replace wc with (cf_contract : WeakContract) in * by congruence.
         cbn in e3. unfold Init.init in *. cbn in e3.
         unfold Monads.option_bind in e3.
         destruct (deserialize setup);tryfalse. inversion e3;subst;clear e3.
         rewrite deserialize_serialize in Hst. inversion Hst. subst.
         easy.
      ** eapply IH;eauto.
    * (* Call *)
      rewrite_environment_equiv.
      subst new_acts.
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
        inversion e3. subst;clear e3.
        unfold option_map in Hopt.
        destruct (Receive.receive _ _ _ _) eqn:Hreceive;tryfalse.
        destruct p. inversion Hopt. subst. clear Hopt.
        unfold cf_state in *. erewrite contract_states_eq in Hst by eauto.
        cbn in *. unfold set_chain_contract_state in Hst.
        rewrite Nat.eqb_refl in Hst.
        rewrite deserialize_serialize in Hst. inversion Hst. subst.
        assert (Hprev_consistent: consistent_balance_done p_local_state) by
            (eapply IH;eauto;now rewrite e1).
        remember (Build_ctx from to _) as ctx.
        remember (Build_chain _ _ _ _) as ch.

        (* we use one of the functional correctness properties here *)
        specialize (contract_state_consistent ch ctx msg _ Hprev_consistent) as Hnew_consistent.
        destruct Hnew_consistent as [fin [out [Hrun Hcon]]].
        unfold run in Hrun.
        rewrite Hreceive in Hrun. now inversion Hrun;subst.
      ** (* Not to our contract *)
        cbn in *. unfold cf_state in *. erewrite contract_states_eq in Hst by eauto.
        cbn in *. unfold set_chain_contract_state in Hst.
        replace ((contract =? to)%address) with false in Hst by (symmetry;now apply Nat.eqb_neq).
        eapply IH;eauto.
  + (* Permute queue *)
    now rewrite prev_next in *.
Qed.
