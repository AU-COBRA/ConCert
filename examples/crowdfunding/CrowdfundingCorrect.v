(** We develop a deep embedding of a crowdfunding contract and prove some of its
     functional correctness properties using the corresponding shallow embedding *)

From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import Prelude.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingData.
From ConCert.Examples.Crowdfunding Require Import Crowdfunding.
From ConCert.Utils Require Import Automation.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import ssrbool.
From Coq Require Import Lia.

Import ListNotations.
Import Prelude.Maps.
Import CrowdfundingContract.

(** * Properties of the crowdfunding contract *)

Module CrowdfundingProperties.
  Import AcornBlockchain.
  Ltac inv_andb H := apply Bool.andb_true_iff in H; destruct H.
  Ltac split_andb := apply Bool.andb_true_iff; split.

  Open Scope nat.
  Open Scope bool.

  Definition deadline_passed now (s : State_coq) := s.(deadline_coq) <? now.

  Definition goal_reached (s : State_coq) := (s.(goal_coq) <=? s.(balance_coq))%Z.

  Definition funded now (s : State_coq) :=
    deadline_passed now s && goal_reached s.

  Lemma not_leb n m : ~~ (n <=? m) -> m <? n.
  Proof.
   intros.
   unfold Nat.ltb in *.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Nat.leb_gt in *. rewrite Nat.leb_le in *. lia.
  Qed.

  Lemma not_ltb n m : ~~ (n <? m) -> m <=? n.
  Proof.
   intros.
   unfold Nat.ltb in *.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Nat.leb_gt in *. rewrite Nat.leb_le in *. lia.
  Qed.


  Lemma Znot_leb n m : ~~ (n <=? m)%Z -> (m <? n)%Z.
  Proof.
   intros.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Z.leb_gt in *. now rewrite Z.ltb_lt in *.
  Qed.

  Lemma Znot_ltb n m : ~~ (n <? m)%Z -> (m <=? n)%Z.
  Proof.
   intros.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Z.ltb_nlt in *. rewrite Z.leb_le in *. lia.
  Qed.

  (** This lemma states that the only relevant part of the blockchain state is the current slot,
      because we check if the deadline have passed by comparing the deadline recorded in the
      internal state with the current slot number.*)
  Lemma receive_blockchain_state height1 height2 cur_slot fheight1 fheight2 msg st ctx :
    Receive.receive (Build_chain_coq height1 cur_slot fheight1) ctx msg st =
    Receive.receive (Build_chain_coq height2 cur_slot fheight2) ctx msg st.
  Proof.
    destruct msg;
      simpl;
      (match goal with
       | [ |- context[(if ?x then _ else _ )] ] => destruct x eqn:Hx
       end); eauto.
  Qed.

  (** This function is a simplistic execution environment that performs one step of execution *)
  Definition run (receive : State_coq -> option (State_coq * list SimpleActionBody_coq)) (init : State_coq)
    : State_coq * list SimpleActionBody_coq :=
    match receive init with
    | Some (fin, out) => (fin, out)
    | None => (init, []) (* if an error occurs, the state remains the same *)
    end.

  (** A wrapper for the assertions about the contract execution *)
  Definition assertion (pre : State_coq -> Prop)
             (entry : State_coq -> option (State_coq * list SimpleActionBody_coq))
             (post : State_coq -> list SimpleActionBody_coq -> Prop) :=
    forall init, pre init -> exists fin out, run entry init = (fin, out) /\ post fin out.

  Notation "{{ P }} c {{ Q }}" := (assertion P c Q)( at level 50).


  (** The donations can be paid back to the backers if the goal is not
      reached within a deadline *)

  Lemma get_money_back_guarantee CallCtx BC (sender := CallCtx.(Ctx_from)) v :
      (* pre-condition *)
      {{ fun init =>
         deadline_passed BC.(Current_slot) init
       /\ ~~ (goal_reached init)
       /\ ~~ init.(done_coq)
       /\ lookup_map init.(donations_coq) sender = Some v }}

        (* contract call *)
       Receive.receive BC CallCtx Claim_coq

       (* post-condition *)
       {{fun fin out => lookup_map fin.(donations_coq) sender = Some 0%Z
         /\ In (Act_transfer sender v) out}}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hdl [Hgoal [Hndone Hlook]]].
    unfold deadline_passed,goal_reached in *; simpl in *.
    repeat eexists. unfold run. simpl.
    assert (balance_coq init <? goal_coq init = true)%Z by now apply Znot_leb.
    repeat destruct (_ <? _)%Z; tryfalse. destruct (_ <? _); tryfalse.
    destruct (~~ done_coq _)%bool; tryfalse.
    destruct (lookup_map _ _); tryfalse; inversion Hlook; subst; clear Hlook.
    repeat split; cbn. apply lookup_map_add. now constructor.
  Qed.

  (** New donations are recorded correctly in the contract's state *)

  Lemma new_donation_correct CallCtx BC (sender := CallCtx.(Ctx_from))
        (donation := CallCtx.(Ctx_amount)) :

    {{ fun init =>
          sender ∉ init.(donations_coq) (* the sender have not donated before *)
       /\ ~~ deadline_passed BC.(Current_slot) init }}

      (* contract call *)
    Receive.receive BC CallCtx Donate_coq

    {{ fun fin out =>
         (* nothing gets transferred *)
         out = []
         (* donation has been accepted *)
         /\ lookup_map fin.(donations_coq) sender = Some donation }}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hnew_sender Hdl].
    unfold deadline_passed in *; simpl in *.
    unfold run.
    repeat eexists.
    simpl in *. apply not_ltb in Hdl.
    destruct (_ <=? _); tryfalse.
    unfold inmap_map in *.
    destruct (lookup_map _ _); tryfalse.
    repeat split; eauto. simpl. now rewrite lookup_map_add.
  Qed.


  (** Existing donations are updated correctly in the contract's state *)

  Lemma existing_donation_correct BC CallCtx (sender := CallCtx.(Ctx_from))
        (new_don := CallCtx.(Ctx_amount)) old_don :
    {{ fun init =>
         (* the sender has already donated before *)
         lookup_map init.(donations_coq) sender = Some old_don

       /\ ~~ deadline_passed BC.(Current_slot) init }}

     Receive.receive BC CallCtx Donate_coq

    {{ fun fin out =>
         (* nothing gets transferred *)
         out = []
         (* donation has been added *)
       /\ lookup_map fin.(donations_coq) sender = Some (old_don + new_don)%Z }}.
  Proof.
    unfold assertion. intros init H. simpl.
    subst sender new_don.
    destruct H as [Hsender Hdl].
    unfold deadline_passed in *; simpl in *.
    subst; simpl in *.
    eexists. eexists.
    unfold run. simpl in *. apply not_ltb in Hdl.
    destruct (_ <=? _); tryfalse.
    destruct (lookup_map _ _); tryfalse.
    inversion Hsender; subst.
    repeat split; simpl; eauto. now rewrite lookup_map_add.
  Qed.

  Fixpoint sum_map (m : addr_map_coq) : Z :=
    match m with
    | mnil => 0
    | mcons _ v m' => v + sum_map m'
    end.

  Lemma all_non_neg_sum_map m :
    map_forallb (Z.leb 0) m ->
    (sum_map m >= 0)%Z.
  Proof.
    intros H.
    induction m.
    + simpl; lia.
    + simpl in *. inv_andb H.
      specialize (IHm H0). propify. lia.
  Qed.

  Lemma sum_map_add_in m : forall n0 (v' v : Z) k,
      lookup_map m k = Some n0 ->
      sum_map m = v ->
      sum_map (add_map k (n0+v') m) = (v' + v)%Z.
  Proof.
    intros; subst.
    revert dependent n0. revert v' k.
    induction m; intros; subst.
    + inversion H.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * simpl in *. inversion H. subst. lia.
      * simpl in *. rewrite IHm; auto. lia.
  Qed.

  Lemma sum_map_add_not_in m : forall v' v k,
      lookup_map m k = None ->
      sum_map m = v ->
      sum_map (add_map k v' m) = (v' + v)%Z.
  Proof.
    intros; subst.
    revert dependent k. revert v'.
    induction m; intros; subst.
    + reflexivity.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * inversion H.
      * simpl in *. rewrite IHm; auto. lia.
  Qed.

  Lemma sum_map_sub_in m k z v :
    lookup_map m k = Some z ->
    sum_map m = v ->
    sum_map (add_map k 0 m) = (v - z)%Z.
  Proof.
    intros; subst.
    revert dependent k. revert z.
    induction m; intros; subst; tryfalse.
    simpl in *. destruct (k =? n) eqn:Hkn.
    + inversion H; subst.
      simpl in *. lia.
    + simpl. now erewrite IHm; eauto.
  Qed.

  (** The contract does not leak funds: the overall balance before the
      deadline is always equal to the sum of individual donations *)

  Definition consistent_balance_deadline current_slot state :=
    ~~ deadline_passed current_slot state ->
  sum_map (donations_coq state) = balance_coq state.


  (** This lemma holds for any message *)
  Lemma contract_backed BC CallCtx msg :

    {{ consistent_balance_deadline (Current_slot BC) }}

      Receive.receive BC CallCtx msg

    {{ fun fin _ => consistent_balance_deadline (Current_slot BC) fin }}.
  Proof.
    intros init H.
    (* destruct H as [Hdl Hsum]. *)
    destruct msg.
    + (* Donate *)
      simpl in *.
      (* specialize Hdl as Hdl'. *)
      unfold consistent_balance_deadline,deadline_passed in H.
      unfold run,consistent_balance_deadline.
      (* apply not_ltb in Hdl. simpl. *)
      simpl.
      destruct (_ <=? _); tryfalse.
      * destruct (lookup_map _ _) eqn:Hlook.
        ** repeat eexists; intro Hdl; eauto. now apply sum_map_add_in.
        ** repeat eexists; intro Hdl; eauto. now apply sum_map_add_not_in.
      * repeat eexists; intro Hdl; eauto.
    + (* GetFunds *)
      unfold consistent_balance_deadline in *.
      unfold deadline_passed in *.
      unfold run. simpl.
      destruct (deadline_coq init <? Current_slot BC) eqn:Hdl.
      ** (* it is not possible to get funds before the deadline, so the state is not modified *)
         (match goal with
          | [ |- context[(if ?x then _ else _ )] ] => destruct x eqn:Hx
          end); eauto; repeat eexists; simpl in *; intros;
           destruct (_ <? _); tryfalse.
      ** destruct (_ <? _); tryfalse. rewrite Bool.andb_false_r. simpl.
         repeat eexists; eauto.
    + (* Claim *)
      unfold consistent_balance_deadline in *.
      unfold deadline_passed in *.
      unfold run. simpl.
      destruct (deadline_coq init <? Current_slot BC) eqn:Hdl.
      ** (* it is not possible to get funds before the deadline, so the state is not modified *)
         (match goal with
          | [ |- context[(if ?x then _ else _ )] ] => destruct x eqn:Hx
          end);
          simpl in *; try destruct (lookup_map _ _); repeat eexists; eauto; intros; destruct (_ <? _); tryfalse.
      ** destruct (_ <? _); tryfalse. rewrite Bool.andb_false_l. simpl.
         repeat eexists; eauto.
  Qed.

  Definition consistent_balance state :=
    ~~ state.(done_coq) ->
  sum_map (donations_coq state) = balance_coq state.


  (** This lemma holds for any message *)
  Lemma contract_state_consistent BC CallCtx msg :
    {{ consistent_balance }}

      Receive.receive BC CallCtx msg

    {{ fun fin _ => consistent_balance fin }}.
  Proof.
        intros init H.
    (* destruct H as [Hdl Hsum]. *)
    destruct msg.
    + (* Donate *)
      simpl in *.
      (* specialize Hdl as Hdl'. *)
      unfold consistent_balance,deadline_passed in H.
      unfold run,consistent_balance.
      (* apply not_ltb in Hdl. simpl. *)
      simpl.
      destruct (_ <=? _); tryfalse.
      * destruct (lookup_map _ _) eqn:Hlook.
        ** repeat eexists; intro Hdl; eauto. now apply sum_map_add_in.
        ** repeat eexists; intro Hdl; eauto. now apply sum_map_add_not_in.
      * repeat eexists; intro Hdl; eauto.
    + (* GetFunds *)
      unfold consistent_balance in *.
      unfold run. simpl.
         (match goal with
          | [ |- context[(if ?x then _ else _ )] ] => destruct x eqn:Hx
          end); eauto; repeat eexists; simpl in *; intros;
           destruct (_ <? _); tryfalse.
    + (* Claim *)
      unfold consistent_balance in *.
      unfold deadline_passed in *.
      unfold run. simpl.
      destruct (done_coq _) eqn:Hdone.
      * rewrite Bool.andb_false_r. repeat eexists; eauto.
        intros. destruct (done_coq _); tryfalse.
      * (match goal with
         | [ |- context[(if ?x then _ else _ )] ] => destruct x eqn:Hx
         end);
          simpl in *; try destruct (lookup_map _ _) eqn:Hlook; repeat eexists; eauto; intros; destruct (_ <? _); tryfalse.
        cbn. now apply sum_map_sub_in.
  Qed.

  Definition donations_non_neg init := map_forallb (Z.leb 0%Z) init.(donations_coq) = true.

  Lemma non_neg_add_in m : forall n0 (v' : Z) k,
      (0 <= v')%Z ->
      lookup_map m k = Some n0 ->
      map_forallb (Z.leb 0%Z) m ->
      map_forallb (Z.leb 0%Z) (add_map k (n0+v') m).
  Proof.
    intros; subst.
    revert dependent n0. revert k.
    induction m; intros k n0 Hlook; subst.
    + inversion Hlook.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * simpl in *. inversion Hlook.
        inv_andb H1. rewrite Nat.eqb_eq in *; subst.
        subst; split_andb; auto.
        propify; lia.
      * simpl in *.
        inv_andb H1.
        now propify.
  Qed.

  Lemma non_neg_add_not_in m : forall (v' : Z) k,
      (0 <= v')%Z ->
      lookup_map m k = None ->
      map_forallb (Z.leb 0%Z) m ->
      map_forallb (Z.leb 0%Z) (add_map k v' m).
  Proof.
    induction m; intros ? ? Hnneg Hlook H; subst.
    + simpl in *. split_andb; now propify.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * simpl in *.
        inv_andb H. rewrite Nat.eqb_eq in *; subst.
        subst; split_andb; auto.
        propify; lia.
      * simpl in *.
        inv_andb H.
        now propify.
  Qed.

  Lemma non_neg_add_0 m k :
    map_forallb (Z.leb 0%Z) m ->
    map_forallb (Z.leb 0%Z) (add_map k 0 m).
  Proof.
    induction m; intros.
    + easy.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * simpl in *.
        now inv_andb H.
      * simpl in *.
        inv_andb H.
        now propify.
  Qed.

  (** All the entries in the table of contributions contains non-negative amounts *)
  Lemma contract_state_donation_non_neg BC CallCtx msg :
    (0 <= CallCtx.(Ctx_amount))%Z ->

    {{ donations_non_neg }}

      Receive.receive BC CallCtx msg

    {{ fun fin _ => donations_non_neg fin }}.
  Proof.
    intros Hamount init H.
    destruct msg.
    + (* Donate *)
      simpl in *.
      (* specialize Hdl as Hdl'. *)
      unfold consistent_balance,deadline_passed in H.
      unfold run,consistent_balance.
      (* apply not_ltb in Hdl. simpl. *)
      simpl.
      destruct (_ <=? _); tryfalse.
      * destruct (lookup_map _ _) eqn:Hlook.
        ** repeat eexists; eauto.
           assert (0 <=? z)%Z by now eapply map_forallb_lookup_map.
           unfold donations_non_neg. cbn.
           eapply non_neg_add_in; eauto.
        ** repeat eexists; eauto.
           unfold donations_non_neg. cbn.
           eapply non_neg_add_not_in; eauto.
      * repeat eexists; eauto.
    + (* GetFunds *)
      unfold donations_non_neg in *.
      unfold run. simpl.
         (match goal with
          | [ |- context[(if ?x then _ else _ )] ] => destruct x eqn:Hx
          end); eauto; repeat eexists; simpl in *; intros;
           destruct (_ <? _); tryfalse.
    + (* Claim *)
      unfold donations_non_neg in *.
      unfold run. simpl.
      (match goal with
         | [ |- context[(if ?x then _ else _ )] ] => destruct x eqn:Hx
       end);
        simpl in *; try destruct (lookup_map _ _) eqn:Hlook; repeat eexists; eauto.
      simpl. now apply non_neg_add_0.
  Qed.


  (** The owner gets the money after the deadline, if the goal is reached *)

  Lemma GetFunds_correct BC CallCtx (OwnerAddr := CallCtx.(Ctx_from)) (funds : Z) :
    {{ fun init => funded BC.(Current_slot) init
       /\ init.(owner_coq) =? OwnerAddr
       /\ balance_coq init = funds }}

    Receive.receive BC CallCtx GetFunds_coq

    {{ fun fin out =>
       (* the money are sent back *)
       In (Act_transfer OwnerAddr funds) out
       (* set balance to 0 after withdrawing by the owner *)
       /\ fin.(balance_coq) = 0%Z
       (* set the "done" flag *)
       /\ fin.(done_coq) = true}}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hfunded [Hown Hbalance]]. unfold funded,goal_reached,deadline_passed in *.
    subst. simpl in *.
    unfold run. simpl in *. subst OwnerAddr. eexists. eexists.
    destruct (_ <? _); tryfalse. destruct ( _ =? _); tryfalse. simpl in *.
    destruct (_ <=? _)%Z; tryfalse. repeat split; eauto.
    now constructor.
  Qed.

  (** Backers cannot claim their money if the campaign have succeeded (but owner haven't claimed the money yet, so the "done" flag is not set to [true]) *)
  Lemma no_claim_if_succeeded BC CallCtx the_state:
    {{ fun init =>
         funded BC.(Current_slot) init
         /\ ~~ init.(done_coq)
         /\ init = the_state }}

      Receive.receive BC CallCtx Claim_coq

    (* Nothing happens - the stated stays the same and no outgoing transfers *)
    {{ fun fin out => fin = the_state /\ out = [] }}.
  Proof.
    unfold assertion. intros init H. simpl.
    unfold funded,deadline_passed,goal_reached in *. subst. simpl in *.
    destruct H as [Hdl [Hgoal Hst]].
    inv_andb Hdl. subst. unfold run. simpl.
    exists the_state. eexists.
    destruct the_state as [i_balance i_dons i_own i_dl i_done i_goal].
    destruct CallCtx. simpl in *.

    destruct (_ <? _); tryfalse.
    replace (i_balance <? i_goal)%Z with false by
        (symmetry; rewrite Z.ltb_ge in *; rewrite Z.leb_le in *; lia).
    now simpl.
  Qed.

  (** Backers cannot claim their money if the contract is marked as "done" *)
  Lemma no_claim_after_done BC CallCtx the_state :
    {{ fun init => init.(done_coq) /\ init = the_state }}

     Receive.receive BC CallCtx Claim_coq
    (* Nothing happens - the stated stays the same and no outgoing transfers *)
    {{ fun fin out => fin = the_state /\ out = [] }}.
  Proof.
    unfold assertion. intros init H. simpl. destruct H. subst.
    unfold funded,deadline_passed,goal_reached in *. subst. simpl in *.
    exists the_state. eexists.
    unfold run. simpl in *. destruct (done_coq _); tryfalse. simpl in *.
    now rewrite Bool.andb_false_r.
  Qed.

End CrowdfundingProperties.
