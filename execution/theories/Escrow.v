(* This file defines a simple escrow contract based on the "safe remote
purchase" example in Solidity's docs. This contract allows a seller to sell an
item in a trustless setting assuming economically rational actors. With the
premise that the seller wants to sell an item for 1 ETH, the contract works in
the following way:

1. The seller deploys the contract and commits 2 ETH.
2. The buyer commits 2 ETH before the deadline.
3. The seller hands over the item (outside of the smart contract).
4. The buyer confirms he has received the item. He gets 1 ETH back
while the seller gets 3 ETH back.

If the buyer does not commit the funds, the seller gets his money back after the
deadline. The economic rationality shows up in our assumption that the seller
will confirm he has received the item to get his own funds back. *)

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
Require Import Automation.
Require Import Blockchain.
Require Import Extras.
Require Import Monads.
Require Import Serializable.
From RecordUpdate Require Import RecordUpdate.

Import ListNotations.
Import RecordSetNotations.

Section Escrow.
Context `{Base : ChainBase}.

Set Nonrecursive Elimination Schemes.

Record Setup :=
  build_setup {
      setup_buyer : Address;
    }.

Inductive NextStep :=
(* Waiting for buyer to commit itemvalue * 2 *)
| buyer_commit
(* Waiting for buyer to confirm item received *)
| buyer_confirm
(* Waiting for buyer and seller to withdraw their funds. *)
| withdrawals
(* No next step, sale is done. *)
| none.

Record State :=
  build_state {
      last_action : nat;
      next_step : NextStep;
      seller : Address;
      buyer : Address;
      seller_withdrawable : Amount;
      buyer_withdrawable : Amount;
    }.

Inductive Msg :=
| commit_money
| confirm_item_received
| withdraw.

Global Instance State_settable : Settable _ :=
  settable! build_state <last_action; next_step; seller; buyer;
                         seller_withdrawable; buyer_withdrawable>.

Global Instance Setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect<build_setup>.

Global Instance NextStep_serializable : Serializable NextStep :=
  Derive Serializable NextStep_rect<buyer_commit, buyer_confirm, withdrawals, none>.

Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>.

Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<commit_money, confirm_item_received, withdraw>.

Open Scope Z.
Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup)
  : option State :=
  let seller := ctx_from ctx in
  let buyer := setup_buyer setup in
  do if (buyer =? seller)%address then None else Some tt;
  do if ctx_amount ctx =? 0 then None else Some tt;
  do if Z.even (ctx_amount ctx) then Some tt else None;
  Some (build_state (current_slot chain) buyer_commit seller buyer 0 0).

Definition receive
           (chain : Chain) (ctx : ContractCallContext)
           (state : State) (msg : option Msg)
  : option (State * list ActionBody) :=
  match msg, next_step state with
  | Some commit_money, buyer_commit =>
    let item_price := (account_balance chain (ctx_contract_address ctx)
                       - ctx_amount ctx) / 2 in
    let expected := item_price * 2 in
    do if (ctx_from ctx =? buyer state)%address then Some tt else None;
    do if ctx_amount ctx =? expected then Some tt else None;
    Some (state<|next_step := buyer_confirm|>
               <|last_action := current_slot chain|>, [])

  | Some confirm_item_received, buyer_confirm =>
    let item_price := account_balance chain (ctx_contract_address ctx) / 4 in
    do if (ctx_from ctx =? buyer state)%address then Some tt else None;
    do if ctx_amount ctx =? 0 then Some tt else None;
    let new_state :=
        state<|next_step := withdrawals|>
             <|buyer_withdrawable := item_price|>
             <|seller_withdrawable := item_price * 3|> in
    Some (new_state, [])

  | Some withdraw, withdrawals =>
    do if ctx_amount ctx =? 0 then Some tt else None;
    let from := ctx_from ctx in
    do '(to_pay, new_state) <-
       match from =? buyer state, from =? seller state with
       | true, _ => Some (buyer_withdrawable state, state<|buyer_withdrawable := 0|>)
       | _, true => Some (seller_withdrawable state, state<|seller_withdrawable := 0|>)
       | _, _ => None
       end%address;
    do if to_pay >? 0 then Some tt else None;
    let new_state :=
        match buyer_withdrawable new_state, seller_withdrawable new_state with
        | 0, 0 => new_state<|next_step := none|>
        | _, _ => new_state
        end in
    Some (new_state, [act_transfer (ctx_from ctx) to_pay])

  | Some withdraw, buyer_commit =>
    do if ctx_amount ctx =? 0 then Some tt else None;
    do if (last_action state + 50 <? current_slot chain)%nat then None else Some tt;
    do if (ctx_from ctx =? seller state)%address then Some tt else None;
    let balance := account_balance chain (ctx_contract_address ctx) in
    Some (state<|next_step := none|>, [act_transfer (seller state) balance])

  | _, _ => None
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

Program Definition contract : Contract Setup Msg State :=
  build_contract init _ receive _.
Next Obligation. repeat intro; solve_contract_proper. Qed.
Next Obligation. repeat intro; solve_contract_proper. Qed.

Section Theories.
  Lemma no_self_calls bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Escrow.contract : WeakContract) ->
    Forall (fun abody => match abody with
                         | act_transfer to _ => (to =? caddr)%address = false
                         | _ => False
                         end) (outgoing_acts bstate caddr).
  Proof.
    contract_induction; intros; cbn in *; auto.
    - now inversion IH.
    - apply Forall_app; split; try tauto.
      clear IH.
      unfold receive in receive_some.
      destruct_match as [[]|] in receive_some; try congruence.
      + destruct_match in receive_some; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        inversion_clear receive_some; auto.
      + destruct_match in receive_some; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        inversion_clear receive_some; auto.
      + destruct_match in receive_some; try congruence.
        * destruct_match in receive_some; cbn in *; try congruence.
          destruct_match in receive_some; cbn in *; try congruence.
          destruct (address_eqb_spec (ctx_from ctx) (seller prev_state)) as
              [<-|]; cbn in *; try congruence.
          inversion_clear receive_some.
          constructor; try constructor.
          apply address_eq_ne; auto.
        * destruct_match in receive_some; cbn in *; try congruence.
          destruct_match in receive_some; cbn in *; try congruence.
          destruct_match in receive_some.
          destruct_match in receive_some; cbn in *; try congruence.
          inversion_clear receive_some.
          constructor; try constructor.
          apply address_eq_ne; auto.
    - inversion_clear IH as [|? ? head_not_me tail_not_me].
      apply Forall_app; split; auto; clear tail_not_me.
      destruct head; try contradiction.
      destruct action_facts as [? [? ?]].
      destruct_address_eq; congruence.
    - now rewrite <- perm.
    - instantiate (DeployFacts := fun _ _ => True).
      instantiate (CallFacts := fun _ _ _ => True).
      instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      unset_all; subst; cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
  Qed.

  Definition txs_to (to : Address) (txs : list Tx) : list Tx :=
    filter (fun tx => (tx_to tx =? to)%address) txs.

  Arguments txs_to : simpl never.

  Lemma txs_to_cons addr tx txs :
    txs_to addr (tx :: txs) =
    if (tx_to tx =? addr)%address then
      tx :: txs_to addr txs
    else
      txs_to addr txs.
  Proof. reflexivity. Qed.

  Definition txs_from (from : Address) (txs : list Tx) : list Tx :=
    filter (fun tx => (tx_from tx =? from)%address) txs.

  Arguments txs_from : simpl never.

  Lemma txs_from_cons addr tx txs :
    txs_from addr (tx :: txs) =
    if (tx_from tx =? addr)%address then
      tx :: txs_from addr txs
    else
      txs_from addr txs.
  Proof. reflexivity. Qed.

  Local Open Scope bool.
  Definition buyer_confirmed (inc_calls : list (ContractCallInfo Msg)) buyer :=
    existsb (fun call => (call_from call =? buyer)%address &&
                         match call_msg call with
                         | Some confirm_item_received => true
                         | _ => false
                         end) inc_calls.

  Definition transfer_acts_to addr acts :=
    filter (fun a => match a with
                     | act_transfer to _ => (to =? addr)%address
                     | _ => false
                     end) acts.

  Arguments transfer_acts_to : simpl never.

  Lemma transfer_acts_to_cons addr act acts :
    transfer_acts_to addr (act :: acts) =
    if match act with
       | act_transfer to _ => (to =? addr)%address
       | _ => false
       end
    then
      act :: transfer_acts_to addr acts
    else
      transfer_acts_to addr acts.
  Proof. reflexivity. Qed.

  Definition money_to
             {bstate_from bstate_to}
             (trace : ChainTrace bstate_from bstate_to)
             caddr addr :=
    sumZ tx_amount (txs_to addr (outgoing_txs trace caddr)) +
    sumZ act_body_amount (transfer_acts_to addr (outgoing_acts bstate_to caddr)).

  Lemma escrow_correct_strong bstate caddr (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (Escrow.contract : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      let item_worth := deployment_amount depinfo / 2 in
      let seller_addr := deployment_from depinfo in
      let buyer_addr := setup_buyer (deployment_setup depinfo) in
      deployment_amount depinfo = 2 * item_worth /\
      item_worth > 0 /\
      seller cstate = seller_addr /\
      buyer cstate = buyer_addr /\
      buyer_addr <> seller_addr /\
      forallb (fun act => match act with
                         | act_transfer _ _ => true
                         | _ => false
                         end) (outgoing_acts bstate caddr) = true /\
      match next_step cstate with
      | buyer_commit =>
        account_balance bstate caddr = 2 * item_worth /\
        outgoing_acts bstate caddr = [] /\
        outgoing_txs trace caddr = [] /\
        inc_calls = []

      | buyer_confirm =>
        account_balance bstate caddr = 4 * item_worth /\
        outgoing_acts bstate caddr = [] /\
        outgoing_txs trace caddr = [] /\
        inc_calls = [build_call_info buyer_addr (2 * item_worth) (Some commit_money)]

      | withdrawals =>
        buyer_confirmed inc_calls buyer_addr = true /\
        filter (fun c => negb (call_amount c =? 0)%Z ) inc_calls =
        [build_call_info buyer_addr (2 * item_worth) (Some commit_money)] /\
        money_to trace caddr seller_addr + seller_withdrawable cstate = 3 * item_worth /\
        money_to trace caddr buyer_addr + buyer_withdrawable cstate = 1 * item_worth

      | none =>
        buyer_confirmed inc_calls buyer_addr = true /\
        filter (fun c => negb (call_amount c =? 0)%Z) inc_calls =
        [build_call_info buyer_addr (2 * item_worth) (Some commit_money)] /\
        money_to trace caddr seller_addr = 3 * item_worth /\
        money_to trace caddr buyer_addr = 1 * item_worth \/

        inc_calls = [build_call_info seller_addr 0 (Some withdraw)] /\
        money_to trace caddr seller_addr = 2 * item_worth /\
        money_to trace caddr buyer_addr = 0
      end.
  Proof.
    unfold money_to.
    contract_induction; cbn in *; intros.
    - (* New block *)
      auto.
    - (* Deployment *)
      unfold Escrow.init in *.
      destruct (address_eqb_spec (setup_buyer setup) (ctx_from ctx));
        cbn in *; try congruence.
      destruct (ctx_amount ctx =? 0) eqn:amount_some; cbn in *; try congruence.
      destruct (Z.even (ctx_amount ctx)) eqn:amount_even; cbn in *; try congruence.
      inversion init_some; subst; clear init_some.
      cbn.
      assert (2 * (ctx_amount ctx / 2) > 0 -> ctx_amount ctx / 2 > 0) by lia.
      enough (2 * (ctx_amount ctx / 2) > 0 /\
              ctx_amount ctx = 2 * (ctx_amount ctx / 2)) by tauto.
      assert (ctx_amount ctx mod 2 = 0).
      {
        rewrite Zeven_mod in amount_even.
        unfold Zeq_bool in *.
        destruct_match eqn:amount_mod_2 in amount_even; try congruence; auto.
        destruct (Z.compare_spec (ctx_amount ctx mod 2) 0); auto; try congruence.
      }
      rewrite <- (Z_div_exact_2 (ctx_amount ctx) 2) by (auto; lia).
      split; auto.
      instantiate (DeployFacts := fun _ ctx => ctx_amount ctx >= 0);
        subst DeployFacts; cbn in *.
      apply Z.eqb_neq in amount_some.
      lia.
    - (* Transfer from contract to someone *)
      repeat rewrite txs_to_cons.
      do 5 (split; try tauto).
      destruct IH as [_ [_ [_ [<- [_ [only_transfers IH]]]]]].
      apply andb_prop in only_transfers.
      split; try tauto.
      destruct only_transfers as [is_transfer _].
      destruct out_act; try congruence.
      destruct tx_act_match as [<- [<- _]].
      repeat rewrite transfer_acts_to_cons in *.
      destruct (next_step cstate).
      + intuition congruence.
      + intuition congruence.
      + (* Transfer while next_step is withdraw; so seller or buyer withdrew *)
        do 2 (split; try tauto).
        destruct IH as [_ [_ [? ?]]].
        destruct_address_eq; cbn in *; lia.
      + (* Transfer while next_step is none; action moved from queue to txs *)
        destruct IH as [IH | IH]; [left|right].
        * do 2 (split; try tauto).
          destruct IH as [_ [? ?]].
          destruct_address_eq; cbn in *; lia.
        * split; try tauto.
          destruct IH as [_ ?].
          destruct_address_eq; cbn in *; lia.
    - (* Call from someone else *)
      do 2 (split; try tauto).
      unfold Escrow.receive in *.
      set (item_worth := deployment_amount dep_info / 2) in *.
      destruct msg as [[| |]|].
      + (* Some commit_money *)
        destruct (next_step prev_state); try congruence.
        destruct (address_eqb_spec (ctx_from ctx) (buyer prev_state)) as [->|];
          cbn in *; try congruence.
        destruct (ctx_amount ctx =? _) eqn:proper_amount in receive_some;
          cbn in *; try congruence.
        inversion_clear receive_some.
        cbn.
        do 4 (split; try tauto).
        destruct IH as [deployed_even [_ [_ [-> [_ [_ [balance_eq [-> [-> ->]]]]]]]]].
        apply Z.eqb_eq in proper_amount.
        rewrite balance_eq in proper_amount.
        rewrite proper_amount.
        replace (account_balance _ _) with (2 * item_worth + 2 * item_worth / 2 * 2) by lia.
        rewrite <- Z.mul_comm.
        rewrite Z.div_mul by lia.
        repeat split; auto.
        lia.
      + (* Some confirm_item_received *)
        destruct_match in receive_some; cbn in *; try congruence.
        destruct (address_eqb_spec (ctx_from ctx) (buyer prev_state)) as [->|];
          cbn in *; try congruence.
        destruct (ctx_amount ctx =? 0) eqn:zero_amount in receive_some;
          cbn in *; try congruence.
        inversion_clear receive_some.
        cbn.
        do 4 (split; try tauto).
        destruct IH as [deployed_even [? [<- [<- [_ [_ [balance_eq [-> [-> ->]]]]]]]]].
        rewrite address_eq_refl.
        cbn.
        split; auto.
        unfold txs_to, transfer_acts_to; cbn.
        apply Z.eqb_eq in zero_amount.
        rewrite zero_amount in *.
        replace (account_balance _ _) with (4 * item_worth) in * by lia.
        rewrite (Z.mul_comm 4).
        rewrite Z.div_mul by lia.
        destruct (Z.eqb_spec (2 * item_worth) 0); cbn in *; try lia.
        repeat split; lia.
      + (* Some withdraw. Can be sent while next_step is either
           commit_money or withdrawals. *)
        destruct_match eqn:prev_next_step in receive_some;
          cbn -[Nat.ltb] in *; try congruence.
        * (* next_step was commit_money, so seller is withdrawing money
          because buyer did not commit anything. *)
          destruct (ctx_amount ctx =? 0) eqn:zero_amount in receive_some;
            cbn -[Nat.ltb] in *; try congruence.
          apply Z.eqb_eq in zero_amount.
          rewrite zero_amount in *.
          destruct_match in receive_some; cbn in *; try congruence.
          destruct (address_eqb_spec (ctx_from ctx) (seller prev_state))
            as [->|]; cbn in *; try congruence.
          inversion_clear receive_some; cbn.
          do 4 (split; try tauto).
          (* In this case we go to none state without buyer having confirmed anything *)
          right.
          destruct IH as [_ [_ [<- [_ [? [_ [? [-> [-> ->]]]]]]]]].
          unfold txs_to, transfer_acts_to.
          cbn.
          rewrite address_eq_refl, address_eq_ne by auto.
          cbn.
          split; auto; lia.
        * (* next_step was withdrawals, so either seller or buyer is withdrawing money.
             This might put us into next_step = none. *)
          destruct (ctx_amount ctx =? 0) eqn:zero_amount in receive_some;
            cbn -[Nat.ltb] in *; try congruence.
          apply Z.eqb_eq in zero_amount.
          rewrite zero_amount in *.
          destruct (address_eqb_spec (ctx_from ctx) (buyer prev_state))
            as [->|]; [|destruct (address_eqb_spec (ctx_from ctx) (seller prev_state))
                         as [->|]; cbn in *; try congruence].
          -- (* Buyer withdrawing *)
            cbn in *.
            destruct_match in receive_some; cbn in *; try congruence.
            inversion_clear receive_some; cbn.
            apply and_assoc; split; [destruct_match; tauto|].
            do 2 (split; try tauto).
            destruct (Z.eqb_spec (seller_withdrawable prev_state) 0) as [seller_done|].
            ++ (* No one has more to withdrew, next_step is none now, so establish
                  final IH. Since we got here from withdrawal we will be in left case. *)
              rewrite seller_done in *.
              left.
              repeat rewrite transfer_acts_to_cons.
              fold (buyer_confirmed prev_inc_calls
                                    (setup_buyer (deployment_setup dep_info))).
              destruct IH as [_ [_ [<- [-> [? [_ [-> [-> [? ?]]]]]]]]].
              rewrite address_eq_refl.
              rewrite address_eq_ne by assumption.
              cbn.
              do 2 (split; [tauto|]).
              lia.
            ++ (* Seller still has more to withdraw, next_step is still withdrawals *)
              replace (match seller_withdrawable prev_state with _ => _ end)
                with (prev_state <| buyer_withdrawable := 0 |>)
                by (destruct_match; cbn in *; try congruence).
              cbn.
              rewrite prev_next_step.
              repeat rewrite transfer_acts_to_cons.
              fold (buyer_confirmed prev_inc_calls
                                    (setup_buyer (deployment_setup dep_info))).
              destruct IH as [_ [_ [<- [-> [? [_ [-> [-> [? ?]]]]]]]]].
              rewrite address_eq_refl.
              rewrite address_eq_ne by assumption.
              cbn.
              do 2 (split; try tauto).
              lia.
          -- (* Seller withdrawing. Todo: generalize and clean up. *)
            cbn in *.
            destruct_match in receive_some; cbn in *; try congruence.
            inversion_clear receive_some; cbn.
            apply and_assoc; split; [destruct_match; tauto|].
            do 2 (split; try tauto).
            destruct (Z.eqb_spec (buyer_withdrawable prev_state) 0) as [buyer_done|].
            ++ (* No one has more to withdrew, next_step is none now, so establish
                  final IH. Since we got here from withdrawal we will be in left case. *)
              rewrite buyer_done in *.
              left.
              repeat rewrite transfer_acts_to_cons.
              fold (buyer_confirmed prev_inc_calls
                                    (setup_buyer (deployment_setup dep_info))).
              destruct IH as [_ [_ [<- [<- [? [_ [-> [-> [? ?]]]]]]]]].
              rewrite address_eq_refl.
              rewrite address_eq_ne by auto.
              cbn.
              do 2 (split; [tauto|]).
              lia.
            ++ (* Buyer still has more to withdraw, next_step is still withdrawals *)
              replace (match buyer_withdrawable prev_state with _ => _ end)
                with (prev_state <| seller_withdrawable := 0 |>)
                by (destruct_match; cbn in *; try congruence).
              cbn.
              rewrite prev_next_step.
              repeat rewrite transfer_acts_to_cons.
              fold (buyer_confirmed prev_inc_calls
                                    (setup_buyer (deployment_setup dep_info))).
              destruct IH as [_ [_ [<- [<- [? [_ [-> [-> [? ?]]]]]]]]].
              rewrite address_eq_refl.
              rewrite address_eq_ne by auto.
              cbn.
              do 2 (split; [tauto|]).
              lia.
      + (* None *)
        congruence.
    - (* Self call *)
      instantiate (CallFacts := fun _ ctx _ => ctx_from ctx <> ctx_contract_address ctx);
        subst CallFacts; cbn in *; congruence.
    - (* Permuting queue *)
      do 5 (split; try tauto).
      split.
      + now rewrite <- perm.
      + assert (out_queue = [] -> out_queue' = [])
          by (intros ->; now apply Permutation_nil).
        unfold transfer_acts_to in *.
        repeat rewrite sumZ_filter in *.
        destruct (next_step cstate); try tauto.
        * now rewrite <- perm.
        * destruct IH as [_ [_ [_ [_ [_ [_ [IH | IH]]]]]]];
            [left|right]; rewrite <- perm; auto.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      unset_all; subst; cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      intros.
      pose proof (no_self_calls bstate_from to_addr ltac:(assumption) ltac:(assumption))
           as all.
      unfold outgoing_acts in *.
      rewrite queue_prev in *.
      subst act; cbn in all.
      destruct_address_eq; cbn in *; auto.
      inversion_clear all as [|? ? hd _].
      destruct msg.
      + contradiction.
      + rewrite address_eq_refl in hd.
        congruence.
  Qed.

  Definition net_balance_effect
             {bstate_from bstate_to : ChainState}
             (trace : ChainTrace bstate_from bstate_to)
             (caddr addr : Address) : Amount :=
    sumZ tx_amount (txs_to addr (outgoing_txs trace caddr))
    - sumZ tx_amount (txs_from addr (incoming_txs trace caddr)).

  (* Our main assumption is that the escrow will always finish due to
  economically rational actors. We do not formalize this. *)
  Definition is_escrow_finished cstate :=
    match next_step cstate with
    | none => true
    | _ => false
    end.

  (* The functional correctness of the Escrow, under the assumption that the
  escrow finishes due to rational actors. *)
  Corollary escrow_correct
            {ChainBuilder : ChainBuilderType}
            prev new header acts :
    builder_add_block prev header acts = Some new ->
    let trace := builder_trace new in
    forall caddr,
      env_contracts new caddr = Some (Escrow.contract : WeakContract) ->
      exists (depinfo : DeploymentInfo Setup)
             (cstate : State)
             (inc_calls : list (ContractCallInfo Msg)),
        deployment_info Setup trace caddr = Some depinfo /\
        contract_state new caddr = Some cstate /\
        incoming_calls Msg trace caddr = Some inc_calls /\
        let item_worth := deployment_amount depinfo / 2 in
        let seller := deployment_from depinfo in
        let buyer := setup_buyer (deployment_setup depinfo) in
        is_escrow_finished cstate = true ->
        (buyer_confirmed inc_calls buyer = true /\
         net_balance_effect trace caddr seller = item_worth /\
         net_balance_effect trace caddr buyer = -item_worth \/

         buyer_confirmed inc_calls buyer = false /\
         net_balance_effect trace caddr seller = 0 /\
         net_balance_effect trace caddr buyer = 0).
  Proof.
    intros after_add trace caddr escrow_at_caddr.
    cbn in *.
    pose proof (escrow_correct_strong _ caddr trace escrow_at_caddr) as general.
    cbn in general.
    destruct general as
        [cstate [depinfo [inc_calls [? [? [? [? [? [? [? [? [_ IH]]]]]]]]]]]].
    exists depinfo, cstate, inc_calls.
    do 3 (split; [tauto|]).
    intros is_finished.
    unfold is_escrow_finished in *.
    destruct (next_step cstate); try congruence; clear is_finished.
    unfold net_balance_effect, money_to.
    assert (inc_txs:
              forall addr,
                sumZ tx_amount (txs_from addr (incoming_txs trace caddr)) =
                sumZ (fun '(a, b, c) => c)
                     (filter (fun '(from, _, _) => (from =? addr)%address)
                             (map (fun tx => (tx_from tx, tx_to tx, tx_amount tx))
                                  (incoming_txs trace caddr)))).
    {
      intros addr.
      induction (incoming_txs trace caddr) as [|hd tl IH'].
      - reflexivity.
      - rewrite txs_from_cons.
        cbn.
        destruct_address_eq; cbn in *; rewrite IH'; reflexivity.
    }

    repeat rewrite inc_txs; clear inc_txs.
    rewrite (incoming_txs_contract caddr _ trace _ depinfo _ inc_calls) by assumption.
    repeat rewrite filter_app, sumZ_app.
    cbn.
    rewrite address_eq_refl.
    rewrite address_eq_ne by auto.
    cbn.
    rewrite 2!filter_map, 2!sumZ_map.

    set (buyer_addr := setup_buyer (deployment_setup depinfo)) in *.
    set (seller_addr := deployment_from depinfo) in *.

    unfold money_to, transfer_acts_to in IH.
    cbn in IH.

    change (fun a => call_amount a) with (@call_amount _ Msg).

    destruct IH as [IH | IH]; [left|right].
    - split; [tauto|].
      remember (build_call_info _ _ (Some commit_money)) as commitment.
      assert (Hsum :
                forall f,
                  sumZ call_amount (filter f inc_calls) =
                  sumZ call_amount (filter f [commitment])).
      {
        intros f.
        destruct IH as [_ [<- ?]].
        clear -inc_calls.
        induction inc_calls as [|hd tl IH']; auto.
        cbn.
        destruct (Z.eqb_spec (call_amount hd) 0) as [zero_amount|].
        - cbn.
          destruct (f hd); cbn; try rewrite zero_amount; rewrite IH'; auto.
        - cbn.
          destruct (f hd); cbn; rewrite IH'; auto.
      }

      rewrite 2!Hsum; clear Hsum; subst commitment; cbn in *.
      rewrite address_eq_refl, address_eq_ne by auto.
      cbn.
      destruct IH as [_ [_ [? ?]]].
      split; lia.
    - destruct IH as [-> IH].
      cbn.
      rewrite address_eq_refl, address_eq_ne by auto.
      cbn.
      split; [auto|].
      split; lia.
  Qed.

End Theories.

End Escrow.
