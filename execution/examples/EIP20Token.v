(*
  This file contains an implementation of the EIP 20 Token Specification (https://eips.ethereum.org/EIPS/eip-20).
  The implementation is essentially a port of https://github.com/ConsenSys/Tokens/blob/fdf687c69d998266a95f15216b1955a4965a0a6d/contracts/eip20/EIP20.sol

*)

From Coq Require Import ZArith.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.

Import ListNotations.
Import RecordSetNotations.

Section EIP20Token.
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  Definition TokenValue := N.
  Open Scope N_scope.

  Inductive Msg :=
  | transfer : Address -> TokenValue -> Msg
  | transfer_from : Address -> Address -> TokenValue -> Msg
  | approve : Address -> TokenValue -> Msg.

  Record State :=
    build_state {
        total_supply : TokenValue;
  balances : FMap Address TokenValue;
  allowances : FMap Address (FMap Address TokenValue)
    }.

  Record Setup :=
    build_setup {
  owner : Address;
  init_amount : TokenValue;
    }.

  MetaCoq Run (make_setters State).
  MetaCoq Run (make_setters Setup).

  Section Serialization.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <transfer, transfer_from, approve>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.

  Definition init (chain : Chain)
       (ctx : ContractCallContext)
       (setup : Setup) : option State :=
    Some {| total_supply := setup.(init_amount);
            balances := FMap.add setup.(owner) setup.(init_amount) FMap.empty;
            allowances := FMap.empty |}.

  (* Transfers <amount> tokens, if <from> has enough tokens to transfer *)
  Definition try_transfer (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
    let from_balance := with_default 0 (FMap.find from state.(balances)) in
    if from_balance <? amount
    then None
    else let new_balances := FMap.add from (from_balance - amount) state.(balances) in
         let new_balances := FMap.partial_alter (fun balance => Some (with_default 0 balance + amount)) to new_balances in
         Some (state<|balances := new_balances|>).

(* The delegate tries to transfer <amount> tokens from <from> to <to>.
   Succeeds if <from> has indeed allowed the delegate to spend at least <amount> tokens on its behalf. *)
  Local Open Scope bool_scope.
  Definition try_transfer_from (delegate : Address)
       (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
  do from_allowances_map <- FMap.find from state.(allowances) ;
  do delegate_allowance <- FMap.find delegate from_allowances_map ;
  let from_balance := with_default 0 (FMap.find from state.(balances)) in
  if (delegate_allowance <? amount) || (from_balance <? amount)
  then None
  else let new_allowances := FMap.add delegate (delegate_allowance - amount) from_allowances_map in
       let new_balances := FMap.add from (from_balance - amount) state.(balances) in
       let new_balances := FMap.partial_alter (fun balance => Some (with_default 0 balance + amount)) to new_balances in
       Some (state<|balances := new_balances|><|allowances ::= FMap.add from new_allowances|>).

  (* The caller approves the delegate to transfer up to <amount> tokens on behalf of the caller *)
  Definition try_approve (caller : Address)
       (delegate : Address)
       (amount : TokenValue)
       (state : State) : option State :=
    match FMap.find caller state.(allowances) with
    | Some caller_allowances =>
      Some (state<|allowances ::= FMap.add caller (FMap.add delegate amount caller_allowances) |>)
    | None =>
      Some (state<|allowances ::= FMap.add caller (FMap.add delegate amount FMap.empty) |>)
    end.

  Open Scope Z_scope.
  Definition receive (chain : Chain)
       (ctx : ContractCallContext)
       (state : State)
       (maybe_msg : option Msg)
    : option (State * list ActionBody) :=
    let sender := ctx.(ctx_from) in
    let without_actions := option_map (fun new_state => (new_state, [])) in
    (* Only allow calls with no money attached *)
    if ctx.(ctx_amount) >? 0
    then None
    else match maybe_msg with
   | Some (transfer to amount) => without_actions (try_transfer sender to amount state)
   | Some (transfer_from from to amount) => without_actions (try_transfer_from sender from to amount state)
   | Some (approve delegate amount) => without_actions (try_approve sender delegate amount state)
   (* transfer actions to this contract are not allowed *)
         | None => None
   end.
  Close Scope Z_scope.

  Lemma init_proper :
    Proper (ChainEquiv ==> eq ==> eq ==> eq) init.
  Proof. repeat intro; solve_contract_proper. Qed.

  Lemma receive_proper :
    Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive.
  Proof. repeat intro; solve_contract_proper. Qed.

  Definition contract : Contract Setup Msg State :=
    build_contract init init_proper receive receive_proper.

Section Theories.

Import Program.Basics.
Import Lia.
Import Coq.Logic.FunctionalExtensionality.
Notation "f 'o' g" := (compose f g) (at level 50).

Definition transfer_balance_update_correct old_state new_state from to tokens :=
  let get_balance addr state := with_default 0 (FMap.find addr state.(balances)) in
  let from_balance_before := get_balance from old_state in
  let to_balance_before := get_balance to old_state in
  let from_balance_after := get_balance from new_state in
  let to_balance_after := get_balance to new_state in
  (* if the transfer is a self-transfer, balances should remain unchained *)
  if address_eqb from to
  then
    (from_balance_before =? from_balance_after) &&
    (to_balance_before =? to_balance_after)
  else
    (from_balance_before =? from_balance_after + tokens) &&
    (to_balance_before + tokens =? to_balance_after).

Definition transfer_from_allowances_update_correct (old_state new_state : State) (from delegate : Address) (tokens : TokenValue) :=
  let get_allowance state := with_default 0 (FMap.find delegate (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from state.(allowances)))) in
  let delegate_allowance_before := get_allowance old_state in
  let delegate_allowance_after := get_allowance new_state in 
    Some (delegate_allowance_before =? delegate_allowance_before + tokens).

Lemma add_is_partial_alter : forall (account : Address) (balances : FMap Address N) (f : N -> N),
  FMap.partial_alter (fun balance : option N => Some (f (with_default 0 balance))) account balances =
  FMap.add account (f (with_default 0 (FMap.find account balances))) balances.
Proof.
  intros.
  apply fin_maps.partial_alter_ext. intros. now subst.
Qed.

Lemma add_is_partial_alter_plus : forall (account : Address) amount (balances : FMap Address N) (f : N -> N),
  FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) account balances =
  FMap.add account (with_default 0 (FMap.find account balances) + amount) balances.
Proof.
  intros.
  apply fin_maps.partial_alter_ext. intros. now subst.
Qed.

Lemma partial_alter_add_id : forall from to amount state v,
  from = to -> FMap.find from state.(balances) = Some v -> amount <= v ->
  FMap.partial_alter (fun balance => Some (with_default 0 balance + amount)) to
    (FMap.add from (v - amount) state.(balances)) = state.(balances).
Proof.
  intros.
  subst.
  rewrite add_is_partial_alter_plus; try auto.
  rewrite FMap.add_add. rewrite FMap.find_add. simpl.
  rewrite N.sub_add.
  - rewrite FMap.add_id.
    + reflexivity.
    + now setoid_rewrite H0.
  - auto.
Qed.

Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct prev_state new_state ctx.(ctx_from) to amount = true.
Proof.
  intros.
  unfold receive in H. destruct_match in H.
  - (* case: ctx_amount > 0 *) congruence.
  - (* case: ctx_amount = 0 *) unfold try_transfer in H. unfold transfer_balance_update_correct.
    destruct_match eqn:H1; destruct (FMap.find (ctx_from ctx) (balances prev_state)) eqn:from_prev; destruct_match eqn:H2 in H;
      simpl in *; try congruence; apply N.ltb_ge in H2; destruct_address_eq; try discriminate; subst; try rewrite from_prev;
      inversion H; simpl in *.
    + (* case: from =  to && find from = Some n && amount <= n *)
      rewrite FMap.find_partial_alter, FMap.find_add; try auto. simpl.
      now repeat rewrite N.sub_add, N.eqb_refl.
    + (* case: from =  to && find from = None   && amount = 0 *)
      apply N.lt_eq_cases in H2. destruct H2; try lia. subst.
      now rewrite FMap.find_partial_alter, FMap.find_add.
    + (* case: from <> to && find from = Some n && amount <= n *)
      rewrite FMap.find_partial_alter_ne, FMap.find_partial_alter, FMap.find_add, FMap.find_add_ne; try auto.
      simpl. rewrite N.sub_add; auto. now repeat rewrite N.eqb_refl.
    + (* case: from <> to && find from = None   && amount = 0 *)
      apply N.lt_eq_cases in H2. destruct H2; try lia. subst.
      rewrite FMap.find_partial_alter_ne, FMap.find_partial_alter, FMap.find_add, FMap.find_add_ne; try auto.
      apply N.eqb_refl.
Qed.

Definition sum_balances' (state : EIP20Token.State) :=
  let balances_list := (map snd o FMap.elements) state.(balances) in
    fold_left N.add balances_list 0%N.

Definition sum_balances (state : EIP20Token.State) :=
  sumnat (fun '(k, v) => N.to_nat v) (FMap.elements (balances state)).

Lemma sumnat_split : forall x y n m (l : list (Address * N)),
  sumnat (fun '(_, v) => N.to_nat v) ((y, n + m) :: l) =
  sumnat (fun '(_, v) => N.to_nat v) ((x, n) :: (y, m) :: l).
Proof.
  simpl. lia.
Qed.

Lemma sumnat_swap : forall x y n m (l : list (Address * N)),
  sumnat (fun '(_, v) => N.to_nat v) ((x, n) :: (y, m) :: l) =
  sumnat (fun '(_, v) => N.to_nat v) ((x, m) :: (y, n) :: l).
Proof.
  simpl. lia.
Qed.

Lemma sumnat_FMap_add_sub : forall from to amount (balances : FMap Address N),
  amount <= with_default 0 (FMap.find from balances) ->
    N.of_nat (sumnat (fun '(_, v) => N.to_nat v) (FMap.elements balances)) =
    N.of_nat
      (sumnat (fun '(_, v) => N.to_nat v)
         (FMap.elements
            (FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) to
               (FMap.add from (with_default 0 (FMap.find from balances) - amount) balances)))).
Proof.
  intros from to amount balances H.
  rewrite add_is_partial_alter_plus; auto.
  destruct (address_eqb from to) eqn:from_to_eq;
    destruct (FMap.find from balances) eqn:from_prev;
    destruct_address_eq; try discriminate; subst; simpl in *;
    repeat match goal with
    | H : _ <= 0 |- _ => apply N.lt_eq_cases in H as [H | H]; try lia; subst
    | |- context [ with_default _ (FMap.find to balances) ] => destruct (FMap.find to balances) eqn:to_prev; simpl
    | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => rewrite FMap.find_add
    | H : FMap.find ?t ?m = Some _ |- FMap.find ?t ?m = Some _ => simpl; rewrite H; f_equal; lia
    | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
    | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
    | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] =>rewrite FMap.elements_add_existing; eauto
    | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => rewrite FMap.add_add
    | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add; eauto
    | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
    | H : FMap.find ?x ?m = Some _ |- context [ sumnat _ ((?x, _) :: FMap.elements (FMap.remove ?x ?m)) ] => rewrite fin_maps.map_to_list_delete; auto
    | H : FMap.find ?x _ = Some ?n |- context [ sumnat _ ((?x, ?n) :: FMap.elements (FMap.remove ?x _)) ] => rewrite fin_maps.map_to_list_delete; auto
    | H : FMap.find ?x _ = Some ?n |- context [ sumnat _ ((?x, ?n) :: (_, _) :: FMap.elements (FMap.remove ?x _)) ] => rewrite sumnat_swap, fin_maps.map_to_list_delete; auto
    | |- context [ _ + 0 ] => rewrite N.add_0_r
    | |- context [ 0 + _ ] => rewrite N.add_0_l
    | |- context [ sumnat _ ((?t, ?n + ?m) :: _) ] => rewrite sumnat_split with (x:=t)
    | |- context [ sumnat _ ((_, ?n) :: (_, ?m - ?n) :: _) ] => rewrite <- sumnat_split
   end.
Qed.

Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
  N.of_nat (sum_balances prev_state) = N.of_nat (sum_balances new_state).
Proof.
  intros.
  unfold receive in H.
  unfold try_transfer in H.
  destruct_match in H; simpl in *; try congruence.
  destruct_match eqn:H1 in H; simpl in *; try congruence.
  apply N.ltb_ge in H1.
  inversion H.
  unfold sum_balances. simpl.
  now apply sumnat_FMap_add_sub.
Qed.

Lemma try_transfer_from_preserves_total_supply : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
  N.of_nat (sum_balances prev_state) = N.of_nat (sum_balances new_state).
Proof.
  intros.
  unfold receive in H.
  unfold try_transfer_from in H.
  do 3 (destruct_match in H; simpl in *; try congruence).
  destruct_match eqn:H1 in H; simpl in *; try congruence.
  apply Bool.orb_false_iff in H1 as [_ H1].
  apply N.ltb_ge in H1.
  inversion H.
  unfold sum_balances. simpl.
  now apply sumnat_FMap_add_sub.
Qed.

Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
  N.of_nat (sum_balances prev_state) = N.of_nat (sum_balances new_state).
Proof.
  intros.
  unfold receive in H.
  unfold try_approve in H.
  do 2 (destruct_match in H; simpl in *; try congruence).
  all: now inversion H.
Qed.

Lemma sum_balances_eq_init_supply block_state contract_addr (trace : ChainTrace empty_state block_state) :
  env_contracts block_state contract_addr = Some (contract : WeakContract) ->
  exists cstate call_info deploy_info,
    incoming_calls Msg trace contract_addr = Some call_info
    /\ contract_state block_state contract_addr = Some cstate
    /\ deployment_info _ trace contract_addr = Some deploy_info
    /\ let init_val := init_amount deploy_info.(deployment_setup) in
      init_val = N.of_nat (sum_balances cstate).
Proof.
  contract_induction.
  - intros. cbn in *. auto.
  - intros. cbn in *. inversion init_some. unfold sum_balances. cbn in *. rewrite FMap.elements_add.
    + rewrite FMap.elements_empty. simpl. lia.
    + auto.
  - intros. cbn in *. auto.
  - intros. cbn in *. destruct msg. destruct m. 
    + apply try_transfer_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + apply try_transfer_from_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + apply try_approve_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + unfold receive in receive_some; destruct_match in receive_some; try congruence.
  - intros. cbn in *. destruct msg. destruct m. 
    + apply try_transfer_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + apply try_transfer_from_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + apply try_approve_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + unfold receive in receive_some; destruct_match in receive_some; try congruence.
  - intros. cbn in *. auto.
  - intros. cbn in *. auto.
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ => True).
    unset_all; subst;cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.



End Theories.
End EIP20Token.
