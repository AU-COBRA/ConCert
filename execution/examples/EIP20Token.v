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

  Definition contract : Contract Setup Msg State :=
    build_contract init receive.



Section Theories.

Import Lia.
Import Permutation.

(* ------------------- EIP20 functions not payable ------------------- *)
(* TODO improve proof to proving amount=0 *)
Lemma EIP20_not_payable : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state (Some msg) = Some (new_state, new_acts) ->
    ((ctx_amount ctx) <= 0)%Z.
Proof.
  intros.
  unfold receive in H. destruct_match eqn:amount in H.
  - (* case: ctx_amount > 0 *) congruence.
  - (* case: ctx_amount = 0 *) now rewrite Z.gtb_ltb, Z.ltb_ge in amount.
Qed.

Lemma receive_not_payable : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state (Some msg) = Some (new_state, new_acts) ->
    match msg with
    | transfer to amount => option_map (fun new_state : State => (new_state, [])) (try_transfer (ctx_from ctx) to amount prev_state)
    | transfer_from from to amount =>
        option_map (fun new_state : State => (new_state, [])) (try_transfer_from (ctx_from ctx) from to amount prev_state)
    | approve delegate amount =>
        option_map (fun new_state : State => (new_state, [])) (try_approve (ctx_from ctx) delegate amount prev_state)
    end = Some (new_state, new_acts).
Proof.
  intros.
  apply EIP20_not_payable in H as H1.
  unfold receive in H.
  rewrite <- Z.ltb_ge, <- Z.gtb_ltb in H1.
  now rewrite H1 in H.
Qed.



(* ------------------- EIP20 functions produce no acts ------------------- *)

Lemma EIP20_no_acts : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state (Some msg) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros.
  apply receive_not_payable in H.
    destruct_match in H;
    match goal with
    | H : context [ option_map (fun new_state : State => (new_state, [])) ?m = Some (new_state, new_acts) ] |- _ =>
      destruct m; cbn in H; try congruence; now inversion H
   end.
Qed.

Lemma receive_no_acts : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state (Some msg) = Some (new_state, new_acts) ->
    receive chain ctx prev_state (Some msg) = Some (new_state, []).
Proof.
  intros.
  now apply EIP20_no_acts in H as H1.
Qed.



(* ------------------- Tactic to simplify proof steps ------------------- *)

Ltac receive_simpl_step :=
  match goal with
  | H : receive _ _ _ (Some _) = Some (_, _) |- _ =>
    apply receive_no_acts, receive_not_payable in H; cbn in H
  | H : context[try_transfer] |- _ => unfold try_transfer in H
  | H : context[try_transfer_from] |- _ => unfold try_transfer_from in H
  | H : context[try_approve] |- _ => unfold try_approve in H
  | H : option_map (fun s : State => (s, _)) match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
  | H : option_map (fun s : State => (s, _)) (if ?m then _ else None) = Some _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
  | H : option_map (fun s : State => (s, _)) (if ?m then None else _) = Some _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try rewrite a; cbn in *; try congruence
  end.

Tactic Notation "receive_simpl" := repeat receive_simpl_step.

Ltac FMap_simpl_step :=
  match goal with
    | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => rewrite FMap.find_add
    | H : FMap.find ?t ?m = Some _ |- FMap.find ?t ?m = Some _ => cbn; rewrite H; f_equal; lia
    | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
    | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
    | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] =>rewrite FMap.elements_add_existing; eauto
    | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => rewrite FMap.add_add
    | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add; eauto
    | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
    | |- context [ FMap.find ?x (FMap.partial_alter _ ?x _) ] => rewrite FMap.find_partial_alter
    | H : ?x' <> ?x |- context [ FMap.find ?x' (FMap.partial_alter _ ?x _) ] => rewrite FMap.find_partial_alter_ne; auto
    | H : ?x <> ?x' |- context [ FMap.find ?x' (FMap.partial_alter _ ?x _) ] => rewrite FMap.find_partial_alter_ne
   end.

Tactic Notation "FMap_simpl" := repeat (FMap_simpl_step; cbn).



(* ------------------- FMap partial alter is FMap add ------------------- *)

Lemma add_is_partial_alter_plus : forall (account : Address) amount (balances : FMap Address N) (f : N -> N),
  FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) account balances =
  FMap.add account (with_default 0 (FMap.find account balances) + amount) balances.
Proof.
  intros.
  apply fin_maps.partial_alter_ext. intros. now subst.
Qed.



(* ------------------- sumN function ------------------- *)

Fixpoint sumN {A : Type} (f : A -> N) (xs : list A) : N :=
  match xs with
  | [] => 0
  | x :: xs' => f x + sumN f xs'
  end.

Lemma sumN_permutation {A : Type} {f : A -> N} {xs ys : list A} (perm_eq : Permutation xs ys) :
  sumN f xs = sumN f ys.
Proof.
  induction perm_eq; perm_simplify; lia.
Qed.

Instance sumN_perm_proper {A : Type} :
  Proper (eq ==> Permutation (A:=A) ==> eq) sumN.
Proof.
  repeat intro. subst. now apply sumN_permutation.
Qed.

Lemma sumN_split : forall {A : Type} x y n m (l : list (A * N)),
  sumN (fun '(_, v) => v) ((y, n + m) :: l) =
  sumN (fun '(_, v) => v) ((x, n) :: (y, m) :: l).
Proof.
  cbn. lia.
Qed.

Lemma sumN_swap : forall {A : Type} x y n m (l : list (A * N)),
  sumN (fun '(_, v) => v) ((x, n) :: (y, m) :: l) =
  sumN (fun '(_, v) => v) ((x, m) :: (y, n) :: l).
Proof.
  cbn. lia.
Qed.

Lemma sumN_FMap_add_sub : forall from to amount (balances : FMap Address N),
  amount <= with_default 0 (FMap.find from balances) ->
    (sumN (fun '(_, v) => v) (FMap.elements balances)) =
    (sumN(fun '(_, v) => v)
       (FMap.elements
          (FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) to
             (FMap.add from (with_default 0 (FMap.find from balances) - amount) balances)))).
Proof.
  intros from to amount balances H.
  rewrite add_is_partial_alter_plus; auto.
  destruct (address_eqb from to) eqn:from_to_eq;
    destruct (FMap.find from balances) eqn:from_prev;
    destruct_address_eq; try discriminate; subst; cbn in *;
    repeat match goal with
    | H : _ <= 0 |- _ => apply N.lt_eq_cases in H as [H | H]; try lia; subst
    | |- context [ with_default _ (FMap.find to balances) ] => destruct (FMap.find to balances) eqn:to_prev; cbn
    | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => rewrite FMap.find_add
    | H : FMap.find ?t ?m = Some _ |- FMap.find ?t ?m = Some _ => cbn; rewrite H; f_equal; lia
    | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
    | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
    | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] =>rewrite FMap.elements_add_existing; eauto
    | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => rewrite FMap.add_add
    | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add; eauto
    | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
    | H : FMap.find ?x ?m = Some _ |- context [ sumN _ ((?x, _) :: FMap.elements (FMap.remove ?x ?m)) ] => rewrite fin_maps.map_to_list_delete; auto
    | H : FMap.find ?x _ = Some ?n |- context [ sumN _ ((?x, ?n) :: FMap.elements (FMap.remove ?x _)) ] => rewrite fin_maps.map_to_list_delete; auto
    | H : FMap.find ?x _ = Some ?n |- context [ sumN _ ((?x, ?n) :: (_, _) :: FMap.elements (FMap.remove ?x _)) ] => rewrite sumN_swap, fin_maps.map_to_list_delete; auto
    | |- context [ _ + 0 ] => rewrite N.add_0_r
    | |- context [ 0 + _ ] => rewrite N.add_0_l
    | |- context [ sumN _ ((?t, ?n + ?m) :: _) ] => rewrite sumN_split with (x:=t)
    | |- context [ sumN _ ((_, ?n) :: (_, ?m - ?n) :: _) ] => rewrite <- sumN_split
   end.
Qed.

Definition sum_balances (state : EIP20Token.State) :=
  sumN (fun '(k, v) => v) (FMap.elements (balances state)).



(* ------------------- Expected behvaiour of EIP20 functions ------------------- *)

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
    delegate_allowance_before =? delegate_allowance_after + tokens.

Definition approve_allowance_update_correct (new_state : State) (from delegate : Address) (tokens : TokenValue) :=
  let get_allowance state := with_default 0 (FMap.find delegate (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from state.(allowances)))) in
  let delegate_allowance_after := get_allowance new_state in
    delegate_allowance_after =? tokens.



(* ------------------- Transfer updates correct ------------------- *)

Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct prev_state new_state ctx.(ctx_from) to amount = true.
Proof.
  intros.
  receive_simpl.
  unfold transfer_balance_update_correct.
    destruct_address_eq; destruct (FMap.find (ctx_from ctx) (balances prev_state)) eqn:from_prev;
    cbn in *; try congruence; apply N.ltb_ge in H0; subst; try rewrite from_prev; inversion H; cbn in *.
    - (* case: from =  to && find from = Some n && amount <= n *) 
      FMap_simpl.
      now repeat rewrite N.sub_add, N.eqb_refl.
    - (* case: from =  to && find from = None   && amount = 0 *)
      apply N.lt_eq_cases in H0. destruct H0; try lia. subst. now FMap_simpl.
    - (* case: from <> to && find from = Some n && amount <= n *)
      FMap_simpl.
      rewrite N.sub_add; auto. now repeat rewrite N.eqb_refl.
    - (* case: from <> to && find from = None   && amount = 0 *)
      apply N.lt_eq_cases in H0. destruct H0; try lia. subst.
      FMap_simpl.
      apply N.eqb_refl.
Qed.

Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_transfer_preserves_allowances : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_transfer_preserves_other_balances : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) -> account <> to ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H. cbn. FMap_simpl.
Qed.



(* ------------------- Transfer_from updates correct ------------------- *)

Lemma try_transfer_from_balance_correct : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct prev_state new_state from to amount = true /\
  transfer_from_allowances_update_correct prev_state new_state from ctx.(ctx_from) amount = true.
Proof.
  intros.
  unfold transfer_balance_update_correct.
  unfold transfer_from_allowances_update_correct.
  receive_simpl.
  apply Bool.orb_false_iff in H2 as [H3 H4]; apply N.ltb_ge in H3; apply N.ltb_ge in H4.
  split.
    + (* proof of balance updated correct *)
    destruct_address_eq; destruct (FMap.find from (balances prev_state)) eqn:from_bal_prev;
      subst; try rewrite from_bal_prev; inversion H; cbn in *.
      * (* case: from =  to && find from = Some n && amount <= n *)
        FMap_simpl.
        now repeat rewrite N.sub_add, N.eqb_refl.
      * (* case: from =  to && find from = None   && amount = 0 *)
        apply N.lt_eq_cases in H4. destruct H4; try lia. subst.
        now FMap_simpl.
      * (* case: from <> to && find from = Some n && amount <= n *)
        FMap_simpl.
        rewrite N.sub_add; auto. now repeat rewrite N.eqb_refl.
      * (* case: from <> to && find from = None   && amount = 0 *)
        apply N.lt_eq_cases in H4. destruct H4; try lia. subst.
        FMap_simpl.
        apply N.eqb_refl.
    + (* proof of allowances updated correct *)
      inversion H. cbn. FMap_simpl.
      rewrite N.sub_add; auto. apply N.eqb_refl.
Qed.

Lemma try_transfer_from_preserves_total_supply : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros.
  receive_simpl.
  now inversion H.
Qed.

Lemma try_transfer_from_preserves_other_balances : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> from -> account <> to ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H. cbn. FMap_simpl.
Qed.

Lemma try_transfer_from_preserves_other_allowances : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> from ->
      FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
Proof.
  intros.
  receive_simpl.
  inversion H. cbn. FMap_simpl.
Qed.

Lemma try_transfer_from_preserves_other_allowance : forall prev_state new_state chain ctx from to amount new_acts,
  let get_allowance state account := FMap.find account (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from state.(allowances))) in
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      get_allowance prev_state account = get_allowance new_state account.
Proof.
  intros.
  unfold get_allowance.
  receive_simpl.
  inversion H. cbn. FMap_simpl.
Qed.



(* ------------------- Approve updates correct ------------------- *)

Lemma try_approve_allowance_correct : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
  approve_allowance_update_correct new_state ctx.(ctx_from) delegate amount = true.
Proof.
  intros.
  receive_simpl.
  destruct_match eqn:from_allowance in H; inversion H; cbn; FMap_simpl; apply N.eqb_refl.
Qed.

Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros.
  receive_simpl.
  destruct_match in H; now inversion H.
Qed.

Lemma try_approve_preserves_balances : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (balances prev_state) = (balances new_state).
Proof.
  intros.
  receive_simpl.
  destruct_match in H; now inversion H.
Qed.

Lemma try_approve_preserves_other_allowances : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
Proof.
  intros.
  receive_simpl.
  destruct_match in H;inversion H; cbn; FMap_simpl.
Qed.

Lemma try_approve_preserves_other_allowance : forall prev_state new_state chain ctx delegate amount new_acts,
  let get_allowance state from := FMap.find from (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find (ctx_from ctx) state.(allowances))) in
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    forall account, account <> delegate ->
      get_allowance prev_state account = get_allowance new_state account.
Proof.
  intros.
  receive_simpl.
  unfold get_allowance.
  destruct_match in H;inversion H; cbn; FMap_simpl.
Qed.



(* ------------------- EIP20 functions preserve sum of balances ------------------- *)

Lemma try_transfer_preserves_balances_sum : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros.
  receive_simpl.
  apply N.ltb_ge in H0.
  inversion H.
  unfold sum_balances. cbn.
  now apply sumN_FMap_add_sub.
Qed.

Lemma try_transfer_from_preserves_balances_sum : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros.
  receive_simpl.
  apply Bool.orb_false_iff in H2 as [_ H2].
  apply N.ltb_ge in H2.
  inversion H.
  unfold sum_balances. cbn.
  now apply sumN_FMap_add_sub.
Qed.

Lemma try_approve_preserves_balances_sum : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros.
  receive_simpl.
  destruct_match in H; now inversion H.
Qed.



(* ------------------- Total supply always equals inial supply ------------------- *)

Lemma total_supply_eq_init_supply block_state contract_addr (trace : ChainTrace empty_state block_state) :
  env_contracts block_state contract_addr = Some (contract : WeakContract) ->
  exists cstate deploy_info,
    contract_state block_state contract_addr = Some cstate
    /\ deployment_info _ trace contract_addr = Some deploy_info
    /\ let init_supply := init_amount deploy_info.(deployment_setup) in
      init_supply = total_supply cstate.
Proof.
  contract_induction; intros; try auto.
  - now inversion init_some.
  - destruct msg. destruct m.
    + apply try_transfer_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + apply try_transfer_from_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + apply try_approve_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + cbn in receive_some. unfold receive in receive_some. destruct_match in receive_some; congruence.
  - destruct msg. destruct m.
    + apply try_transfer_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + apply try_transfer_from_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + apply try_approve_preserves_total_supply in receive_some. now rewrite <- receive_some.
    + cbn in receive_some. unfold receive in receive_some. destruct_match in receive_some; congruence.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ => True).
    unset_all; subst;cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.



(* ------------------- Sum of balances always equals total supply ------------------- *)

Lemma sum_balances_eq_total_supply block_state contract_addr :
  reachable block_state ->
  env_contracts block_state contract_addr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state block_state contract_addr = Some cstate
    /\ (total_supply cstate) = (sum_balances cstate).
Proof.
  contract_induction; intros; try auto.
  - inversion init_some. unfold sum_balances. cbn.
    rewrite FMap.elements_add; auto.
    rewrite FMap.elements_empty. cbn. lia.
  - destruct msg. destruct m.
    + apply try_transfer_preserves_balances_sum in receive_some as balance_sum.
      apply try_transfer_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_transfer_from_preserves_balances_sum in receive_some as balance_sum.
      apply try_transfer_from_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_approve_preserves_balances_sum in receive_some as balance_sum.
      apply try_approve_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + cbn in receive_some. unfold receive in receive_some. destruct_match in receive_some; congruence.
  - destruct msg. destruct m.
    + apply try_transfer_preserves_balances_sum in receive_some as balance_sum.
      apply try_transfer_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_transfer_from_preserves_balances_sum in receive_some as balance_sum.
      apply try_transfer_from_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + apply try_approve_preserves_balances_sum in receive_some as balance_sum.
      apply try_approve_preserves_total_supply in receive_some.
      now rewrite <- balance_sum, <- IH.
    + cbn in receive_some. unfold receive in receive_some. destruct_match in receive_some; congruence.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ => True).
    unset_all; subst;cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.


End Theories.
End EIP20Token.
