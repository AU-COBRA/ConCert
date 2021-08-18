(*
  This file contains an implementation of the EIP 20 Token Specification (https://eips.ethereum.org/EIPS/eip-20).
  The implementation is essentially a port of https://github.com/ConsenSys/Tokens/blob/fdf687c69d998266a95f15216b1955a4965a0a6d/contracts/eip20/EIP20.sol
*)
From Coq Require Import ZArith.
From Coq Require Import Morphisms.
From Coq Require Import List.

From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import Extras.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution.Examples Require Import Common.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.
Import RecordSetNotations.

Section EIP20Token.
  Context {BaseTypes : ChainBase}.
  Set Nonrecursive Elimination Schemes.

  Definition TokenValue := N.
  Open Scope N_scope.
  Open Scope bool.

  Inductive Msg :=
  | transfer : Address -> TokenValue -> Msg
  | transfer_from : Address -> Address -> TokenValue -> Msg
  | approve : Address -> TokenValue -> Msg.

  Record State :=
    build_state {
        total_supply : TokenValue;
        balances : AddressMap.AddrMap TokenValue;
        allowances : AddressMap.AddrMap (AddressMap.AddrMap TokenValue)
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
            balances := AddressMap.add setup.(owner) setup.(init_amount) AddressMap.empty;
            allowances := AddressMap.empty |}.

  Definition increment_balance (m : AddressMap.AddrMap TokenValue) (addr : Address) (inc : TokenValue) : AddressMap.AddrMap TokenValue :=
    match AddressMap.find addr m with
    | Some old => AddressMap.add addr (old + inc) m
    | None => AddressMap.add addr inc m
    end.

  (* Transfers <amount> tokens, if <from> has enough tokens to transfer *)
  Definition try_transfer (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
    let from_balance := with_default 0 (AddressMap.find from state.(balances)) in
    if from_balance <? amount
    then None
    else let new_balances := AddressMap.add from (from_balance - amount) state.(balances) in
         let new_balances := increment_balance new_balances to amount in
         Some (state<|balances := new_balances|>).

(* The delegate tries to transfer <amount> tokens from <from> to <to>.
   Succeeds if <from> has indeed allowed the delegate to spend at least <amount> tokens on its behalf. *)
  Definition try_transfer_from (delegate : Address)
       (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
  do from_allowances_map <- AddressMap.find from state.(allowances) ;
  do delegate_allowance <- AddressMap.find delegate from_allowances_map ;
  let from_balance := with_default 0 (AddressMap.find from state.(balances)) in
  if (delegate_allowance <? amount) || (from_balance <? amount)
  then None
  else let new_allowances := AddressMap.add delegate (delegate_allowance - amount) from_allowances_map in
       let new_balances := AddressMap.add from (from_balance - amount) state.(balances) in
       let new_balances := increment_balance new_balances to amount in
       Some (state<|balances := new_balances|><|allowances ::= AddressMap.add from new_allowances|>).

  (* The caller approves the delegate to transfer up to <amount> tokens on behalf of the caller *)
  Definition try_approve (caller : Address)
       (delegate : Address)
       (amount : TokenValue)
       (state : State) : option State :=
    match AddressMap.find caller state.(allowances) with
    | Some caller_allowances =>
      Some (state<|allowances ::= AddressMap.add caller (AddressMap.add delegate amount caller_allowances) |>)
    | None =>
      Some (state<|allowances ::= AddressMap.add caller (AddressMap.add delegate amount AddressMap.empty) |>)
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

(* receive only returns Some if the sender amount is zero *)
Lemma EIP20_not_payable : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
    ((ctx_amount ctx) <= 0)%Z.
Proof.
  intros * receive_some.
  unfold receive in receive_some.
  destruct_match eqn:amount in receive_some.
  - (* case: ctx_amount > 0 *)
    congruence.
  - (* case: ctx_amount <= 0 *)
    now rewrite Z.gtb_ltb, Z.ltb_ge in amount.
Qed.

(* Lemma for simplifying the receive function by eliminating the case
    where sender amount is larger than zero *)
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
  intros * receive_some.
  apply EIP20_not_payable in receive_some as amount_zero.
  unfold receive in receive_some.
  rewrite <- Z.ltb_ge, <- Z.gtb_ltb in amount_zero.
  now rewrite amount_zero in receive_some.
Qed.



(* ------------------- EIP20 functions produce no acts ------------------- *)

(* receive never produces any new_acts *)
Lemma EIP20_no_acts : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  unfold receive, option_map in receive_some.
  repeat destruct_match in receive_some; try congruence.
Qed.

Lemma receive_no_acts : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state (Some msg) = Some (new_state, new_acts) ->
    receive chain ctx prev_state (Some msg) = Some (new_state, []).
Proof.
  intros.
  now erewrite <- EIP20_no_acts.
Qed.



(* ------------------- Default entrypoint always fail ------------------- *)

Lemma default_none : forall prev_state chain ctx,
  receive chain ctx prev_state None = None.
Proof.
  intros.
  unfold receive.
  now destruct_match.
Qed.



(* ------------------- FMap partial alter is FMap add ------------------- *)

Lemma add_is_partial_alter_plus : forall (account : Address) amount (balances : FMap Address N) (f : N -> N),
  FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) account balances =
  FMap.add account (with_default 0 (FMap.find account balances) + amount) balances.
Proof.
  intros.
  now apply fin_maps.partial_alter_ext.
Qed.

Lemma increment_balanace_is_partial_alter_plus : forall (addr : Address) amount (m : FMap Address N),
  increment_balance m addr amount =
  FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) addr m.
Proof.
  intros.
  unfold increment_balance, AddressMap.add, AddressMap.find.
  rewrite add_is_partial_alter_plus by auto.
  destruct_match eqn:addr_in_map;
    now setoid_rewrite addr_in_map.
Qed.



(* ------------------- Tactic to simplify proof steps ------------------- *)

Ltac receive_simpl_step :=
  match goal with
  | H : receive _ _ _ (Some _) = Some (_, _) |- _ =>
    apply receive_no_acts, receive_not_payable in H; cbn in H
  | |- receive _ _ _ (Some _) = Some (_, _) =>
    apply receive_no_acts, receive_not_payable; cbn
  | H : context[receive] |- _ => unfold receive in H
  | |- context[receive] => unfold receive
  | H : context[Blockchain.receive] |- _ => unfold Blockchain.receive; cbn in H
  | H : context[try_transfer] |- _ => unfold try_transfer in H
  | H : context[try_transfer_from] |- _ => unfold try_transfer_from in H
  | H : context[try_approve] |- _ => unfold try_approve in H
  | |- context[Blockchain.receive] => unfold Blockchain.receive; cbn
  | |- context[try_transfer] => unfold try_transfer
  | |- context[try_transfer_from] => unfold try_transfer_from
  | |- context[try_approve] => unfold try_approve
  | H : context [ AddressMap.find _ _ ] |- _ => rewrite AddressMap_find_convertible in H
  | H : context [ AddressMap.add _ _ _ ] |- _ =>  rewrite AddressMap_add_convertible in H
  | H : context [ increment_balance _ _ _ ] |- _ => rewrite increment_balanace_is_partial_alter_plus in H
  | |- context [ AddressMap.find _ _ ] => rewrite AddressMap_find_convertible
  | |- context [ AddressMap.add _ _ _ ] => rewrite AddressMap_add_convertible
  | |- context [ increment_balance _ _ _ ] => rewrite increment_balanace_is_partial_alter_plus
  | H : option_map (fun s : State => (s, _)) match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
  | H : option_map (fun s : State => (s, _)) (if ?m then ?a else ?b) = Some _ |- _ =>
    match a with
    | None =>
      let a := fresh "H" in
      destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
    | _ => match b with
           | None =>
             let a := fresh "H" in
             destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
           | _ => idtac
    end end
  | H : (if ?m then ?a else ?b) = Some _ |- _ =>
    match a with
    | None =>
      let a := fresh "H" in
      destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
    | _ => match b with
           | None =>
             let a := fresh "H" in
             destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
           | _ => idtac
    end end
  end.

Tactic Notation "receive_simpl" := repeat receive_simpl_step.

Ltac FMap_simpl_step :=
  match goal with
    | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => setoid_rewrite FMap.find_add
    | H : FMap.find ?t ?m = Some _ |- FMap.find ?t ?m = Some _ => cbn; rewrite H; f_equal; lia
    | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => setoid_rewrite FMap.find_add_ne; eauto
    | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => setoid_rewrite FMap.find_add_ne; eauto
    | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] => setoid_rewrite FMap.elements_add_existing; eauto
    | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => setoid_rewrite FMap.add_add
    | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => setoid_rewrite FMap.elements_add; eauto
    | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
    | |- context [ FMap.find ?x (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter
    | H : ?x' <> ?x |- context [ FMap.find ?x' (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter_ne; auto
    | H : ?x <> ?x' |- context [ FMap.find ?x' (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter_ne
    | H : context [ AddressMap.find _ _ ] |- _ => rewrite AddressMap_find_convertible in H
    | H : context [ AddressMap.add _ _ _ ] |- _ =>  rewrite AddressMap_add_convertible in H
    | H : context [ increment_balance _ _ _ ] |- _ => rewrite increment_balanace_is_partial_alter_plus in H
    | |- context [ AddressMap.find _ _ ] => rewrite AddressMap_find_convertible
    | |- context [ AddressMap.add _ _ _ ] =>  rewrite AddressMap_add_convertible
    | |- context [ increment_balance _ _ _ ] => rewrite increment_balanace_is_partial_alter_plus
   end.

Tactic Notation "FMap_simpl" := repeat (FMap_simpl_step; cbn).



(* ------------------- isSome function ------------------- *)

Definition isSome {A : Type} (a : option A) := match a with | Some _ => true | None => false end.

(* if x is None then with_default is equal to default element *)
Lemma with_default_is_some : forall {A : Type} (x : option A) (y : A),
  isSome x = false ->
    with_default y x = y.
Proof.
  now destruct x.
Qed.



(* ------------------- sumN function ------------------- *)

(* sumN of balances is the same after transfer changes if sender has enough balance *)
Lemma sumN_FMap_add_sub : forall from to amount (balances : FMap Address N),
  amount <= with_default 0 (FMap.find from balances) ->
    (sumN (fun '(_, v) => v) (FMap.elements balances)) =
    (sumN(fun '(_, v) => v)
       (FMap.elements
          (FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) to
             (FMap.add from (with_default 0 (FMap.find from balances) - amount) balances)))).
Proof.
  intros from to amount balances from_enough_balance.
  rewrite add_is_partial_alter_plus; auto.
  edestruct (address_eqb from to) eqn:from_to_eq;
    destruct FMap.find eqn:from_prev;
    destruct_address_eq; try discriminate; subst; cbn in *;
    repeat match goal with
    | H : _ <= 0 |- _ => apply N.lt_eq_cases in H as [H | H]; try lia; subst
    | |- context [ with_default _ (FMap.find to balances) ] => destruct (FMap.find to balances) eqn:to_prev; cbn
    | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => rewrite FMap.find_add
    | H : FMap.find ?t ?m = Some _ |- FMap.find ?t ?m = Some _ => cbn; rewrite H; f_equal; lia
    | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
    | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
    | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add_existing; eauto
    | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => rewrite FMap.add_add
    | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add; eauto
    | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
    | H : FMap.find ?x ?m = Some _ |- context [ sumN _ ((_, _) :: FMap.elements (FMap.remove ?x ?m)) ] => rewrite fin_maps.map_to_list_delete; auto
    | H : FMap.find ?x _ = Some ?n |- context [ sumN _ ((?x, ?n) :: FMap.elements (FMap.remove ?x _)) ] => rewrite fin_maps.map_to_list_delete; auto
    | H : FMap.find ?x _ = Some ?n |- context [ sumN _ ((?x, ?n) :: (_, _) :: FMap.elements (FMap.remove ?x _)) ] => rewrite sumN_swap, fin_maps.map_to_list_delete; auto
    | |- context [ _ + 0 ] => rewrite N.add_0_r
    | |- context [ 0 + _ ] => rewrite N.add_0_l
    | |- context [ sumN _ ((?t, ?n + ?m) :: _) ] => erewrite sumN_split with (x:= (t, n)) (y := (_, m)) by lia
    | |- context [ sumN _ ((_, ?n) :: (_, ?m - ?n) :: _) ] => erewrite <- sumN_split with (z := (_, n + m - n)) by lia
   end.
   Unshelve. eauto.
Qed.

(* sum of all balances in the token state *)
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

Definition get_allowance state from delegate :=
  with_default 0 (FMap.find delegate (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances state)))).

Definition transfer_from_allowances_update_correct (old_state new_state : State) (from delegate : Address) (tokens : TokenValue) :=
  let delegate_allowance_before := get_allowance old_state from delegate in
  let delegate_allowance_after := get_allowance new_state from delegate in 
    delegate_allowance_before =? delegate_allowance_after + tokens.

Definition approve_allowance_update_correct (new_state : State) (from delegate : Address) (tokens : TokenValue) :=
  let delegate_allowance_after := get_allowance new_state from delegate in
    delegate_allowance_after =? tokens.



(* ------------------- Transfer correct ------------------- *)

(* try_transfer correctly moves <amount> from <sender> to <to> *)
Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct prev_state new_state ctx.(ctx_from) to amount = true.
Proof.
  intros * receive_some.
  unfold transfer_balance_update_correct.
  receive_simpl.
  rename H into sender_enough_balance.
  apply N.ltb_ge in sender_enough_balance.
  destruct_address_eq; destruct (FMap.find (ctx_from ctx) (balances prev_state)) eqn:from_prev;
    try congruence; subst; try rewrite from_prev; inversion receive_some;
    clear receive_some H0 from_prev new_acts chain; cbn in *.
    - (* case: from =  to && find from = Some n && amount <= n *)
      FMap_simpl.
      now rewrite N.sub_add, N.eqb_refl.
    - (* case: from =  to && find from = None   && amount = 0 *)
      apply N.lt_eq_cases in sender_enough_balance as []; [lia | subst].
      now FMap_simpl.
    - (* case: from <> to && find from = Some n && amount <= n *)
      FMap_simpl.
      rewrite N.sub_add; auto.
      now rewrite !N.eqb_refl.
    - (* case: from <> to && find from = None   && amount = 0 *)
      apply N.lt_eq_cases in sender_enough_balance as []; [lia | subst].
      FMap_simpl.
      apply N.eqb_refl.
Qed.

(* try_transfer does not change the total supply of tokens *)
Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

(* try_transfer does not change allowances *)
Lemma try_transfer_preserves_allowances : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (allowances prev_state) = (allowances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

(* try_transfer only modifies the <sender> and <to> balances *)
Lemma try_transfer_preserves_other_balances : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) -> account <> to ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros * receive_some account account_not_sender account_not_receiver.
  receive_simpl.
  inversion receive_some.
  cbn.
  FMap_simpl.
Qed.

(* If the requirements are met then then receive on transfer msg must succeed and
    if receive on transfer msg succeeds then requirements must hold *)
Lemma try_transfer_is_some : forall state chain ctx to amount,
  (ctx_amount ctx >? 0)%Z = false ->
  (amount = 0 /\ isSome (FMap.find (ctx_from ctx) (balances state)) = false)
  \/ amount <= with_default 0 (FMap.find (ctx_from ctx) (balances state))
    <-> isSome (receive chain ctx state (Some (transfer to amount))) = true.
Proof.
  intros * amount_positive.
  split.
  - intros [(amount_zero & sender_balance_some) | sender_enough_balance];
    receive_simpl; destruct_match eqn:amount_from; auto.
    + subst.
      now erewrite with_default_is_some, N.ltb_irrefl by assumption.
    + rewrite <- N.ltb_ge in sender_enough_balance.
      now setoid_rewrite sender_enough_balance.
  - intros receive_some. receive_simpl. rewrite amount_positive in receive_some.
    destruct_match eqn:amount_from in receive_some.
    + discriminate.
    + now apply N.ltb_ge in amount_from.
Qed.



(* ------------------- Transfer_from correct ------------------- *)

(* try_transfer_from correctly updates balance and allowance *)
Lemma try_transfer_from_balance_correct : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct prev_state new_state from to amount = true /\
  transfer_from_allowances_update_correct prev_state new_state from ctx.(ctx_from) amount = true.
Proof.
  intros * receive_some.
  unfold transfer_balance_update_correct,
    transfer_from_allowances_update_correct,
    get_allowance.
  receive_simpl.
  rename H into from_allowances.
  rename H0 into sender_alloance.
  apply Bool.orb_false_iff in H1 as (sender_enough_allowance%N.ltb_ge &
                                     from_enough_balance%N.ltb_ge).
  split.
    + (* proof of balance updated correct *)
    destruct_address_eq;
      destruct (FMap.find from (balances prev_state)) eqn:from_bal_prev;
      subst; try rewrite from_bal_prev; inversion receive_some;
      cbn in *; clear receive_some H0.
      * (* case: from =  to && find from = Some n && amount <= n *)
        FMap_simpl.
        now rewrite N.sub_add, N.eqb_refl.
      * (* case: from =  to && find from = None   && amount = 0 *)
        apply N.lt_eq_cases in from_enough_balance as []; [lia | subst].
        now FMap_simpl.
      * (* case: from <> to && find from = Some n && amount <= n *)
        FMap_simpl.
        rewrite N.sub_add by auto.
        now rewrite ?N.eqb_refl.
      * (* case: from <> to && find from = None   && amount = 0 *)
        apply N.lt_eq_cases in from_enough_balance as []; [lia | subst].
        FMap_simpl.
        apply N.eqb_refl.
    + (* proof of allowances updated correct *)
      inversion receive_some.
      cbn. FMap_simpl.
      rewrite N.sub_add by auto.
      apply N.eqb_refl.
Qed.

(* try_transfer_from does not change total supply of tokens *)
Lemma try_transfer_from_preserves_total_supply : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  now inversion receive_some.
Qed.

(* try_transfer_from only changes <from> and <to> balances *)
Lemma try_transfer_from_preserves_other_balances : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> from -> account <> to ->
      FMap.find account (balances prev_state) = FMap.find account (balances new_state).
Proof.
  intros * receive_some account account_not_from account_not_to.
  receive_simpl.
  inversion receive_some.
  cbn.
  FMap_simpl.
Qed.

(* try_transfer_from only changes allowance map of <from> *)
Lemma try_transfer_from_preserves_other_allowances : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> from ->
      FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
Proof.
  intros * receive_some account account_not_from.
  receive_simpl.
  inversion receive_some.
  cbn.
  FMap_simpl.
Qed.

(* try_transfer_from only changes allowance of <sender> *)
Lemma try_transfer_from_preserves_other_allowance : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      get_allowance prev_state from account = get_allowance new_state from account.
Proof.
  intros * receive_some account account_not_sender.
  unfold get_allowance.
  receive_simpl.
  inversion receive_some.
  cbn.
  FMap_simpl.
Qed.

(* If the requirements are met then then receive on transfer_from msg must succeed and
    if receive on transfer_from msg succeeds then requirements must hold *)
Lemma try_transfer_from_is_some : forall state chain ctx from to amount,
  let get_allowance_ account := FMap.find account (with_default (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances state))) in
  (ctx_amount ctx >? 0)%Z = false ->
  isSome (FMap.find from (allowances state)) = true
  /\ isSome (get_allowance_ (ctx_from ctx)) = true
  /\ amount <= with_default 0 (FMap.find from (balances state))
  /\ amount <= with_default 0 (get_allowance_ (ctx_from ctx))
    <-> isSome (receive chain ctx state (Some (transfer_from from to amount))) = true.
Proof.
  intros * sender_amount_zero.
  split; receive_simpl; rewrite sender_amount_zero in *;
    unfold get_allowance_; clear get_allowance_; cbn.
  - intros (from_allowances_some &
            sender_allowance &
            from_enough_balance%N.ltb_ge &
            sender_enough_allowance%N.ltb_ge).
    destruct_match eqn:allowances_ctx; setoid_rewrite allowances_ctx in sender_allowance; auto.
    setoid_rewrite allowances_ctx in sender_enough_allowance.
    cbn in *. clear from_allowances_some.
    destruct_match eqn:allowance_ctx; setoid_rewrite allowance_ctx in sender_allowance; auto.
    setoid_rewrite allowance_ctx in sender_enough_allowance.
    cbn in *. clear sender_allowance.
    destruct_match eqn:amount_from; auto.
    setoid_rewrite from_enough_balance in amount_from.
    now setoid_rewrite sender_enough_allowance in amount_from.
  - intros receive_some.
    destruct_match eqn:allowances_ctx in receive_some; setoid_rewrite allowances_ctx; try discriminate.
    destruct_match eqn:allowance_ctx in receive_some; setoid_rewrite allowance_ctx; try discriminate.
    destruct_match eqn:amount_from in receive_some; try discriminate.
    apply Bool.orb_false_iff in amount_from as
      (from_enough_balance%N.ltb_ge & sender_enough_allowance%N.ltb_ge).
    intuition.
Qed.



(* ------------------- Approve correct ------------------- *)

(* try_approve correctly replaces allowance *)
Lemma try_approve_allowance_correct : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
  approve_allowance_update_correct new_state ctx.(ctx_from) delegate amount = true.
Proof.
  intros * receive_some.
  unfold approve_allowance_update_correct, get_allowance.
  receive_simpl.
  destruct_match eqn:from_allowance in receive_some;
    inversion receive_some; cbn;
    FMap_simpl; apply N.eqb_refl.
Qed.

(* try_approve does not change total supply of tokens *)
Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (total_supply prev_state) = (total_supply new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  destruct_match in receive_some;
    now inversion receive_some.
Qed.

(* try_approve does not change balances *)
Lemma try_approve_preserves_balances : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (balances prev_state) = (balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  destruct_match in receive_some;
    now inversion receive_some.
Qed.

(* try_approve does not change allowances map of other addresses *)
Lemma try_approve_preserves_other_allowances : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    forall account, account <> (ctx_from ctx) ->
      FMap.find account (allowances prev_state) = FMap.find account (allowances new_state).
Proof.
  intros * receive_some account account_not_sender.
  receive_simpl.
  destruct_match in receive_some;
    inversion receive_some;
    cbn; FMap_simpl.
Qed.

(* try_approve does not change allowance of other addresses *)
Lemma try_approve_preserves_other_allowance : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    forall account, account <> delegate ->
      get_allowance prev_state (ctx_from ctx) account = get_allowance new_state (ctx_from ctx) account.
Proof.
  intros * receive_some account account_not_delegate.
  receive_simpl.
  unfold get_allowance.
  destruct_match eqn:allowances_from in receive_some;
    setoid_rewrite allowances_from;
    inversion receive_some;
    cbn; FMap_simpl.
Qed.

(* If the requirements are met then then receive on approve msg must succeed and
    if receive on approve msg succeeds then requirements must hold *)
Lemma try_approve_is_some : forall state chain ctx delegate amount,
  (ctx_amount ctx >? 0)%Z = false <-> isSome (receive chain ctx state (Some (approve delegate amount))) = true.
Proof.
  split; receive_simpl.
  - intros sender_amount_zero.
    rewrite sender_amount_zero.
    now destruct_match.
  - intros receive_some.
    now destruct_match in receive_some.
Qed.



(* ------------------- EIP20 functions preserve sum of balances ------------------- *)

(* sum of all balances remain the same after proccessing transfer msg *)
Lemma try_transfer_preserves_balances_sum : forall prev_state new_state chain ctx to amount new_acts,
  receive chain ctx prev_state (Some (transfer to amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  rename H into sender_enough_balance.
  apply N.ltb_ge in sender_enough_balance.
  inversion receive_some.
  unfold sum_balances. cbn.
  now apply sumN_FMap_add_sub.
Qed.

(* sum of all balances remain the same after proccessing transfer_from msg *)
Lemma try_transfer_from_preserves_balances_sum : forall prev_state new_state chain ctx from to amount new_acts,
  receive chain ctx prev_state (Some (transfer_from from to amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  rename H into from_allowances.
  rename H0 into sender_allowance.
  rename H1 into enough_balance.
  apply Bool.orb_false_iff in enough_balance as
    (_ & from_enough_balance%N.ltb_ge).
  inversion receive_some.
  unfold sum_balances. cbn.
  now apply sumN_FMap_add_sub.
Qed.

(* sum of all balances remain the same after approve transfer msg *)
Lemma try_approve_preserves_balances_sum : forall prev_state new_state chain ctx delegate amount new_acts,
  receive chain ctx prev_state (Some (approve delegate amount)) = Some (new_state, new_acts) ->
    (sum_balances prev_state) = (sum_balances new_state).
Proof.
  intros * receive_some.
  receive_simpl.
  destruct_match in receive_some;
    now inversion receive_some.
Qed.



(* ------------------- Contract never produces any actions ------------------- *)

Lemma lift_outgoing_acts_nil : forall (bstate : ChainState) (caddr : Address),
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  outgoing_acts bstate caddr = [].
Proof.
  intros * reach deployed.
  apply (lift_outgoing_acts_nil contract); eauto.
  intros.
  now eapply EIP20_no_acts.
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
    + now apply try_transfer_preserves_total_supply in receive_some.
    + now apply try_transfer_from_preserves_total_supply in receive_some.
    + now apply try_approve_preserves_total_supply in receive_some.
    + receive_simpl.
  - destruct msg. destruct m.
    + now apply try_transfer_preserves_total_supply in receive_some.
    + now apply try_transfer_from_preserves_total_supply in receive_some.
    + now apply try_approve_preserves_total_supply in receive_some.
    + receive_simpl.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ _ => True).
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
  - inversion init_some. clear H0.
    unfold sum_balances. cbn.
    setoid_rewrite FMap.elements_add; auto.
    setoid_rewrite FMap.elements_empty. cbn. lia.
  - destruct msg. destruct m.
    + now erewrite try_transfer_preserves_balances_sum,
        try_transfer_preserves_total_supply in IH.
    + now erewrite try_transfer_from_preserves_balances_sum,
        try_transfer_from_preserves_total_supply in IH.
    + now erewrite try_approve_preserves_balances_sum,
        try_approve_preserves_total_supply in IH.
    + receive_simpl.
  - destruct msg. destruct m.
    + now erewrite try_transfer_preserves_balances_sum,
        try_transfer_preserves_total_supply in IH.
    + now erewrite try_transfer_from_preserves_balances_sum,
        try_transfer_from_preserves_total_supply in IH.
    + now erewrite try_approve_preserves_balances_sum,
        try_approve_preserves_total_supply in IH.
    + receive_simpl.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ _ => True).
    unset_all; subst;cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.

End Theories.
End EIP20Token.
