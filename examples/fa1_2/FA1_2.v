(** * FA1.2 token contract *)
(** A basic FA1.2 implementation inspired by the Dexter2 liquidity token FA1.2
    token implementation but with minting and burning removed. *)
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Lia.
Import ListNotations.

Definition non_zero_amount (amt : Z) : bool:= (0 <? amt)%Z.

(** * Contract types *)

Section FA12Types.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

(* Dummy implementation of callbacks. *)
Record callback := {
  return_addr : Address;
}.

Definition callback_addr (c : callback) : Address := c.(return_addr).
Coercion callback_addr : callback >-> Address.

Record transfer_param :=
  build_transfer_param{
    from : Address;
    to : Address;
    value : N
}.

Record approve_param :=
  build_approve_param{
    spender : Address;
    value_ : N
}.

Record getAllowance_param :=
  build_getAllowance_param{
    request : (Address * Address);
    allowance_callback : callback
}.

Record getBalance_param :=
  build_getBalance_param{
    owner_ : Address;
    balance_callback : callback
}.

Record getTotalSupply_param :=
  build_getTotalSupply_param{
    request_ : unit;
    supply_callback : callback
}.

Record State :=
  build_state {
    tokens : FMap Address N;
    allowances : FMap (Address * Address) N;
    total_supply : N
}.

Record Setup :=
  build_setup {
    lqt_provider : Address;
    initial_pool : N
}.

(* Any contract that wants to receive callback messages from the FA1.2 liquidity contract
   should have this type as its Msg type. The contract may have other endpoints,
   as composed in the 'other_msg' constructor. *)
Inductive FA12ReceiverMsg {Msg' : Type} `{Serializable Msg'} :=
  | receive_allowance : N ->  FA12ReceiverMsg
  | receive_balance_of : N -> FA12ReceiverMsg
  | receive_total_supply : N -> FA12ReceiverMsg
  | other_msg : Msg' -> FA12ReceiverMsg.

(* FA1.2 Endpoints. *)
Inductive Msg :=
  | transfer : transfer_param -> Msg
  | approve : approve_param -> Msg
  | getAllowance : getAllowance_param -> Msg
  | getBalance : getBalance_param -> Msg
  | getTotalSupply : getTotalSupply_param -> Msg.

(* begin hide *)
MetaCoq Run (make_setters transfer_param).
MetaCoq Run (make_setters approve_param).
MetaCoq Run (make_setters getAllowance_param).
MetaCoq Run (make_setters getBalance_param).
MetaCoq Run (make_setters getTotalSupply_param).
MetaCoq Run (make_setters State).
MetaCoq Run (make_setters Setup).
(* end hide *)

End FA12Types.

Module Type FA12Serializable.
  Section FA12Serializable.
    Context `{ChainBase}.

    Axiom callback_serializable : Serializable callback.

    Axiom transfer_param_serializable : Serializable transfer_param.

    Axiom approve_param_serializable : Serializable approve_param.

    Axiom getAllowance_param_serializable : Serializable getAllowance_param.

    Axiom getBalance_param_serializable : Serializable getBalance_param.

    Axiom getTotalSupply_param_serializable : Serializable getTotalSupply_param.

    Axiom  FA12ReceiverMsg_serializable : forall {Msg : Type} `{serMsg : Serializable Msg}, Serializable (@FA12ReceiverMsg Msg serMsg).

    Axiom msg_serializable : Serializable Msg.

    Axiom state_serializable : Serializable State.

    Axiom setup_serializable : Serializable Setup.
  End FA12Serializable.
End FA12Serializable.

Module FA12SInstances <: FA12Serializable.
  Section Serialization.
    Context `{ChainBase}.

    Instance  callback_serializable : Serializable callback :=
    Derive Serializable callback_rect <Build_callback>.

    Instance transfer_param_serializable : Serializable transfer_param :=
      Derive Serializable transfer_param_rect <build_transfer_param>.

    Instance approve_param_serializable : Serializable approve_param :=
      Derive Serializable approve_param_rect <build_approve_param>.

    Instance getAllowance_param_serializable : Serializable getAllowance_param :=
      Derive Serializable getAllowance_param_rect <build_getAllowance_param>.

    Instance getBalance_param_serializable : Serializable getBalance_param :=
      Derive Serializable getBalance_param_rect <build_getBalance_param>.

    Instance getTotalSupply_param_serializable : Serializable getTotalSupply_param :=
      Derive Serializable getTotalSupply_param_rect <build_getTotalSupply_param>.

    Instance FA12ReceiverMsg_serializable {Msg : Type} `{serMsg : Serializable Msg} : Serializable (@FA12ReceiverMsg Msg serMsg) :=
      Derive Serializable (@FA12ReceiverMsg_rect Msg serMsg) <
        (@receive_allowance Msg serMsg),
        (@receive_balance_of Msg serMsg),
        (@receive_total_supply Msg serMsg),
        (@other_msg Msg serMsg)>.

    Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <transfer,
                                  approve,
                                  getAllowance,
                                  getBalance,
                                  getTotalSupply>.

  Instance state_serializable : Serializable State :=
    Derive Serializable State_rect <build_state>.

  Instance setup_serializable : Serializable Setup :=
    Derive Serializable Setup_rect <build_setup>.
  End Serialization.
End FA12SInstances.
(* end hide *)


(** * Contract functions *)
Module FA12 (SI : FA12Serializable).
Import SI.

(* begin hide *)
Existing Instance callback_serializable.
Existing Instance transfer_param_serializable.
Existing Instance approve_param_serializable.
Existing Instance getAllowance_param_serializable.
Existing Instance getBalance_param_serializable.
Existing Instance getTotalSupply_param_serializable.
Existing Instance FA12ReceiverMsg_serializable.
Existing Instance msg_serializable.
Existing Instance state_serializable.
Existing Instance setup_serializable.
(* end hide *)

Section FA12Defs.
Context `{BaseTypes : ChainBase}.
Open Scope N_scope.

Definition find_allowance (k : Address * Address) (m : FMap (Address * Address) N) : option N :=
  FMap.find k m.

Definition update_allowance (k : Address * Address) (val : option N) (m : FMap (Address * Address) N) :=
  FMap.update k val m.

Definition empty_allowance : FMap (Address * Address) N := FMap.empty.

(** ** Transfer *)
(** Transfers [amount] tokens, if [from] has enough tokens to transfer
    and [sender] is allowed to send that much on behalf of [from] *)
Definition try_transfer (sender : Address) (param : transfer_param) (state : State) : option State :=
  let allowances_ := state.(allowances) in
  let tokens_ := state.(tokens) in
  do allowances_ <- (* Update allowances *)
    (if address_eqb sender param.(from)
    then Some allowances_
    else
      let allowance_key := (param.(from), sender) in
      let authorized_value := with_default 0 (find_allowance allowance_key allowances_) in
        do _ <- throwIf (authorized_value <? param.(value)) ; (* NotEnoughAllowance *)
        Some (update_allowance allowance_key (maybe (authorized_value - param.(value))) allowances_)
    ) ;
  do tokens_ <- (* Update from balance *)
    (let from_balance := with_default 0 (AddressMap.find param.(from) tokens_) in
      do _ <- throwIf (from_balance <? param.(value)) ; (* NotEnoughBalance *)
      Some (AddressMap.update param.(from) (maybe (from_balance - param.(value))) tokens_)
    ) ;
  let tokens_ :=
    let to_balance := with_default 0 (AddressMap.find param.(to) tokens_) in
      AddressMap.update param.(to) (maybe (to_balance + param.(value))) tokens_ in
    Some (state<|tokens := tokens_|>
               <|allowances := allowances_|>).

(** ** Approve *)
(** The caller approves the [spender] to transfer up to [amount] tokens on behalf of the [sender] *)
Definition try_approve (sender : Address) (param : approve_param) (state : State) : option State :=
  let allowances_ := state.(allowances) in
  let allowance_key := (sender, param.(spender)) in
  let previous_value := with_default 0 (find_allowance allowance_key allowances_) in
  do _ <- throwIf (andb (0 <? previous_value) (0 <? param.(value_))) ; (* UnsafeAllowanceChange *)
  let allowances_ := update_allowance allowance_key (maybe param.(value_)) allowances_ in
    Some (state<|allowances := allowances_|>).

Definition mk_callback (to_addr : Address) (msg : @FA12ReceiverMsg unit _) :=
  act_call to_addr 0 (serialize msg).

Definition receive_allowance_ n := @receive_allowance unit _ n.
Definition receive_balance_of_ n := @receive_balance_of unit _ n.
Definition receive_total_supply_ n := @receive_total_supply unit _ n.

(** ** Get allowance *)
(** Get the quantity that [snd request] is allowed to spend on behalf of [fst request] *)
Definition try_get_allowance (sender : Address) (param : getAllowance_param) (state : State) : list ActionBody :=
  let value := with_default 0 (find_allowance param.(request) state.(allowances)) in
    [mk_callback param.(allowance_callback) (receive_allowance_ value)].

(** ** Get balance *)
(** Get the quantity of tokens belonging to [owner] *)
Definition try_get_balance (sender : Address) (param : getBalance_param) (state : State) : list ActionBody :=
  let value := with_default 0 (AddressMap.find param.(owner_) state.(tokens)) in
    [mk_callback param.(balance_callback) (receive_balance_of_ value)].

(** ** Get total supply *)
(** Get the total supply of tokens *)
Definition try_get_total_supply (sender : Address) (param : getTotalSupply_param) (state : State) : list ActionBody :=
  let value := state.(total_supply) in
    [mk_callback param.(supply_callback) (receive_total_supply_ value)].

(** ** Init *)
(** Initalize contract storage *)
Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : option State :=
  do _ <- throwIf (non_zero_amount ctx.(ctx_amount)); (* DontSendTez *)
  Some {|
    tokens := AddressMap.add setup.(lqt_provider) setup.(initial_pool) AddressMap.empty;
    allowances := empty_allowance;
    total_supply := setup.(initial_pool);
  |}.

(** ** Receive *)
(** Contract main entrypoint *)
Open Scope Z_scope.
Definition receive (chain : Chain) (ctx : ContractCallContext)
                   (state : State) (maybe_msg : option Msg)
                    : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
  let without_statechange acts := Some (state, acts) in
  do _ <- throwIf (non_zero_amount ctx.(ctx_amount)); (* DontSendTez *)
  match maybe_msg with
  | Some (transfer param) => without_actions (try_transfer sender param state)
  | Some (approve param) => without_actions (try_approve sender param state)
  | Some (getAllowance param) => without_statechange (try_get_allowance sender param state)
  | Some (getBalance param) => without_statechange (try_get_balance sender param state)
  | Some (getTotalSupply param) => without_statechange (try_get_total_supply sender param state)
  | None => None (* Transfer actions to this contract are not allowed *)
  end.
Close Scope Z_scope.

Definition contract : Contract Setup Msg State :=
  build_contract init receive.

  End FA12Defs.
End FA12.

Module FA12Instance := FA12 FA12SInstances.
Import FA12Instance.

(** * Properties *)
Section Theories.

Context `{ChainBase}.

Open Scope N_scope.

(* begin hide *)
(* always unfold, if applied *)
Arguments AddressMap.update _ _ _ _ _ /.
Arguments AddressMap.find _ _ _ _/.
Arguments AddressMap.empty _ _/.

Arguments find_allowance _ _ _ /.
Arguments update_allowance _ _ _ _ /.

Arguments non_zero_amount _ /.

Set Keyed Unification.
(* end hide *)

(** ** Contract rejects money *)
(** [receive] only returns Some if the sender amount is zero *)
Lemma contract_not_payable : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
    ((ctx_amount ctx) <= 0)%Z.
Proof.
  intros * receive_some.
  unfold receive, throwIf in receive_some;cbn in receive_some.
  destruct (0 <? _)%Z eqn:amount in receive_some.
  - (* case: ctx_amount > 0 *)
    congruence.
  - (* case: ctx_amount <= 0 *)
    now rewrite Z.ltb_ge in amount.
Qed.

Lemma contract_not_payable' : forall prev_state chain ctx msg,
  (0 < (ctx_amount ctx))%Z ->
    receive chain ctx prev_state msg = None.
Proof.
  intros * ctx_amount_positive.
  unfold receive,throwIf;cbn.
  destruct (0 <? _)%Z eqn:amount.
  - (* case: ctx_amount > 0 *)
    reflexivity.
  - (* case: ctx_amount <= 0 *)
    now apply Z.ltb_ge in amount.
Qed.

(* begin hide *)
Tactic Notation "contract_simpl" := contract_simpl receive init.

Ltac destruct_message :=
  repeat match goal with
  | msg : option Msg |- _ => destruct msg
  | msg : Msg |- _ => destruct msg
  | H : Blockchain.receive _ _ _ _ None = Some _ |- _ => now contract_simpl
  | H : receive _ _ _ None = Some _ |- _ => now contract_simpl
  end.

Hint Rewrite N.ltb_lt N.ltb_ge
  Z.ltb_ge Z.ltb_lt
  Bool.andb_true_iff Bool.andb_false_iff : BoolElim.
(* end hide *)



(** ** Default entrypoint correct *)
(* Default entrypoint should never succeed *)
Lemma default_entrypoint_none : forall prev_state chain ctx,
  receive chain ctx prev_state None = None.
Proof.
  intros *.
  contract_simpl.
  now destruct_match.
Qed.



(** ** Transfer correct *)
Definition transfer_balance_update_correct old_state new_state from to amount :=
  let get_balance addr state := with_default 0 (FMap.find addr state.(tokens)) in
  let from_balance_before := get_balance from old_state in
  let to_balance_before := get_balance to old_state in
  let from_balance_after := get_balance from new_state in
  let to_balance_after := get_balance to new_state in
  (* If the transfer is a self-transfer, balances should remain unchained *)
  if address_eqb from to
  then
    (from_balance_before =? from_balance_after) &&
    (to_balance_before =? to_balance_after)
  else
    (from_balance_before =? from_balance_after + amount) &&
    (to_balance_before + amount =? to_balance_after).

(** [try_transfer] correctly moves [amount] from [from] to [to] *)
Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (transfer param)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct prev_state new_state param.(from) param.(to) param.(value) = true.
Proof.
  intros * receive_some.
  contract_simpl.
  match goal with
    [ H : with_default 0 _ <? _ = false |- _ ] => rename H into enough_balance
  end.
  rewrite N.ltb_ge in enough_balance.
  unfold transfer_balance_update_correct.
  cbn.
  destruct_match eqn:from_to_eqb.
  - (* from = to *)
    destruct (address_eqb_spec param.(from) param.(to)) as [<-|]; auto.
    rewrite !FMap.map_update_idemp.
    rewrite !FMap.find_update_eq with (map:=prev_state.(tokens)).
    destruct (FMap.find (from param) _) eqn:from_prev; cbn in *.
    + now apply maybe_sub_add in enough_balance as [[-> ->] | ->]; rewrite N.eqb_refl.
    + rewrite N.add_0_l.
      apply N.le_0_r in enough_balance.
      now rewrite enough_balance.
  - (* from <> to *)
    destruct (address_eqb_spec param.(from) param.(to)) as [| from_to_eq]; auto.
    rewrite !FMap.find_update_ne with (map:=prev_state.(tokens)) by auto.
    rewrite !FMap.find_update_ne by auto.
    rewrite !FMap.find_update_eq.
    destruct (FMap.find (from param) _) eqn:from_prev; cbn;
      [| apply N.le_0_r in enough_balance; rewrite enough_balance];
    destruct (FMap.find (to param) _) eqn:to_prev; cbn;
    rewrite ?N.add_0_l, ?N.add_0_r, ?N.sub_add, ?N.eqb_refl by auto;
    rewrite andb_true_iff, ?N.eqb_eq;
    cbn in enough_balance.
    * specialize (maybe_cases (n - value param)) as [[-> ?H] | [-> _]];
      specialize (maybe_cases (n0 + value param)) as [[-> ?H] | [-> _]];
      cbn; lia.
    * specialize (maybe_cases (n - value param)) as [[-> ?H] | [-> _]];
      specialize (maybe_cases (value param)) as [[-> ?H] | [-> _]];
      cbn; lia.
    * now specialize (maybe_cases n) as [[-> ?H] | [-> _]].
    * auto.
Qed.

Definition transfer_allowances_update_correct old_state new_state sender from amount :=
  let get_allowance addr1 addr2 state := with_default 0 (FMap.find (addr1, addr2) state.(allowances)) in
  let allowance_before := get_allowance from sender old_state in
  let allowance_after := get_allowance from sender new_state in
  (* If the from and sender is equal, allowances should remain unchained *)
  if address_eqb sender from
  then
    (allowance_before =? allowance_after)
  else
    (allowance_before =? allowance_after + amount).

(** [try_transfer] correctly subtracts [amount] from allowances if [sender] is not [from] *)
Lemma try_transfer_allowance_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (transfer param)) = Some (new_state, new_acts) ->
  transfer_allowances_update_correct prev_state new_state ctx.(ctx_from) param.(from) param.(value) = true.
Proof.
  intros * receive_some.
  contract_simpl.
  unfold transfer_allowances_update_correct.
  cbn.
  destruct_match eqn:sender_from_eqb.
  - (* sender = from *)
    match goal with
    [ H : Some (allowances _) = Some _ |- _ ] => rename H into allowances_eq
    end.
    inversion_clear allowances_eq.
    now rewrite N.eqb_refl.
  - (* sender <> from *)
    contract_simpl.
    match goal with
    [ H : with_default 0 (FMap.find _ (allowances _)) <? _ = false |- _ ] => rename H into enough_allowance
    end.
    rewrite N.ltb_ge in enough_allowance.
    rewrite FMap.find_update_eq.
    destruct (FMap.find (from param, ctx_from ctx) (allowances prev_state)) eqn:from_prev; cbn.
    + unfold maybe.
      destruct (n - value param =? 0) eqn:n_eq_value; cbn.
      * apply Neqb_ok in n_eq_value.
        rewrite N.sub_0_le in n_eq_value.
        erewrite (N.le_antisymm n _) by eassumption.
        now rewrite !N.eqb_refl.
      * now rewrite N.sub_add, N.eqb_refl.
    + apply N.le_0_r in enough_allowance.
      now rewrite enough_allowance.
Qed.

(** [try_transfer] does not produce any new actions *)
Lemma try_transfer_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (transfer param)) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  contract_simpl.
Qed.

(** [try_transfer] does not change the total supply of tokens *)
Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (transfer param)) = Some (new_state, new_acts) ->
    total_supply prev_state = total_supply new_state.
Proof.
  intros * receive_some.
  contract_simpl.
Qed.

(** [try_transfer] only modifies the [from] and [to] balances *)
Lemma try_transfer_preserves_other_balances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (transfer param)) = Some (new_state, new_acts) ->
    forall account, account <> param.(from) -> account <> param.(to) ->
      FMap.find account (tokens prev_state) = FMap.find account (tokens new_state).
Proof.
  intros * receive_some account account_not_from account_not_to.
  contract_simpl.
  cbn.
  now rewrite !FMap.find_update_ne.
Qed.

(** [try_transfer] only modifies the [sender] and [from] allowances *)
Lemma try_transfer_preserves_other_allowances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (transfer param)) = Some (new_state, new_acts) ->
    forall allowance_key, allowance_key <> (param.(from), ctx.(ctx_from)) ->
      FMap.find allowance_key (allowances prev_state) = FMap.find allowance_key (allowances new_state).
Proof.
  intros * receive_some account allowance_key_ne.
  contract_simpl.
  cbn.
  match goal with
    [ H : _ = Some _ |- _ ] => rename H into allowance_eq
  end.
  destruct_address_eq.
  - (* from = sender *)
    now inversion_clear allowance_eq.
  - (* from <> sender *)
    destruct_match in allowance_eq;
      inversion_clear allowance_eq.
    now rewrite !FMap.find_update_ne.
Qed.

(** [try_transfer] removes empty entries from allowances map *)
Lemma try_transfer_remove_empty_allowances : forall prev_state new_state chain ctx new_acts param,
  (forall n, FMap.find (param.(from), ctx.(ctx_from)) (allowances prev_state) = Some n -> n > 0) ->
  receive chain ctx prev_state (Some (transfer param)) = Some (new_state, new_acts) ->
    forall n, FMap.find (param.(from), ctx.(ctx_from)) (allowances new_state) = Some n -> n > 0.
Proof.
  intros * IH receive_some *.
  contract_simpl.
  destruct_match in *.
  - now contract_simpl.
  - contract_simpl.
    rewrite !FMap.find_update_eq.
    now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
Qed.

(** [try_transfer] removes empty entries from balance map *)
Lemma try_transfer_remove_empty_balances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (transfer param)) = Some (new_state, new_acts) ->
    forall n,
    (FMap.find param.(from) (tokens new_state) = Some n -> n > 0) /\
    (FMap.find param.(to) (tokens new_state) = Some n -> n > 0).
Proof.
  intros * receive_some *.
  contract_simpl.
  rewrite N.ltb_ge in *.
  destruct (address_eqb_spec param.(from) param.(to)) as [<-|]; auto.
  - rewrite !FMap.find_update_eq.
    now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
  - rewrite !FMap.find_update_ne by auto.
    rewrite !FMap.find_update_eq.
    rewrite !FMap.find_update_ne with (map := prev_state.(tokens)) by auto.
    specialize (maybe_cases ) as [[-> ?H] | [-> ?H]];
    now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
Qed.

(** If the requirements are met then then receive on transfer msg must succeed and
    if receive on transfer msg succeeds then requirements must hold *)
Lemma try_transfer_is_some : forall state chain ctx param,
  (ctx_amount ctx <= 0)%Z /\
  param.(value) <= with_default 0 (FMap.find param.(from) (tokens state)) /\
  (param.(from) <> ctx.(ctx_from) ->
    param.(value) <= with_default 0 (FMap.find (param.(from), ctx.(ctx_from)) (allowances state)))
    <-> exists new_state new_acts, receive chain ctx state (Some (transfer param)) = Some (new_state, new_acts).
Proof.
  split.
  - intros (amount_zero & enough_balance & enough_allowance).
    apply Z.ltb_ge in amount_zero.
    cbn.
    rewrite amount_zero;cbn.
    destruct_match eqn:allowances_eq;
    destruct_match eqn:sender_from_eqb in allowances_eq; try congruence;
    try destruct_match eqn:enough_allowance_check in allowances_eq; try congruence;
    try destruct_match eqn:new_balance;
    try destruct_match eqn:enough_balance_check in new_balance; try congruence.
    + (* case no contradictions *)
      inversion_clear allowances_eq.
      now inversion_clear new_balance.
    + (* enough balances contradiction *)
      contract_simpl.
      apply N.ltb_lt in enough_balance_check.
      now apply N.le_ngt in enough_balance.
    + (* case: no contradictions *)
      inversion_clear allowances_eq.
      now inversion_clear new_balance.
    + (* enough balances contradiction *)
      contract_simpl.
      apply N.ltb_lt in enough_balance_check.
      now apply N.le_ngt in enough_balance.
    + (* enough allowance contradiction *)
      contract_simpl.
      apply N.ltb_lt in enough_allowance_check.
      destruct (address_eqb_spec ctx.(ctx_from) param.(from)) as [| sender_from_ne]; try discriminate.
      now apply not_eq_sym, enough_allowance, N.le_ngt in sender_from_ne.
  - intros (new_state & new_acts & receive_some).
    contract_simpl.
    rewrite Z.ltb_ge in *.
    split; try assumption.
    rewrite N.ltb_ge in *.
    destruct_match eqn:sender_from_eqb in *.
      destruct (address_eqb_spec ctx.(ctx_from) param.(from)) as
        [send_from_eq | sender_from_ne];contract_simpl;try discriminate.
    +  (* sender = from *)
       now split.
    + (* sender <> from *)
      destruct_match eqn:enough_allowance in *; try congruence.
      contract_simpl.
      now apply N.ltb_ge in enough_allowance.
Qed.



(** ** Approve correct *)
(** [try_approve] correctly sets allowance of [(sender, spender)] to [value_] *)
Lemma try_approve_allowance_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (approve param)) = Some (new_state, new_acts) ->
    FMap.find (ctx.(ctx_from), param.(spender)) (allowances new_state) = maybe param.(value_).
Proof.
  intros * receive_some.
  contract_simpl.
  cbn.
  now rewrite !FMap.find_update_eq.
Qed.

(** [try_approve] does not produce any new actions *)
Lemma try_approve_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (approve param)) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  contract_simpl.
Qed.

(** [try_approve] does not change allowances map of other addresses *)
Lemma try_approve_preserves_other_allowances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (approve param)) = Some (new_state, new_acts) ->
    forall allowance_key, allowance_key <> (ctx.(ctx_from), param.(spender)) ->
      FMap.find allowance_key (allowances prev_state) = FMap.find allowance_key (allowances new_state).
Proof.
  intros * receive_some allowance_key allowance_key_ne.
  contract_simpl.
  cbn.
  now rewrite FMap.find_update_ne.
Qed.

(** [try_approve] does not change total supply of tokens *)
Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (approve param)) = Some (new_state, new_acts) ->
    total_supply prev_state = total_supply new_state.
Proof.
  intros * receive_some.
  now contract_simpl.
Qed.

(** [try_approve] does not change balances *)
Lemma try_approve_preserves_balances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (approve param)) = Some (new_state, new_acts) ->
    tokens prev_state = tokens new_state.
Proof.
  intros * receive_some.
  now contract_simpl.
Qed.

(** [try_approve] removes empty entries from allowances map *)
Lemma try_approve_remove_empty_allowances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (approve param)) = Some (new_state, new_acts) ->
    forall n, FMap.find (ctx.(ctx_from), param.(spender)) (allowances new_state) = Some n -> n > 0.
Proof.
  intros * IH receive_some *.
  contract_simpl.
  cbn.
  rewrite FMap.find_update_eq.
  now specialize (maybe_cases ) as [[-> ?H] | [-> ?H]].
Qed.

(** If the requirements are met then then receive on approve msg must succeed and
    if receive on approve msg succeeds then requirements must hold *)
Lemma try_approve_is_some : forall state chain ctx param,
  (ctx_amount ctx <= 0)%Z /\
  (with_default 0 (FMap.find (ctx.(ctx_from), param.(spender)) (allowances state)) = 0 \/ param.(value_) = 0)
    <-> exists new_state new_acts, receive chain ctx state (Some (approve param)) = Some (new_state, new_acts).
Proof.
  split;
    intros;
    destruct_hyps;
    contract_simpl;
    now autorewrite with BoolElim in *.
Qed.



(** ** Get allowance correct *)
(** [try_get_allowance] produces a callback to the correct contract with
    the requested allowance, the call should carry no balance *)
Lemma try_get_allowance_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (getAllowance param)) = Some (new_state, new_acts) ->
    new_acts = [
      act_call param.(allowance_callback) 0%Z (serialize
        (receive_allowance (with_default 0 (FMap.find param.(request) (allowances prev_state)))))
    ].
Proof.
  intros * receive_some.
  now contract_simpl.
Qed.

(** [try_get_allowance] does not modify state *)
Lemma try_get_allowance_preserves_state : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (getAllowance param)) = Some (new_state, new_acts) ->
    prev_state = new_state.
Proof.
  intros * receive_some.
  now contract_simpl.
Qed.

(** If the requirements are met then then receive on get_allowance msg must succeed and
    if receive on get_allowance msg succeeds then requirements must hold *)
Lemma try_get_allowance_is_some : forall prev_state chain ctx param,
  (ctx_amount ctx <= 0)%Z <->
  exists new_state new_acts, receive chain ctx prev_state (Some (getAllowance param)) = Some (new_state, new_acts).
Proof.
  split;
    intros;
    destruct_hyps;
    contract_simpl;
    now autorewrite with BoolElim in *.
Qed.



(** ** Get balance correct *)
(** [try_get_balance] produces a callback to the correct contract with
    the requested balance, the call should carry no balance *)
Lemma try_get_balance_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (getBalance param)) = Some (new_state, new_acts) ->
    new_acts = [
      act_call param.(balance_callback) 0%Z (serialize
        (receive_balance_of (with_default 0 (FMap.find param.(owner_) (tokens prev_state)))))
    ].
Proof.
  intros * receive_some.
  now contract_simpl.
Qed.

(** [try_get_balance] does not modify state *)
Lemma try_get_balance_preserves_state : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (getBalance param)) = Some (new_state, new_acts) ->
    prev_state = new_state.
Proof.
  intros * receive_some.
  now contract_simpl.
Qed.

(** If the requirements are met then then receive on getBalance msg must succeed and
    if receive on getBalance msg succeeds then requirements must hold *)
Lemma try_get_balance_is_some : forall prev_state chain ctx param,
  (ctx_amount ctx <= 0)%Z <->
  exists new_state new_acts, receive chain ctx prev_state (Some (getBalance param)) = Some (new_state, new_acts).
Proof.
  split;
    intros;
    destruct_hyps;
    contract_simpl;
    now autorewrite with BoolElim in *.
Qed.



(** ** Get total supply correct *)
(** [try_get_total_supply] produces a callback to the correct contract with
    the total supply of tokens, the call should carry no balance *)
Lemma try_get_total_supply_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (getTotalSupply param)) = Some (new_state, new_acts) ->
    new_acts = [
      act_call param.(supply_callback) 0%Z (serialize
        (receive_total_supply prev_state.(total_supply)))
    ].
Proof.
  intros * receive_some.
  now contract_simpl.
Qed.

(** [try_get_total_supply] does not modify state *)
Lemma try_get_total_supply_preserves_state : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (getTotalSupply param)) = Some (new_state, new_acts) ->
    prev_state = new_state.
Proof.
  intros * receive_some.
  now contract_simpl.
Qed.

(** If the requirements are met then then receive on get_total_supply msg must succeed and
    if receive on get_total_supply msg succeeds then requirements must hold *)
Lemma try_get_total_supply_is_some : forall prev_state chain ctx param,
  (ctx_amount ctx <= 0)%Z <->
  exists new_state new_acts, receive chain ctx prev_state (Some (getTotalSupply param)) = Some (new_state, new_acts).
Proof.
  split;
    intros;
    destruct_hyps;
    contract_simpl;
    now autorewrite with BoolElim in *.
Qed.



(** ** Init correct *)
(** After initalization no accounts should hold tokens *)
Lemma init_balances_correct : forall chain ctx setup state,
  init chain ctx setup = Some state ->
    state.(tokens) = FMap.add setup.(lqt_provider) setup.(initial_pool) FMap.empty.
Proof.
  intros * init_some.
  now contract_simpl.
Qed.

(** After initalization no allowances should be set *)
Lemma init_allowances_correct : forall chain ctx setup state,
  init chain ctx setup = Some state ->
    state.(allowances) = FMap.empty.
Proof.
  intros * init_some.
  now contract_simpl.
Qed.

Lemma init_total_supply_correct : forall chain ctx setup state,
  init chain ctx setup = Some state ->
    state.(total_supply) = setup.(initial_pool).
Proof.
  intros * init_some.
  now contract_simpl.
Qed.

(** initialization should always succeed *)
Lemma init_is_some : forall chain ctx setup,
  exists state, init chain ctx setup = state.
Proof.
  intros.
  eauto.
Qed.

(* begin hide *)
Ltac try_solve_acts_correct :=
  match goal with
  | [ H : receive _ _ _ _ = Some _ |- _ ] =>
    first [apply try_transfer_new_acts_correct in H
          |apply try_approve_new_acts_correct in H
          |apply try_get_allowance_new_acts_correct in H
          |apply try_get_balance_new_acts_correct in H
          |apply try_get_total_supply_new_acts_correct in H ];
    subst;eauto
  end.

Ltac try_solve_preserves_state :=
  match goal with
  | [ H : receive _ _ _ _ = Some _ |- _ ] =>
    first [apply try_get_allowance_preserves_state in H
          |apply try_get_balance_preserves_state in H
          |apply try_get_total_supply_preserves_state in H];
    subst;eauto
  end.
(* end hide *)



(** ** Outgoing acts facts *)
(** If contract emits self calls then they are for the receive entrypoints (which do not exits) *)
Lemma only_getter_self_calls bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  Forall (fun act_body =>
    match act_body with
    | act_transfer to _ => False
    | act_call to _ msg => to = caddr ->
        (exists n, msg = serialize (receive_allowance n)) \/
        (exists n, msg = serialize (receive_balance_of n)) \/
        (exists n, msg = serialize (receive_total_supply n))
    | _ => False
    end) (outgoing_acts bstate caddr).
Proof.
  contract_induction; intros; auto.
  - now inversion IH.
  - apply Forall_app; split; auto.
    clear IH. simpl in *.
    destruct msg.
    + destruct m;
        try_solve_acts_correct.
    + contract_simpl.
  - inversion_clear IH as [|? ? head_not_me tail_not_me].
    destruct head;
      try contradiction.
    destruct action_facts as (? & ? & ? & ?).
    subst.
    destruct head_not_me as [[] | [[] | []]]; auto;
      subst;
      now contract_simpl.
  - now rewrite <- perm.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ _ => True).
    unset_all; subst;cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.

(** Contract never calls itself *)
Lemma no_self_calls : forall bstate origin from_addr to_addr amount msg acts ctx prev_state new_state resp_acts,
  reachable bstate ->
  env_contracts bstate to_addr = Some (contract : WeakContract) ->
  chain_state_queue bstate =
  {| act_origin := origin;
     act_from := from_addr;
     act_body :=
       match msg with
       | Some msg => act_call to_addr amount msg
       | None => act_transfer to_addr amount
    end |} :: acts ->
  wc_receive contract bstate ctx prev_state msg = Some (new_state, resp_acts) ->
  from_addr <> to_addr.
Proof.
  intros * reach deployed queue receive_some.
  apply only_getter_self_calls in deployed as no_self_calls; auto.
  unfold outgoing_acts in no_self_calls.
  rewrite queue in no_self_calls.
  cbn in no_self_calls.
  destruct_address_eq; auto.
  inversion_clear no_self_calls as [|? ? hd _].
  destruct msg; auto.
  destruct hd as [[] | [[] | []]];
    auto; subst;
    eapply wc_receive_strong in receive_some as (_ & ? & _ & _ & msg_correct & _);
    now destruct_match in msg_correct.
Qed.

(** The contract never produces actions carrying money *)
Lemma new_acts_amount_zero : forall prev_state chain ctx msg new_state new_acts,
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
    sumZ (fun act => act_body_amount act) new_acts = 0%Z.
Proof.
  intros * receive_some.
  destruct msg.
  - destruct m;try_solve_acts_correct.
  - contract_simpl.
Qed.

Lemma outgoing_acts_amount_zero : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  Forall (fun act => act_body_amount act = 0%Z) (outgoing_acts bstate caddr).
Proof.
  intros * reach deployed.
  apply (lift_outgoing_acts_prop contract); auto.
  intros * receive_some. simpl in *.
  destruct msg.
  - destruct m;try_solve_acts_correct.
  - contract_simpl.
Qed.

(** Contract only produces contract call actions *)
Lemma outgoing_acts_are_calls : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  Forall (fun act_body =>
    match act_body with
    | act_call _ _ _ => True
    | _ => False
    end) (outgoing_acts bstate caddr).
Proof.
  intros * reach deployed.
  apply (lift_outgoing_acts_prop contract); auto.
  intros * receive_some; simpl in *.
  destruct msg.
  - destruct m; try_solve_acts_correct.
  - contract_simpl.
Qed.



(** ** Contract balance facts *)
(** Contract balance should always be zero *)
Lemma contract_initial_balance_bound : forall bstate caddr (trace : ChainTrace empty_state bstate),
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists deploy_info,
    deployment_info Setup trace caddr = Some deploy_info
    /\ deploy_info.(deployment_amount) = 0%Z.
Proof.
  contract_induction; intros; auto.
  - instantiate (DeployFacts := fun _ ctx => (0 <= ctx_amount ctx)%Z).
    unfold DeployFacts in facts.
    contract_simpl.
    now propify.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (CallFacts := fun _ _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    now apply Z.ge_le.
Qed.

Lemma contract_balance_bound' : forall bstate caddr (trace : ChainTrace empty_state bstate),
  let effective_balance := (env_account_balances bstate caddr - (sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr)))%Z in
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists deploy_info,
    deployment_info Setup trace caddr = Some deploy_info
    /\ effective_balance = deploy_info.(deployment_amount).
Proof.
  intros.
  subst effective_balance.
  contract_induction; intros; auto.
  - cbn.
    lia.
  - cbn in IH.
    lia.
  - instantiate (CallFacts := fun _ ctx _ _ =>
      (0 <= ctx_amount ctx)%Z /\ ctx_from ctx <> ctx_contract_address ctx).
    destruct facts as (ctx_amount_positive & _).
    simpl in *.
    apply contract_not_payable in receive_some as not_payable.
    apply new_acts_amount_zero in receive_some as amount_zero_new_acts.
    apply Z.le_antisymm in ctx_amount_positive; auto.
    rewrite ctx_amount_positive, Z.sub_0_r in IH.
    now rewrite sumZ_app, amount_zero_new_acts, Z.add_0_l.
  - now destruct facts.
  - now erewrite sumZ_permutation in IH by eauto.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros.
    subst. cbn.
    split.
    + now apply Z.ge_le.
    + rewrite deployed in *.
      match goal with
      | H : Some ?x = Some _ |- _ => inversion H; subst x; clear H
      end.
      now eapply no_self_calls.
Qed.

Lemma contract_balance_bound : forall bstate caddr (trace : ChainTrace empty_state bstate),
  env_contracts bstate caddr = Some (contract : WeakContract) ->
    env_account_balances bstate caddr = 0%Z.
Proof.
  intros * trace deployed.
  specialize contract_balance_bound' as (dep_info & deployment_info_eq & balance_bound); eauto.
  specialize contract_initial_balance_bound as (dep_info' & deployment_info_eq' & balance_init_bound); eauto.
  rewrite deployment_info_eq in deployment_info_eq'.
  Unshelve. all: eauto.
  injection deployment_info_eq' as ->.
  rewrite balance_init_bound in balance_bound.
  apply outgoing_acts_amount_zero in deployed as act_amount_zero;
    try now constructor.
  rewrite <- balance_bound.
  rewrite Zminus_0_l_reverse, Z.sub_cancel_l at 1.
  clear balance_init_bound balance_bound deployment_info_eq dep_info' trace deployed.
  induction (outgoing_acts bstate caddr).
  - reflexivity.
  - cbn.
    apply list.Forall_cons in act_amount_zero as (act_amount_zero & acts_amount_zero).
    rewrite act_amount_zero, Z.add_0_l.
    now apply IHl.
Qed.



(** ** Total supply / token balance facts *)
(** Sum of all token balances *)
Definition sum_balances state :=
  sumN (fun '(k, v) => v) (FMap.elements (tokens state)).

(** The balance of a single account is always less than
   or equal to the sum of all balances *)
Lemma balance_le_sum_balances : forall addr state,
  with_default 0 (FMap.find addr (tokens state)) <= sum_balances state.
Proof.
  intros.
  destruct FMap.find eqn:balance.
  - eapply FMap.In_elements, sumN_in_le in balance.
    eapply N.le_trans; cycle 1; eauto.
  - apply N.le_0_l.
Qed.

(** [total_supply] is always equal to the sum of all account token balances *)
Lemma sum_balances_eq_total_supply : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ total_supply cstate = sum_balances cstate.
Proof.
  intros * reach deployed.
  apply (lift_contract_state_prop contract);
    intros *;simpl in *; auto; clear reach deployed bstate caddr.
  - intros init_some.
    unfold sum_balances.
    erewrite init_total_supply_correct, init_balances_correct; eauto.
    rewrite FMap.elements_add, FMap.elements_empty by auto.
    now cbn.
  - intros IH receive_some.
    destruct msg. destruct m.
    + erewrite <- try_transfer_preserves_total_supply; eauto.
      rename t into param.
      unfold sum_balances.
      contract_simpl.
      cbn.
      rewrite N.ltb_ge in *.
      destruct (address_eqb_spec param.(from) param.(to)) as
        [<-| from_to_ne];
        [rewrite FMap.find_update_eq | rewrite FMap.find_update_ne by auto];
        destruct (FMap.find (from param) _) eqn:from_balance;
        destruct (FMap.find (to param) (tokens cstate)) eqn:to_balance;
        destruct param;cbn in *;
          unshelve (repeat match goal with
            | H : ?x = ?y |- context [ ?x ] => rewrite H
            | H : _ <= 0 |- _ => apply N.lt_eq_cases in H as [H | H]; try lia; subst
            | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => rewrite FMap.find_add
            | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => rewrite FMap.add_add
            | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
            | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => rewrite FMap.find_add_ne; eauto
            | H : ?x <> ?y |- context [ FMap.find ?x (FMap.remove ?y _) ] => rewrite FMap.find_remove_ne; eauto
            | H : ?y <> ?x |- context [ FMap.find ?x (FMap.remove ?y _) ] => rewrite FMap.find_remove_ne; eauto
            | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add_existing; eauto
            | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => rewrite FMap.elements_add; eauto
            | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
            | H : FMap.find ?x ?m = Some _ |- context [ sumN _ ((_, _) :: FMap.elements (FMap.remove ?x ?m)) ] => rewrite fin_maps.map_to_list_delete; auto
            | H : FMap.find ?x _ = Some ?n |- context [ sumN _ ((?x, ?n) :: (_, _) :: FMap.elements (FMap.remove ?x _)) ] => rewrite sumN_swap, fin_maps.map_to_list_delete; auto
            | |- context [ sumN _ ((?t, ?n + ?m) :: _) ] => erewrite sumN_split with (x:= (t, n)) (y := (_, m)) by lia
            | |- context [ sumN _ ((_, 0) :: (?x, ?n) :: _) ] => erewrite <- sumN_split with (z := (x, n)) by auto
            | |- context [ sumN _ ((_, ?n) :: (?x, ?m - ?n) :: _) ] => erewrite <- sumN_split with (z := (x, n + m - n))
            | |- context [ sumN _ ((?x, ?m - ?n) :: (_, ?n) :: _) ] => erewrite <- sumN_split with (z := (x, n + m - n))
            | |- context [ with_default _ None ] => unfold with_default
            | |- context [ with_default _ (Some _) ] => unfold with_default
            | |- context [ FMap.update _ None _ ] => unfold FMap.update
            | |- context [ FMap.update _ (Some _) _ ] => unfold FMap.update
            | |- context [ 0 + _ ] => rewrite N.add_0_l
            | |- context [ _ + 0 ] => rewrite N.add_0_r
            | |- context [ 0 - _ ] => rewrite N.sub_0_l
            | |- context [ _ - 0 ] => rewrite N.sub_0_r
            | H : ?x <= ?y, G : ?y - ?x = 0 |- _ => rewrite N.sub_0_le in G; apply N.le_antisymm in G
            | H : ?x + ?y = 0 |- _ => apply N.eq_add_0 in H as []
            | H : ?x = 0 |- _ => subst x
            | |- context [ FMap.update ?k _ (FMap.update ?k _ _) ] => rewrite FMap.map_update_idemp
            | H : ?y <= ?x |- context [ maybe (with_default 0 (maybe (?x - ?y)) + ?y) ] => apply maybe_sub_add in H as [[-> ->] | ->]
            | H : FMap.find ?x ?m = Some 0 |- context [ FMap.elements (FMap.remove ?x _) ] =>
                rewrite <- N.add_0_r; change 0 with ((fun '(_, v) => v) (x, 0)); rewrite sumN_inv; rewrite fin_maps.map_to_list_delete
            | H : FMap.find ?k ?m = None |- context [ FMap.remove ?k _ ] => rewrite fin_maps.delete_notin
            | |- context [ maybe _ ] => specialize maybe_cases as [[-> ?H] | [-> _]]
            | H : ?y <> ?x |- context [ sumN _ ((?x, ?n) :: FMap.elements (FMap.remove ?y _)) ] =>
                cbn; rewrite N.add_comm; change n with ((fun '(_, v) => v) (y, n)); rewrite sumN_inv
           end);try easy.
    + erewrite <- try_approve_preserves_total_supply; eauto.
      unfold sum_balances.
      erewrite <- try_approve_preserves_balances; eauto.
    + try_solve_preserves_state.
    + try_solve_preserves_state.
    + try_solve_preserves_state.
    + now rewrite default_entrypoint_none in receive_some.
Qed.

(** Account token balances are always less than or equal to [total_supply] *)
Lemma token_balance_le_total_supply : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ forall addr, with_default 0 (FMap.find addr (tokens cstate)) <= total_supply cstate.
Proof.
  intros * reach deployed.
  apply sum_balances_eq_total_supply in deployed as
    (cstate & deployed_state & sum_eq_supply); auto.
  eexists.
  rewrite deployed_state, sum_eq_supply.
  clear reach deployed_state sum_eq_supply caddr bstate.
  split; auto.
  intros.
  apply balance_le_sum_balances.
Qed.



(** ** Empty map entries removed *)
(** The [tokens] map never stores entries of zero *)
Lemma zero_balances_removed : forall bstate caddr (trace : ChainTrace empty_state bstate),
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists depinfo cstate,
    deployment_info Setup trace caddr = Some depinfo /\
    contract_state bstate caddr = Some cstate /\
    let initial_tokens := initial_pool (deployment_setup depinfo) in
    initial_tokens > 0 ->
    forall addr n, FMap.find addr (tokens cstate) = Some n -> n > 0.
Proof.
  intros * deployed.
  apply (lift_dep_info_contract_state_prop contract);
    auto; intros *; clear deployed trace bstate caddr.
  - intros init_some initial_pool_positive * addr_some.
    unfold Blockchain.init in *.
    erewrite init_balances_correct in addr_some; eauto.
    cbn in *.
    destruct (address_eqb_spec addr (lqt_provider setup)) as [<-| addr_ne] in addr_some.
    + now rewrite FMap.find_add in addr_some.
    + now rewrite FMap.find_add_ne in addr_some.
  - intros IH receive_some initial_pool_positive * addr_some.
    unfold Blockchain.receive in receive_some.
    simpl in receive_some.
    destruct msg. destruct m.
    + destruct t.
      specialize (address_eqb_spec addr from0) as [<- | addr_from_ne];
      only 2: specialize (address_eqb_spec addr to0) as [<- | addr_to_ne].
      * (* case: addr = from *)
        now eapply try_transfer_remove_empty_balances in receive_some.
      * (* case: addr = to *)
        now eapply try_transfer_remove_empty_balances in receive_some.
      * (* case: addr is not related to transaction *)
        eapply try_transfer_preserves_other_balances in receive_some; eauto.
        now rewrite <- receive_some in addr_some.
    + now erewrite <- try_approve_preserves_balances in addr_some.
    + apply try_get_allowance_preserves_state in receive_some.
      now subst.
    + apply try_get_balance_preserves_state in receive_some.
      now subst.
    + apply try_get_total_supply_preserves_state in receive_some.
      now subst.
    + contract_simpl.
Qed.

(** The [allowances] map never stores entries of zero *)
Lemma zero_allowances_removed : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate /\
    forall sender from n, FMap.find (sender, from) (allowances cstate) = Some n -> n > 0.
Proof.
  intros * reach deployed.
  apply (lift_contract_state_prop contract);
    intros *; auto; clear reach deployed bstate caddr.
  - intros init_some * addr_some. unfold Blockchain.init in *.
    erewrite init_allowances_correct in addr_some by eauto.
    now rewrite FMap.find_empty in addr_some.
  - intros IH receive_some * addr_some.
    unfold Blockchain.receive in receive_some.
    simpl in receive_some.
    destruct msg. destruct m.
    + destruct t.
      specialize (address_eqb_spec ctx.(ctx_from) from0) as [<- | addr_from_ne];
      only 1: specialize (address_eqb_spec from1 sender) as [<- | addr_from_ne].
      * now eapply try_transfer_remove_empty_allowances in receive_some.
      * eapply try_transfer_preserves_other_allowances in receive_some.
       -- now rewrite <- receive_some in addr_some.
       -- intros HH.
          now inversion HH.
      * eapply try_transfer_preserves_other_allowances in receive_some.
       -- now rewrite <- receive_some in addr_some.
       -- intros HH.
          now inversion HH.
    + destruct a.
      specialize (address_eqb_spec ctx.(ctx_from) sender) as [<- | addr_from_ne];
      only 1: specialize (address_eqb_spec spender0 from0) as [<- | addr_from_ne].
      * now eapply try_approve_remove_empty_allowances in receive_some.
      * eapply try_approve_preserves_other_allowances in receive_some.
       -- now rewrite <- receive_some in addr_some.
       -- intros HH.
          now inversion HH.
      * eapply try_approve_preserves_other_allowances in receive_some.
       -- now rewrite <- receive_some in addr_some.
       -- intros HH.
          now inversion HH.
    + apply try_get_allowance_preserves_state in receive_some.
      now subst.
    + apply try_get_balance_preserves_state in receive_some.
      now subst.
    + apply try_get_total_supply_preserves_state in receive_some.
      now subst.
    + contract_simpl.
Qed.



(** ** Total supply correct *)

Open Scope Z_scope.

(** [total_supply] is equal to the initial tokens *)
Lemma total_supply_correct : forall bstate caddr (trace : ChainTrace empty_state bstate),
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate depinfo,
    contract_state bstate caddr = Some cstate /\
    deployment_info Setup trace caddr = Some depinfo /\
    let initial_tokens := initial_pool (deployment_setup depinfo) in
      cstate.(total_supply) = initial_tokens.
Proof.
  contract_induction;
    intros; auto.
  - cbn. unfold Blockchain.init in *.
    now erewrite init_total_supply_correct by eauto.
  - instantiate (CallFacts := fun _ ctx state _ =>
      ctx_from ctx <> ctx_contract_address ctx).
    unfold Blockchain.receive in receive_some.
    simpl in *.
    destruct msg. destruct m.
    + erewrite <- try_transfer_preserves_total_supply; eauto.
    + erewrite <- try_approve_preserves_total_supply; eauto.
    + now eapply try_get_allowance_preserves_state in receive_some.
    + now eapply try_get_balance_preserves_state in receive_some.
    + now eapply try_get_total_supply_preserves_state in receive_some.
    + contract_simpl.
  - now destruct facts.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros.
    subst. cbn.
    rewrite deployed in *.
    match goal with
    | H : Some ?x = Some _ |- _ => inversion H; subst x; clear H
    end.
    now eapply no_self_calls.
Qed.

End Theories.
