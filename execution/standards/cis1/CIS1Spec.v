(** * Concordium's CIS1 *)

(** See the original CIS1 standard: http://proposals.concordium.software/CIS/cis-1.html *)

(**
 The formalisation defines module types that specify what functionality should be
 provided by a function that implements the standard.

Covered by the formalisation:

- Specifications of [transfer], [balanceOf] and [operatorUpdate].

- Proofs that these functions peserve the sum of all balances for all token ids. The properties hold for any contract that satisfies the CIS1 specification defined in this formalisation.

Not covered by the fomalisation:

- Concordium serialisation.

- Logging the events (logs are currently not supported by ConCert).

- Metadata.


The approach to formalisation is inspired by Murdoch Gabbay, Arvid Jakobsson, Kristina Sojakova. Money grows on (proof-)trees: the formal FA1.2 ledger standard.


The CIS1 standard is, however, more general:

- the standard allows for multiple tokens on obe contracts, which makes it possible to define both fungible and non-fungible tokens;

- the transfers happen in batch mode.

 *)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Examples Require Import Common.
From ConCert.Execution.Standards.CIS1 Require Import CIS1Utils.

From MetaCoq.Template Require Import monad_utils.

From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import ZArith.

Import ListNotations.
Import MonadNotation.
Import RemoveProperties.

(** * General types *)

(** NOTE: In CIS1 it's an n-byte sequence, where 0 <= n <= 256.
   We model it as an unbounded number [nat] *)
Definition TokenID := nat.

Definition TokenAmount := nat.

Open Scope program_scope.

(** Supported entry points *)
Inductive CIS1_entry_points :=
| CIS1_transfer
| CIS1_updateOperator
| CIS1_balanceOf.

(** CIS1:
<<
ReceiveHookParameter ::= (id: TokenID) (amount: TokenAmount) (from: Address)
                         (contract: ContractName) (data: AdditionalData).
>> *)

(** NOTE: there is no notion of a contract name in ConCert; [AdditionalData] is not handled at the moment *)
Definition receive_hook_params `{ChainBase} : Type := TokenID * TokenAmount * Address.

(** All addresses owning tokens must supoort the following interface, since all receiving
    addresses are notified with a receive hook. The rest of the functionality is captured
    by the [other_msg] constructor *)
Inductive CIS1ReceiverMsg (Msg : Type) `{Serializable Msg} `{ChainBase} :=
| CIS1_receiver_receive_hook : receive_hook_params -> CIS1ReceiverMsg Msg
| CIS1_receiver_other_msg : Msg -> CIS1ReceiverMsg Msg.

(* begin hide *)
Global Instance CIS1ReceiverMsg_serializable {Msg : Type} `{serMsg : Serializable Msg} `{cb : ChainBase} : Serializable (@CIS1ReceiverMsg Msg serMsg _) :=
  Derive Serializable (@CIS1ReceiverMsg_rect Msg serMsg cb) <
    (@CIS1_receiver_receive_hook Msg serMsg cb),
    (@CIS1_receiver_other_msg Msg serMsg cb)>.
(* end hide *)

(** Abstract types of messages and storage (the contract's state) *)
Module Type CIS1Types.

  Parameter Msg : Type.
  Parameter Storage : Type.

End CIS1Types.

(** * Views *)

(** A module type that defines a view interface. The interface specifies functions for
    observing the contract's state. These functions are used to defined the specification.  *)
Module Type CIS1View (cis1_types : CIS1Types).

  Import cis1_types.

  Parameter get_CIS1_entry_point : Msg -> option CIS1_entry_points.

  Parameter get_balance_opt : forall `{ChainBase}, Storage -> TokenID -> Address -> option TokenAmount.

  Parameter get_operators : forall `{ChainBase}, Storage -> Address -> list Address.

  Parameter get_owners : forall `{ChainBase}, Storage -> TokenID -> list Address.

  Axiom get_owners_no_dup : forall `{ChainBase} st token_id, NoDup (get_owners st token_id).

  (** Owners determined by their balances *)
  Axiom get_owners_balances : forall `{ChainBase} st owner token_id,
    In owner (get_owners st token_id) <->
    exists balance, get_balance_opt st token_id owner = Some balance.

  Parameter token_id_exists : Storage -> TokenID -> bool.

  Parameter get_token_ids : Storage -> list TokenID.

  Definition get_balance `{ChainBase} : Storage -> TokenID -> Address -> option TokenAmount :=
    fun st token_id addr => if token_id_exists st token_id then
                              match get_balance_opt st token_id addr with
                              | Some bal => Some bal
                              | None => Some 0
                              end
                            else None.

  Definition get_balance_total `{ChainBase}
             (st : Storage)
             (token_id : TokenID)
             (p : token_id_exists st token_id = true)
             (addr : Address) : TokenAmount :=
    let o := get_balance st token_id addr in
    match o as o' return (o' = o -> _) with
    | Some bal => fun _ => bal
    | None => fun heq => False_rect _ (ltac:(intros;subst o; unfold get_balance in *;rewrite p in *;
    destruct (get_balance_opt st token_id addr);congruence))
    end eq_refl.

End CIS1View.

(** The module below specifies an abstract interface of the CIS1 token along with the properties
    that must be satisfied by each entry point required by the standard. *)
Module Type CIS1Axioms (cis1_types : CIS1Types) (cis1_view : CIS1View cis1_types).

  Import cis1_types.
  Import cis1_view.

  (** * Contract functions *)

  (** CIS1: A smart contract implementing CIS1 MUST export three functions [transfer], [updateOperator] and [balanceOf]. *)

  Axiom supports_transfer : exists msg, get_CIS1_entry_point msg = Some CIS1_transfer.

  Axiom supports_updateOperator : exists msg, get_CIS1_entry_point msg = Some CIS1_transfer.

  Axiom supports_blanceOf : exists msg, get_CIS1_entry_point msg = Some CIS1_balanceOf.

  (** ** Transfer *)

  (** *** Parameter *)

  (** NOTE: not handling additional data at the moment *)
  Record CIS1_transfer_data `{ChainBase} :=
  { cis1_td_token_id : TokenID;
    cis1_td_amount   : TokenAmount;
    cis1_td_from     : Address;
    cis1_td_to       : Address }.

  Record CIS1_transfer_params `{ChainBase} :=
    { cis_tr_transfers : list CIS1_transfer_data }.

  (** Some utils for getting data from the parameters. *)
  Definition transfer_to `{ChainBase} : CIS1_transfer_params -> list (TokenID * Address) :=
    fun params => map (fun x => (x.(cis1_td_token_id), x.(cis1_td_to))) params.(cis_tr_transfers).

  Definition transfer_from `{ChainBase} : CIS1_transfer_params -> list (TokenID * Address) :=
  fun params => map (fun x => (x.(cis1_td_token_id), x.(cis1_td_from))) params.(cis_tr_transfers).

  Definition get_receive_hook_params `{ChainBase} (params : list CIS1_transfer_data)
  : list (Address * receive_hook_params) :=
  map (fun x => (x.(cis1_td_to), (x.(cis1_td_token_id), x.(cis1_td_amount), x.(cis1_td_from)))) params.


  (** *** Requirements *)

  (** A specification for a single transfer of a particular token id between [from] and [to]. *)
  Definition transfer_single_spec
             `{ChainBase}
             (prev_st next_st : Storage)
             (token_id : TokenID)
             (p : token_id_exists prev_st token_id = true)
             (q : token_id_exists next_st token_id = true)
             (from : Address)
             (to : Address)
             (amount : TokenAmount) : Prop :=
    let prev_from := get_balance_total prev_st token_id p from in
    let next_from := get_balance_total next_st token_id q from in
    let prev_to := get_balance_total prev_st token_id p to in
    let next_to := get_balance_total next_st token_id q to in
    (** The balances that are not [to] and [from] (for the token with [token_id]) remain unchanged *)
    (forall addr, addr <> from ->
             addr <> to ->
             get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr) /\
    (** The balances of all other tokens that are not equal to [token_id] remain unchanged for all addresses *)
    (forall addr other_token_id, other_token_id <> token_id ->
                            get_balance_opt next_st other_token_id addr = get_balance_opt prev_st other_token_id addr) /\
    (** Token ids are preserved by a single transfer *)
    (forall token_id,
        token_id_exists prev_st token_id =  token_id_exists next_st token_id) /\
    (** CIS1: A transfer MUST non-strictly decrease the balance of the from address and non-strictly increase the balance of the to address *)
    prev_from = next_from + amount /\
    next_to = prev_to + amount.

  (** CIS1: The list of transfers MUST be executed in order. *)
  Fixpoint compose_transfers
           `{ChainBase}
           (init_st : Storage)
           (final_st : Storage)
           (params : list CIS1_transfer_data)
           (single_transfer :
              forall (prev_st next_st : Storage)
                     (params : CIS1_transfer_data),
                token_id_exists prev_st params.(cis1_td_token_id) = true ->
                token_id_exists next_st params.(cis1_td_token_id) = true -> Prop)
    : Prop :=
    match params with
    | [] => init_st = final_st
    | pr :: ps =>
     (** NOTE: we require that for each transfer, the updated state [st] becomes the initial state for the next transfer *)
      exists (st : Storage)
        (p: token_id_exists init_st pr.(cis1_td_token_id) = true)
        (q : token_id_exists st pr.(cis1_td_token_id) = true),
      single_transfer init_st st pr p q /\ compose_transfers st final_st ps single_transfer
    end.

  (** A receive hook call is valid if the call parameters are deserialised to a [CIS1_receiver_receive_hook]
      constructor with appropriate data *)
  Definition is_valid_receive_hook `{cb : ChainBase} (p : receive_hook_params) (serialized_params : SerializedValue) : Prop :=
    exists (Msg : Type) (sMsg : Serializable Msg) (msg : @CIS1ReceiverMsg Msg sMsg cb), deserialize serialized_params =
                                                                            Some (@CIS1_receiver_receive_hook Msg sMsg _  p).

  (** A specification for the batch transfer *)
  Record transfer_spec `{ChainBase}
         (params : CIS1_transfer_params)
         (prev_st next_st : Storage)
         (ret_ops : list ActionBody) : Prop :=
    {
      transfer_dec_inc :
        compose_transfers prev_st next_st params.(cis_tr_transfers)
                         (fun st1 st2 x p q =>
                            transfer_single_spec
                              st1
                              st2
                              x.(cis1_td_token_id) p q
                              x.(cis1_td_from)
                              x.(cis1_td_to)
                                  x.(cis1_td_amount));

      (** CIS1: A transfer of any amount of a token type to a contract address MUST call receive hook function on the receiving smart contract with a receive hook parameter. *)
      transfer_receive_hook_calls :
      (** We consider only transfers to addresses that are contracts *)
      let transfers_to_contracts := filter (fun x => address_is_contract x.(cis1_td_to)) params.(cis_tr_transfers) in
      Forall (fun '(op,(to_addr, params)) =>
                exists val,
                  op = act_call to_addr 0%Z val /\
                 is_valid_receive_hook params val)
             (combine ret_ops (get_receive_hook_params transfers_to_contracts)) /\
      ret_ops = map (fun '(to_addr, params) => act_call to_addr 0 (serialize params))
                    (get_receive_hook_params transfers_to_contracts)
    }.

  (** ** updateOperator *)

  (** *** Parameter *)
  Inductive CIS1_updateOperator_kind :=
    cis1_ou_remove_operator
  | cis1_ou_add_operator.

  Record CIS1_updateOperator_update `{ChainBase} :=
    { cis1_ou_update_kind : CIS1_updateOperator_kind;
      cis1_ou_operator_address : Address }.

  Record CIS1_updateOperator_params `{ChainBase} :=
    { cis1_ou_params : list CIS1_updateOperator_update }.

  (** *** Requirements *)

  (** A specification for the update of a single operator *)
  Definition updateOperator_single_spec  `{ChainBase} (ctx : ContractCallContext) (prev_st next_st : Storage) (p : CIS1_updateOperator_update) : Prop :=
    match p.(cis1_ou_update_kind) with
    | cis1_ou_remove_operator =>
      let addr := p.(cis1_ou_operator_address) in
      (** All operators, apart from [addr] remain the same in both states *)
      (forall addr0, addr0 <> addr ->
                In addr0 (get_operators prev_st ctx.(ctx_from)) <->
                In addr0 (get_operators next_st ctx.(ctx_from))) /\
      (** An operator "to remove" is removed (not present) for the caller *)
      ~ In addr (get_operators next_st ctx.(ctx_from))
    | cis1_ou_add_operator =>
      let addr := p.(cis1_ou_operator_address) in
      (** All operators, apart from [addr] remain the same in both states *)
      (forall addr0, addr0 <> addr ->
                In addr0 (get_operators prev_st ctx.(ctx_from)) <->
                In addr0 (get_operators next_st ctx.(ctx_from))) /\
      (* an operator "to add" is recorded for the caller *)
      In addr (get_operators next_st ctx.(ctx_from))
    end.

  (** CIS1: The list of updates MUST be executed in order. *)
  Fixpoint compose_uptadeOperator_specs `{ChainBase} (ctx : ContractCallContext) (st final_st : Storage) (updates : list CIS1_updateOperator_update) :=
    match updates with
    | [] => st = final_st
    | p :: ps => exists next_st, updateOperator_single_spec ctx st next_st p /\
                     compose_uptadeOperator_specs ctx next_st final_st ps
    end.

  (** A specification of the batch operatior update *)
  Record updateOperator_spec `{ChainBase}
         (ctx : ContractCallContext)
         (params : CIS1_updateOperator_params)
         (prev_st next_st : Storage)
         (ret_ops : list ActionBody) :=
    { updateOperator_token_ids_preserved :
        forall token_id,
          token_id_exists prev_st token_id =  token_id_exists next_st token_id;

      updateOperator_balances_preserved : forall addr token_id,
        get_balance_opt prev_st token_id addr = get_balance_opt next_st token_id addr;

      updateOperator_add_remove :
        compose_uptadeOperator_specs ctx prev_st next_st params.(cis1_ou_params)
    }.


  (** ** balanceOf *)

  (** *** Parameter *)

  Record CIS1_balanceOf_query `{ChainBase} :=
    { cis1_bo_query_token_id : TokenID;
      cis1_bo_query_address  : Address }.

  Record CIS1_balanceOf_params `{ChainBase} :=
    { cis1_bo_query : list CIS1_balanceOf_query;
      cis1_bo_result_address : Address;
      cis1_bo_result_address_is_contract : address_is_contract cis1_bo_result_address = true}.

  (** CIS1: The parameter for the callback receive function is a list of pairs, where each pair is a query and an amount of tokens.*)
  Definition balanceOf_callback_type `{ChainBase} : Type := list (TokenID * Address * TokenAmount).

  (** *** Requirements *)

  (** CIS1: The contract function MUST reject if any of the queries fail.

  The [get_balance] function returns [None] (fails) if the token id is unknown.
  We combine the calls to [get_balance] using [monad_map] where the monad is the [option] monad.
   *)
  Definition get_balances `{ChainBase} (st : Storage) (params : CIS1_balanceOf_params) : option balanceOf_callback_type :=
    monad_map
      (fun q =>
         let addr := q.(cis1_bo_query_address) in
         let token_id := q.(cis1_bo_query_token_id) in
         balance <- get_balance st token_id addr;;
         Some (token_id, addr, balance)) params.(cis1_bo_query).

  Record balanceOf_spec
         `{ChainBase}
         (params : CIS1_balanceOf_params)
         (prev_st next_st : Storage)
         (ret_ops : list ActionBody) : Prop :=
    { balanceOf_operators_preserved:
      forall addr, get_operators next_st addr = get_operators prev_st addr;

      balanceOf_token_ids_preserved :
        forall token_id,
          token_id_exists prev_st token_id =  token_id_exists next_st token_id;

      balanceOf_balances_preserved :
        forall token_id addr, get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr;

     (** NOTE: It's assumed that the receiving contract accepts messages of type [balanceOf_callback_type] *)
      balanceOf_callback :
      match get_balances prev_st params with
        | Some query_results =>
          let serialized_query_results := serialize query_results in
          let op := act_call params.(cis1_bo_result_address) 0%Z serialized_query_results in
          ret_ops = [op]
        | None => False
        end
    }.

  End CIS1Axioms.

(** * CIS1 properties  *)

(** ** Operator updates *)

Module CIS1Operators (cis1_types : CIS1Types) (cis1_view : CIS1View cis1_types)
       (cis1_axioms : CIS1Axioms cis1_types cis1_view).

  (** Sanity checks for the batch operator update spec *)

  (** NOTE: the properties could be extended further, if more gurantees about uperator updates are
      required from the standard *)

  Import cis1_types cis1_view cis1_axioms.
  Import Lia.

  Lemma compose_updateOperator_add_add :
    forall `{ChainBase} (ctx : ContractCallContext)
           (prev_st : Storage) (next_st : Storage) (addr1 addr2 : Address),
      let add_addr1 := {| cis1_ou_update_kind := cis1_ou_add_operator;
                         cis1_ou_operator_address := addr1 |} in
      let add_addr2 := {| cis1_ou_update_kind := cis1_ou_add_operator;
                            cis1_ou_operator_address := addr2 |} in
      compose_uptadeOperator_specs ctx prev_st next_st [add_addr1; add_addr2] ->
      In addr1 (get_operators next_st ctx.(ctx_from)).
   Proof.
     intros ? ? ? ? ? ? ? ? H. simpl in *.
     destruct H as [st1 [Hst1 [st2 [Hst2 Heq]]]]. subst. cbn in *.
     destruct Hst1. destruct Hst2 as [H2 ?].
     destruct (address_eqb_spec addr1 addr2);subst;auto.
     apply H2;auto.
   Qed.

  Lemma compose_updateOperator_add_remove_same :
    forall `{ChainBase} (ctx : ContractCallContext)
      (prev_st : Storage) (next_st : Storage) (addr : Address),
      let add_addr := {| cis1_ou_update_kind := cis1_ou_add_operator;
                         cis1_ou_operator_address := addr |} in
      let remove_addr := {| cis1_ou_update_kind := cis1_ou_remove_operator;
                            cis1_ou_operator_address := addr |} in
      compose_uptadeOperator_specs ctx prev_st next_st [add_addr; remove_addr] ->
      ~ In addr (get_operators next_st ctx.(ctx_from)).
   Proof.
     intros ? ? ? ? ? ? ? H. simpl in *.
     destruct H as [st1 [Hst1 [st2 [Hst2 Heq]]]]. subst. cbn in *.
     destruct Hst2.
     assumption.
   Qed.

   Lemma compose_updateOperator_remove_one_remove_another :
    forall `{ChainBase} (ctx : ContractCallContext)
      (prev_st : Storage) (next_st : Storage) (addr1 addr2 : Address),
      addr1 <> addr2 ->
      let remove_addr := {| cis1_ou_update_kind := cis1_ou_remove_operator;
                            cis1_ou_operator_address := addr1 |} in
      let add_addr := {| cis1_ou_update_kind := cis1_ou_add_operator;
                         cis1_ou_operator_address := addr2 |} in
      compose_uptadeOperator_specs ctx prev_st next_st [remove_addr; add_addr] ->
      ~ In addr1 (get_operators next_st ctx.(ctx_from)).
   Proof.
     intros ? ? ? ? ? ? Hneq ? ? H. simpl in *.
     destruct H as [st1 [Hst1 [st2 [Hst2 Heq]]]]. subst. cbn in *.
     destruct Hst1. destruct Hst2 as [H2 ?].
     intro. specialize (H2 _ Hneq). easy.
   Qed.

End CIS1Operators.


(** ** Balances *)
Module CIS1Balances (cis1_types : CIS1Types) (cis1_view : CIS1View cis1_types)
       (cis1_axioms : CIS1Axioms cis1_types cis1_view).

  (** In this module we prove properties related to the preservation of the sum of all balances for
      all token ids.

      These properties follow directly from the specification. That means, in particular, that all
      the contracts that satisfy the specification will automatically satisfy all the properties we
      prove here. *)

  Import cis1_types cis1_view cis1_axioms.
  Import Lia.

  (* begin hide *)

  Definition addr_eq_dec `{ChainBase} (a1 a2 : Address) : {a1 = a2} + {a1 <> a2} :=
    match address_eqb_spec a1 a2 with
    | ssrbool.ReflectT _ p => left p
    | ssrbool.ReflectF _ p => right p
    end.

  (* end hide *)

  (** Get the balance and return zero if [get_balance] returns [None] *)
  Definition get_balance_default `{ChainBase} : Storage -> TokenID -> Address -> TokenAmount :=
    fun st token_id addr => match get_balance st token_id addr with
                         | Some amount => amount
                         | None => 0
                         end.


  (** We sum up all the balances for a given [token_id] for a list of [owners]  *)
  Definition sum_balances `{ChainBase} (st : Storage) (token_id : TokenID) (owners : list Address) :=
    fold_right (fun addr s => get_balance_default st token_id addr + s) 0 owners.

  (** This is an important lemma that is used to prove the main result about the sum of balances.
      The lemma states that we can split the sum of all balances into two parts: the balance of a particular [owner] (which can be zero) and the sum of all _other_ balances (with [owner] removed). *)
  Lemma remove_owner `{ChainBase} st token_id (owners : list Address) (owner : Address) :
    In owner owners \/ get_balance_default st token_id owner = 0 ->
    NoDup owners ->
    sum_balances st token_id owners = get_balance_default st token_id owner + sum_balances st token_id (remove addr_eq_dec owner owners).
  Proof.
    intros Hin.
    destruct Hin as [Hin | Hbal].
    revert dependent owner.
    -induction owners;intros owner Hin Hnodup.
     + inversion Hin.
     + inversion Hin;subst;clear Hin.
       * simpl.
         destruct (addr_eq_dec owner owner);try congruence.
         inversion Hnodup;subst;clear Hnodup.
         now rewrite not_in_remove_same.
       * inversion Hnodup;subst;clear Hnodup.
         simpl.
         destruct (addr_eq_dec owner a).
         ** easy.
         ** simpl. rewrite (IHowners owner);auto;lia.
    - rewrite Hbal;cbn.
      induction owners; intros Hnodup;auto;inversion Hnodup;subst;clear Hnodup.
      simpl. destruct (addr_eq_dec owner a);subst;simpl;easy.
  Qed.

  (* begin hide *)

  (** An auxiliary lemma. *)
  Lemma sum_of_balances_eq `{ChainBase} addrs prev_st next_st token_id :
    (forall addr, In addr addrs ->get_balance_default next_st token_id addr = get_balance_default prev_st token_id addr) ->
    sum_balances next_st token_id addrs = sum_balances prev_st token_id addrs.
  Proof.
    intros Hbal.
    induction addrs;simpl in *;intuition;auto.
  Qed.
  (* end hide *)


  Hint Resolve remove_In not_in_remove_same not_in_remove remove_remove neq_not_removed : hints.
  Hint Resolve remove_extensional : hints.

  (* begin hide *)
  (** A technical lemma: the sum of balances is the same for two lists of owners containing the
      same addresses (without duplication) *)
  Lemma sum_balances_extensional `{ChainBase} st token_id owners1 owners2 :
    NoDup owners1 ->
    NoDup owners2 ->
    (forall addr, In addr owners1 <-> In addr owners2) ->
    sum_balances st token_id owners1 = sum_balances st token_id owners2.
  Proof.
    intros Hnodup1 Hnodup2 Hiff.
    revert dependent owners2.
    induction owners1;intros.
    + cbn in *. destruct owners2;auto.
      destruct (Hiff a);cbn in *;intuition.
    + simpl.
      destruct (Hiff a) as [H1 H2];cbn in *.
      specialize (H1 (or_introl eq_refl)) as HH.
      rewrite remove_owner with (st0 := st) (owner := a) (owners:=owners2);auto with hints.
      inversion Hnodup1;subst.
      rewrite IHowners1 with (owners2 := (remove addr_eq_dec a owners2));eauto with hints.
      intros. split.
      * intros Hin.
        destruct (Hiff addr) as [HH1 HH2];cbn in.
        specialize (HH1 (or_intror Hin)) as HH1.
        destruct (address_eqb_spec a addr).
        ** now subst.
        ** auto with hints.
      * intros Hin.
        destruct (Hiff addr);cbn in.
        destruct (address_eqb_spec a addr).
        ** assert (~ In addr (remove addr_eq_dec a owners2)).
           { intros Hin0. subst. apply (remove_In _ _ _ Hin0). }
           easy.
        ** assert (In addr owners2) by eauto with hints.
           intuition.
  Qed.
  (* end hide *)

  (** An important lemma stating that the sum of balances in two states is the same for the same owners, if the balances in the two states agree.
   This lemma is used to make a connection between the sum of balances and the properties of [transfer] given by the specification *)
  Lemma sum_of_balances_eq_extensional `{ChainBase} owners1 owners2 prev_st next_st token_id :
    NoDup owners1 ->
    NoDup owners2 ->
    (forall addr, In addr owners1 <-> In addr owners2) ->
    (forall addr, In addr owners1 -> get_balance_default next_st token_id addr = get_balance_default prev_st token_id addr) ->
    sum_balances next_st token_id owners1 = sum_balances prev_st token_id owners2.
  Proof.
    intros.
    erewrite sum_of_balances_eq by eauto.
    apply sum_balances_extensional;auto.
  Qed.

  Lemma get_balance_opt_default `{ChainBase} next_st prev_st token_id addr :
    token_id_exists prev_st token_id = token_id_exists next_st token_id ->
    get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr ->
    get_balance_default next_st token_id addr = get_balance_default prev_st token_id addr.
  Proof.
    intros Hids Hopt.
    unfold get_balance_default,get_balance.
    rewrite Hids.
    destruct (token_id_exists next_st token_id);auto.
    destruct (get_balance_opt next_st token_id addr) eqn:Heq1;
    destruct (get_balance_opt prev_st token_id addr) eqn:Heq2;auto;
      inversion H;try congruence.
  Qed.

  (** The owners are the same in two states if the balances agree. We generalise the statement to cover the case when we ignore certain addresses given by [ignore_addrs].  *)
  Lemma same_owners_remove_all  `{ChainBase} token_id ignore_addrs next_st prev_st :
    (forall addr1, ~ In addr1 ignore_addrs ->
    get_balance_opt next_st token_id addr1 = get_balance_opt prev_st token_id addr1) ->
    (forall addr1, In addr1 (remove_all addr_eq_dec ignore_addrs (get_owners next_st token_id))
              <-> In addr1 (remove_all addr_eq_dec ignore_addrs (get_owners prev_st token_id))).
  Proof.
    intros H0 addr1.
    assert (Hdec : forall (a1 a2 : Address), a1 = a2 \/ a1 <> a2).
    { intros. destruct (addr_eq_dec a1 a2);auto. }
    split.
    + intros Hin.
      destruct (ListDec.In_decidable Hdec addr1 ignore_addrs) as [Hin_addrs | Hnotin_addrs];subst.
      * exfalso.
        assert (Hall : Forall (fun x =>~In x (remove_all addr_eq_dec ignore_addrs ((get_owners next_st token_id)))) ignore_addrs)
          by apply remove_all_In.
        rewrite Forall_forall in Hall;easy.
      * specialize (H0 _ Hnotin_addrs).
        destruct (get_balance_opt next_st token_id addr1) eqn:Hnext;inversion Hnext.
        ** apply remove_all_not_in_to_remove;auto. apply get_owners_balances;eauto.
        ** apply In_remove_all in Hin;auto.
           apply get_owners_balances in Hin;destruct Hin;congruence.
    + intros Hin.
      destruct (ListDec.In_decidable Hdec addr1 ignore_addrs) as [Hin_addrs | Hnotin_addrs];subst.
      * exfalso.
        assert (Hall : Forall (fun x =>~In x (remove_all addr_eq_dec ignore_addrs ((get_owners prev_st token_id)))) ignore_addrs)
          by apply remove_all_In.
        rewrite Forall_forall in Hall;easy.
      * specialize (H0 _ Hnotin_addrs).
        destruct (get_balance_opt next_st token_id addr1) eqn:Hnext;inversion Hnext.
        ** apply remove_all_not_in_to_remove;auto. apply get_owners_balances;eauto.
        ** apply In_remove_all in Hin;auto.
           apply get_owners_balances in Hin;destruct Hin;congruence.
  Qed.

  (** Any address either in the list of owners, or owns zero tokens. *)
  Lemma in_owners_or_zero_balance_default  `{ChainBase} st token_id owner :
    In owner (get_owners st token_id) \/ get_balance_default st token_id owner = 0.
  Proof.
    assert (Hdec : forall (a1 a2 : Address), a1 = a2 \/ a1 <> a2).
    { intros. destruct (addr_eq_dec a1 a2);auto. }
    destruct (ListDec.In_decidable Hdec owner (get_owners st token_id)) as [Hin_addrs | Hnotin_addrs];subst;auto.
    right. unfold get_balance_default,get_balance.
    destruct (token_id_exists st token_id);auto.
    cbn.
    destruct (get_balance_opt st token_id owner) eqn:Heq;auto.
    assert (In owner (get_owners st token_id)) by (apply get_owners_balances;eauto).
    easy.
  Qed.

  Hint Resolve in_owners_or_zero_balance_default get_owners_no_dup : hints.

  Lemma get_balance_total_get_balance_default `{ChainBase} st token_id p owner:
    get_balance_total st token_id p owner = get_balance_default st token_id owner.
  Proof.
    unfold get_balance_total, get_balance_default, get_balance. rewrite p. cbn.
    now destruct (get_balance_opt st token_id _).
  Qed.

  (** We can recover a statement for the whole "batch" of transfers from the transfers spec where
      the same property is assumed for each transfer in the batch *)
  Lemma transfer_token_ids_preserved `{ChainBase} transfers prev_st next_st ops :
      let params := Build_CIS1_transfer_params _ transfers in
      transfer_spec params prev_st next_st ops ->
      forall token_id,
        token_id_exists prev_st token_id =  token_id_exists next_st token_id.
  Proof.
    revert dependent prev_st.
    revert dependent ops.
    cbn.
    induction transfers.
    - intros ops prev_st spec token_id.
      destruct spec. cbn in *;now subst.
    - intros ops prev_st spec token_id.
      destruct spec as [Htrans Hcalls]. cbn in *.
      destruct Htrans as [st [p [q [Hsingle Htrs]]]].
      transitivity (token_id_exists st token_id).
      * now destruct Hsingle as [HH0 [HH1 [HH2 HH3]]].
      * eapply IHtransfers;eauto.
        constructor. apply Htrs. cbn.
        destruct Hcalls as [Hforall Hops].
        destruct (address_is_contract (cis1_td_to a)).
        ** subst. now inversion Hforall;subst.
        ** easy.
  Qed.


  (** The balances of all token-address pairs NOT mentioned in the transfer batch remain unchanged
  *)
  Lemma transfer_other_balances_preserved `{ChainBase} transfers prev_st next_st ops :
    let params := Build_CIS1_transfer_params _ transfers in
    transfer_spec params prev_st next_st ops ->
    forall addr token_id,
      ~ In (token_id, addr) (transfer_from params) ->
      ~ In (token_id, addr) (transfer_to params)   ->
    get_balance_opt prev_st token_id addr = get_balance_opt next_st token_id addr.
  Proof.
    revert dependent next_st.
    revert dependent prev_st.
    revert dependent ops.
    induction transfers.
    - cbn;intros ops prev_st next_st spec addr token_id.
      destruct spec. cbn in *;now subst.
    - intros ops prev_st next_st ? spec addr token_id Hfrom Hto.
      destruct spec as [Htr Hcalls].
      destruct Htr as [st [p [q [Hsingle Htrs]]]].
      assert ((token_id, addr) <> (a.(cis1_td_token_id), a.(cis1_td_from)) /\ ~ (In (token_id,addr) (transfer_from params))) by firstorder.
        assert ((token_id, addr) <> (a.(cis1_td_token_id), a.(cis1_td_to)) /\ ~ (In (token_id,addr) (transfer_to params))) by firstorder.
      clear Hto. clear Hfrom.
      transitivity (get_balance_opt st token_id addr).
      + destruct Hsingle as [Hbal_not_addr [Hbal_other_tokens [? ?]]].
        cbn in *.
        destruct (Nat.eq_dec token_id a.(cis1_td_token_id)).
        * assert (addr <> a.(cis1_td_to)) by firstorder.
           assert (addr <> a.(cis1_td_from)) by firstorder.
           subst. symmetry. now apply Hbal_not_addr.
        * now symmetry.
      + cbn in *.
        destruct Hcalls as [Hforall Hops].
        destruct (address_is_contract (cis1_td_to a)).
        * subst;inversion Hforall.
           eapply IHtransfers;firstorder.
        * eapply IHtransfers;firstorder.
  Qed.

  (** If the properties of the single transfer holds (the transfer succeeds), then
      we can conclude that if has been enough tokens for the transfer. *)
  Lemma transfer_single_spec_sufficient_funds `{ChainBase}
        prev_st next_st token_id from to amount
        (p : token_id_exists prev_st token_id)
        (q : token_id_exists next_st token_id)
        (spec : transfer_single_spec prev_st next_st token_id p q from to amount) :
    get_balance_total prev_st token_id p from >= amount.
  Proof.
    destruct spec as [H1 [H2 H3]].
    lia.
  Qed.

  (** An important lemma for the main result. The spec for a single transfer ensures that for a
      particular [token_id] the sum of balances is preserved for all owners for one transfer
      of an [amount] between [from] and [to]. *)
  Lemma transfer_single_spec_preserves_balances `{ChainBase}
        prev_st next_st token_id from to amount
        (p : token_id_exists prev_st token_id)
        (q : token_id_exists next_st token_id)
        (spec : transfer_single_spec prev_st next_st token_id p q from to amount) :
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    sum_balances next_st token_id owners2 =
    sum_balances prev_st token_id owners1.
  Proof.
    intros ??.
    destruct spec as [Hother_balances [H1 [H2 [H3 H4]]]].
    unfold transfer_single_spec in *.
    destruct (address_eqb_spec from to) as [Haddr | Haddr].
    + subst.
      rewrite remove_owner with (st := prev_st) (owner := to)
         by (subst owners1;auto with hints).
      rewrite remove_owner with (st := next_st) (owner := to)
        by (subst owners2;auto with hints).
      assert (HH :
                sum_balances next_st token_id (remove addr_eq_dec to owners2) =
                sum_balances prev_st token_id (remove addr_eq_dec to owners1)).
      { apply sum_of_balances_eq_extensional;subst owners2;subst owners1;eauto with hints.
        intros addr.
        apply same_owners_remove_all with (ignore_addrs:=[to]);intros;cbn in *;intuition;eauto.
        intros addr H0. unfold is_true in *.
        apply get_balance_opt_default;try congruence.
        destruct (address_eqb_spec addr to);subst. exfalso;apply (remove_In _ _ _ H0).
        eauto. }
      repeat rewrite get_balance_total_get_balance_default in H3, H4.
      lia.
    + rewrite remove_owner with (st := prev_st) (owner := from)
        by (subst owners1;auto with hints).
      rewrite remove_owner with (st := prev_st) (owner := to)
        by (assert (In to owners1 \/ get_balance_default prev_st token_id to = 0); subst owners1;auto with hints;intuition;auto with hints).
      rewrite remove_owner with (st := next_st) (owner := from)
        by (subst owners2;auto with hints).
      rewrite remove_owner with (st := next_st) (owner := to)
        by (assert (In to owners2 \/ get_balance_default next_st token_id to = 0);
            subst owners2;auto with hints;intuition;auto with hints).
      repeat rewrite get_balance_total_get_balance_default in H3, H4.
      rewrite H3. rewrite H4.
      assert (HH :
                sum_balances next_st token_id (remove addr_eq_dec to (remove addr_eq_dec from owners2)) =
              sum_balances prev_st token_id (remove addr_eq_dec to (remove addr_eq_dec from owners1))).
      { apply sum_of_balances_eq_extensional;subst owners2;subst owners1;eauto with hints.
        apply same_owners_remove_all with (ignore_addrs:=[to;from]);intros;cbn in *;intuition;eauto.
        intros addr H0. unfold is_true in *.
        apply get_balance_opt_default;try congruence.
        destruct (address_eqb_spec addr to);subst. exfalso;apply (remove_In _ _ _ H0).
        destruct (address_eqb_spec addr from);subst. apply In_remove in H0; auto. exfalso;apply (remove_In _ _ _ H0).
        eauto. }
      lia.
  Qed.

  (** *** Main result *)

  (** The prove our main result about the CIS1 standard with relation to the token balances.
      Namely, we prove that all the supported entry points preserve the sum of balances for all
      token types. The results hold for any contrac that complies with the abstract interface
      of the CIS1 standard. *)

  Lemma transfer_preserves_sum_of_balances `{ChainBase} prev_st next_st ops transfers token_id
        (spec : transfer_spec (Build_CIS1_transfer_params _ transfers) prev_st next_st ops) :
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    sum_balances prev_st token_id owners1 = sum_balances next_st token_id owners2.
  Proof.
    destruct spec as [Htr Hcalls].
    revert dependent prev_st.
    revert dependent next_st.
    revert dependent ops.
    induction transfers;intros ops ? next_st prev_st Htr ? ?.
    - cbn in *. now subst.
    - cbn in *.
      destruct Htr as [st [p [q [Hsingle Htrs]]]].
      transitivity (sum_balances st token_id (get_owners st token_id)).
      + destruct (Nat.eq_dec token_id a.(cis1_td_token_id)).
        * subst. symmetry.
          now eapply transfer_single_spec_preserves_balances with (next_st0 := st).
        * destruct Hsingle as [? [HH [? ?]]].
          apply sum_of_balances_eq_extensional;subst owners2;subst owners1;eauto with hints.
          ** intros. repeat rewrite get_owners_balances.
             now rewrite HH.
          ** intros.
          apply get_balance_opt_default;symmetry;auto.
      + cbn in *.
        destruct Hcalls as [Hforall Hops].
        destruct (address_is_contract (cis1_td_to a)).
        ** subst;inversion Hforall.
           eapply IHtransfers;firstorder.
        ** eapply IHtransfers;firstorder.
  Qed.

  Lemma balanceOf_preserves_sum_of_balances `{ChainBase} params prev_st next_st token_id ops
    (spec : balanceOf_spec params prev_st next_st ops) :
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    sum_balances next_st token_id owners2 =
    sum_balances prev_st token_id owners1.
  Proof.
    intros ??.
    destruct spec as [H1 H2 H3 H4]. clear H4.
    apply sum_of_balances_eq_extensional;subst owners1 owners2;auto with hints.
    intros. now apply same_owners_remove_all with (ignore_addrs := []).
    intros. now apply get_balance_opt_default.
  Qed.

  Lemma updateOperator_preserves_sum_of_balances `{ChainBase} params prev_st next_st token_id ops ctx
    (spec : updateOperator_spec ctx params prev_st next_st ops) :
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    sum_balances next_st token_id owners2 =
    sum_balances prev_st token_id owners1.
  Proof.
    intros ??.
    destruct spec as [H1 H2 H3].
    apply sum_of_balances_eq_extensional;subst owners1 owners2;auto with hints.
    intros. now apply same_owners_remove_all with (ignore_addrs := []).
    intros. now apply get_balance_opt_default.
  Qed.

End CIS1Balances.