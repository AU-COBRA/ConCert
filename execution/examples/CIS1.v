(** * Concordium's CIS-1 http://proposals.concordium.software/CIS/cis-1.html *)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Examples Require Import Common.
From MetaCoq.Template Require Import monad_utils.

From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import JMeq.
From Coq Require Import ZArith.

Import ListNotations.
Import MonadNotation.


(* NOTE: In CIS1 it's an n-byte sequence, where 0 <= n <= 256.
   We model it as an unbounded number [nat] *)
Definition TokenID := nat.
Definition TokenAmount := nat.

(* NOTE: not handling additional data at the moment *)
Record CIS1_transfer_data `{ChainBase} :=
  { cis1_td_token_id : TokenID;
    cis1_td_amount   : TokenAmount;
    cis1_td_from     : Address;
    cis1_td_to       : Address }.

Record CIS1_transfer_params `{ChainBase} :=
  { cis_tr_transfers : list CIS1_transfer_data }.

Definition transfer_to `{ChainBase} : CIS1_transfer_params -> list (TokenID * Address) :=
  fun params => map (fun x => (x.(cis1_td_token_id), x.(cis1_td_to))) params.(cis_tr_transfers).

Definition transfer_from `{ChainBase} : CIS1_transfer_params -> list (TokenID * Address) :=
  fun params => map (fun x => (x.(cis1_td_token_id), x.(cis1_td_from))) params.(cis_tr_transfers).

Inductive CIS1_updateOperator_kind :=
  cis1_ou_remove_operator
| cis1_ou_add_operator.

Record CIS1_updateOperator_update `{ChainBase} :=
  { cis1_ou_update_kind : CIS1_updateOperator_kind;
    cis1_ou_operator_address : Address }.

Record CIS1_updateOperator_params `{ChainBase} :=
  { cis1_ou_params : list CIS1_updateOperator_update }.

Open Scope program_scope.

Record CIS1_balanceOf_query `{ChainBase} :=
 { cis1_bo_query_token_id : TokenID;
   cis1_bo_query_address  : Address }.

Record CIS1_balanceOf_params `{ChainBase} :=
  { cis1_bo_query : list CIS1_balanceOf_query;
    cis1_bo_result_address : Address;
    cis1_bo_result_address_is_contract : address_is_contract cis1_bo_result_address = true}.

Inductive CIS1_entry_points :=
| CIS1_transfer
| CIS1_updateOperator
| CIS1_balanceOf.

Module Type CIS1Types.

  Parameter Msg : Type.
  Parameter Storage : Type.

End CIS1Types.

Module Type CIS1Data (cis1_types : CIS1Types).

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

End CIS1Data.

Module Type CIS1Axioms (cis1_types : CIS1Types) (cis1_data : CIS1Data cis1_types).

  Import cis1_types.
  Import cis1_data.

  (** ** Contract functions *)

  (** CIS1: A smart contract implementing CIS1 MUST export three functions [transfer], [updateOperator] and [balanceOf]. *)

  Axiom supports_transfer : exists msg, get_CIS1_entry_point msg = Some CIS1_transfer.

  Axiom supports_updateOperator : exists msg, get_CIS1_entry_point msg = Some CIS1_transfer.

  Axiom supports_blanceOf : exists msg, get_CIS1_entry_point msg = Some CIS1_balanceOf.

  (** *** Transfer *)

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
    (**  *)
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
                              x.(cis1_td_amount))
    }.

  (** Get the balance and return zero if [get_balance] returns [None] *)
  Definition get_balance_default `{ChainBase} : Storage -> TokenID -> Address -> TokenAmount :=
    fun st token_id addr => match get_balance st token_id addr with
                         | Some amount => amount
                         | None => 0
                         end.

  Definition sum_balances `{ChainBase} (st : Storage) (token_id : TokenID) (owners : list Address) :=
    fold_right (fun addr s => get_balance_default st token_id addr + s) 0 owners.

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


  (** CIS1: The parameter for the callback receive function is a list of pairs, where each pair is a query and an amount of tokens.*)
  Definition balanceOf_callback_type `{ChainBase} : Type := list (TokenID * Address * TokenAmount).

  (** CIS1: The contract function MUST reject if any of the queries fail.

  The [get_balance] function returns [None] (fails) if the token id is unknown. We combine the calls to [get_balance] using [monad_map] where the monad is the [option] monad.
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

  (** Sanity checks for the batch operator update spec *)

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

  End CIS1Axioms.

Module CIS1Balances (cis1_types : CIS1Types) (cis1_data : CIS1Data cis1_types)
       (cis1_axioms : CIS1Axioms cis1_types cis1_data).

  Import cis1_types cis1_data cis1_axioms.
  Import Lia.

  Program Definition addr_eq_dec `{ChainBase} (a1 a2 : Address) : {a1 = a2} + {a1 <> a2} :=
    match address_eqb_spec a1 a2 with
    | ssrbool.ReflectT _ p => left p
    | ssrbool.ReflectF _ p => right p
    end.

  Lemma not_in_remove_same {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A):
    not (In x l) -> remove eq_dec x l = l.
  Proof.
    induction l.
    + auto.
    + intros Hnotin. cbn in *.
      destruct (eq_dec x a);intuition;congruence.
  Qed.

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

  Lemma sum_of_other_balances_eq `{ChainBase} from to addrs prev_st next_st token_id :
    (forall addr, addr <> from -> addr <> to -> get_balance_default next_st token_id addr = get_balance_default prev_st token_id addr) ->
    ~ In from addrs ->
    ~ In to addrs ->
    sum_balances next_st token_id addrs = sum_balances prev_st token_id addrs.
  Proof.
    intros Hbal Hform Hto.
    induction addrs;simpl in *;intuition;auto.
  Qed.

  Lemma sum_of_balances_eq `{ChainBase} addrs prev_st next_st token_id :
    (forall addr, In addr addrs ->get_balance_default next_st token_id addr = get_balance_default prev_st token_id addr) ->
    sum_balances next_st token_id addrs = sum_balances prev_st token_id addrs.
  Proof.
    intros Hbal.
    induction addrs;simpl in *;intuition;auto.
  Qed.

  Lemma not_in_remove {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A):
    not (In x l) -> ~ In x (remove eq_dec y l).
  Proof.
    induction l.
    + auto.
    + intros Hnotin. cbn in *.
      destruct (eq_dec y a);cbn in *;intuition;auto.
  Qed.


  Lemma remove_remove {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A) :
    ~ In x (remove eq_dec y (remove eq_dec x l)).
  Proof.
    induction l;auto;simpl in *.
    destruct (eq_dec x a);subst;intuition;simpl in *.
    destruct (eq_dec y a);subst;intuition;simpl in *.
    intuition;simpl in *.
  Qed.

  Lemma neq_not_removed {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A) :
    x <> y -> In x l -> In x (remove eq_dec y l).
  Proof.
    induction l;intros Hneq Hin; auto;simpl in *.
    destruct Hin.
    + subst. destruct (eq_dec y x);subst; try congruence. now cbn.
    + destruct (eq_dec y a);subst; try congruence; now cbn.
  Qed.

  Hint Constructors NoDup : hints.
  Hint Resolve remove_In not_in_remove_same not_in_remove remove_remove neq_not_removed : hints.

  Lemma NoDup_remove `{ChainBase} {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A) :
    NoDup l -> NoDup (remove eq_dec x l).
  Proof.
    induction l;intros H0;auto;simpl.
    inversion H0; destruct (eq_dec x a);subst;intuition;simpl in *;eauto with hints.
  Qed.

  Hint Resolve NoDup_remove : hints.

  Lemma In_remove {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A) :
    x <> y -> In x (remove eq_dec y l) -> In x l.
  Proof.
    induction l;intros Hneq Hin; auto;simpl in *.
    subst. destruct (eq_dec y a);subst;cbn in *; auto;intuition;auto.
  Qed.


  Hint Resolve In_remove : hints.

  Lemma remove_extensional {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) (y : A) :
    (forall x, In x l1 <-> In x l2 ) -> (forall x, In x (remove eq_dec y l1) <-> In x (remove eq_dec y l2)).
  Proof.
    intros H x.
    split.
    + intros Hin.
      destruct (eq_dec x y);subst.
      * exfalso. apply (remove_In _ _ _ Hin).
      * destruct (H x);intuition;eauto with hints.
    + intros Hin.
      destruct (eq_dec x y);subst.
      * exfalso. apply (remove_In _ _ _ Hin).
      * destruct (H x);intuition;eauto with hints.
  Qed.

  Hint Resolve remove_extensional : hints.

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

  Fixpoint remove_all {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (to_remove : list A) (xs : list A) :=
    match to_remove with
    | [] => xs
    | x :: tl => remove eq_dec x (remove_all eq_dec tl xs)
    end.

  Lemma remove_all_In {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (to_remove : list A) (xs : list A) :
    Forall (fun x => ~ In x (remove_all eq_dec to_remove xs)) to_remove.
  Proof.
    revert dependent xs.
    induction to_remove;simpl;auto.
    constructor;eauto with hints.
    eapply (list.Forall_impl _ _ _ (IHto_remove xs)).
    intros x H HH.
    apply (not_in_remove _ _ _ _ H HH).
  Qed.

  Lemma In_remove_all {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (to_remove : list A) (xs : list A) (x : A):
    ~ (In x to_remove) -> In x (remove_all eq_dec to_remove xs) -> In x xs.
  Proof.
    Admitted.

  Lemma remove_all_not_in_to_remove {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (to_remove : list A) (xs : list A) (x : A):
    ~ (In x to_remove) -> In x xs -> In x (remove_all eq_dec to_remove xs).
  Proof.
    intros H1 H2.
    induction to_remove;auto.
    Admitted.

  Lemma same_owners `{ChainBase}  token_id addr next_st prev_st :
    get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr ->
    In addr (get_owners next_st token_id) <-> In addr (get_owners prev_st token_id).
  Proof.
    intros H0.
    split.
    + intros Hin.
      destruct (get_balance_opt next_st token_id addr) eqn:Hnext;inversion Hnext.
      * apply get_owners_balances;eauto.
      * apply get_owners_balances in Hin;destruct Hin;congruence.
    + intros Hin.
      destruct (get_balance_opt next_st token_id addr) eqn:Hnext;inversion Hnext.
      * apply get_owners_balances;eauto.
      * apply get_owners_balances in Hin;destruct Hin;congruence.
  Qed.

  Lemma get_balance_opt_total `{ChainBase} next_st prev_st token_id p q addr :
    get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr ->
    get_balance_total next_st token_id q addr = get_balance_total prev_st token_id p addr.
  Proof.
    intros H0.
    unfold get_balance_total,get_balance. rewrite p, q. cbn.
    destruct (get_balance_opt next_st token_id addr) eqn:Heq1;
    destruct (get_balance_opt prev_st token_id addr) eqn:Heq2;auto;
      inversion H;try congruence.
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

  Lemma same_owners_remove_all  `{ChainBase} token_id addrs next_st prev_st :
    (forall addr1, ~ In addr1 addrs ->
    get_balance_opt next_st token_id addr1 = get_balance_opt prev_st token_id addr1) ->
    (forall addr1, In addr1 (remove_all addr_eq_dec addrs (get_owners next_st token_id))
              <-> In addr1 (remove_all addr_eq_dec addrs (get_owners prev_st token_id))).
  Proof.
    intros H0 addr1.
    assert (Hdec : forall (a1 a2 : Address), a1 = a2 \/ a1 <> a2).
    { intros. destruct (addr_eq_dec a1 a2);auto. }
    split.
    + intros Hin.
      destruct (ListDec.In_decidable Hdec addr1 addrs) as [Hin_addrs | Hnotin_addrs];subst.
      * exfalso.
        assert (Hall : Forall (fun x =>~In x (remove_all addr_eq_dec addrs ((get_owners next_st token_id)))) addrs)
          by apply remove_all_In.
        rewrite Forall_forall in Hall;easy.
      * specialize (H0 _ Hnotin_addrs).
        destruct (get_balance_opt next_st token_id addr1) eqn:Hnext;inversion Hnext.
        ** apply remove_all_not_in_to_remove;auto. apply get_owners_balances;eauto.
        ** apply In_remove_all in Hin;auto.
           apply get_owners_balances in Hin;destruct Hin;congruence.
    + intros Hin.
      destruct (ListDec.In_decidable Hdec addr1 addrs) as [Hin_addrs | Hnotin_addrs];subst.
      * exfalso.
        assert (Hall : Forall (fun x =>~In x (remove_all addr_eq_dec addrs ((get_owners prev_st token_id)))) addrs)
          by apply remove_all_In.
        rewrite Forall_forall in Hall;easy.
      * specialize (H0 _ Hnotin_addrs).
        destruct (get_balance_opt next_st token_id addr1) eqn:Hnext;inversion Hnext.
        ** apply remove_all_not_in_to_remove;auto. apply get_owners_balances;eauto.
        ** apply In_remove_all in Hin;auto.
           apply get_owners_balances in Hin;destruct Hin;congruence.
  Qed.

  Lemma in_owners_or_zero_balance_total  `{ChainBase} st token_id owner p :
    In owner (get_owners st token_id) \/ get_balance_total st token_id p owner = 0.
  Proof.
    assert (Hdec : forall (a1 a2 : Address), a1 = a2 \/ a1 <> a2).
    { intros. destruct (addr_eq_dec a1 a2);auto. }
    destruct (ListDec.In_decidable Hdec owner (get_owners st token_id)) as [Hin_addrs | Hnotin_addrs];subst;auto.
    right. unfold get_balance_total,get_balance. rewrite p.
    cbn.
    destruct (get_balance_opt st token_id owner) eqn:Heq;auto.
    assert (In owner (get_owners st token_id)) by (apply get_owners_balances;eauto).
    easy.
  Qed.

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


  Hint Resolve in_owners_or_zero_balance_total in_owners_or_zero_balance_default get_owners_no_dup : hints.

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
    induction transfers.
    - intros prev_st ? Htr token_id;subst params.
      destruct Htr. cbn in *;now subst.
    - intros prev_st ? Htr token_id;subst params.
      destruct Htr as [H1]. cbn in *.
      destruct H1 as [st [p [q [Hsingle Htrs]]]].
      transitivity (token_id_exists st token_id).
      * destruct Hsingle as [HH0 [HH1 [HH2 HH3]]].
        easy.
      * apply IHtransfers. easy.
  Qed.


  (** The balances of all token-address pairs NOT mentioned in the transfer batch remain unchanged *)
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
    induction transfers.
    - intros prev_st next_st ? Htr addr token_id.
      destruct Htr. cbn in *;now subst.
    - intros prev_st next_st ? Htr ? ? Hfrom Hto.
      destruct Htr as [H1].
      destruct H1 as [st [p [q [Hsingle Htrs]]]].
      assert ((token_id, addr) <> (a.(cis1_td_token_id), a.(cis1_td_from)) /\ ~ (In (token_id,addr) (transfer_from params))) by firstorder.
        assert ((token_id, addr) <> (a.(cis1_td_token_id), a.(cis1_td_to)) /\ ~ (In (token_id,addr) (transfer_to params))) by firstorder.
      clear Hto. clear Hfrom.
      transitivity (get_balance_opt st token_id addr).
      * destruct Hsingle as [Hbal_not_addr [Hbal_other_tokens [? ?]]].
        cbn in *.
        destruct (Nat.eq_dec token_id a.(cis1_td_token_id)).
        ** assert (addr <> a.(cis1_td_to)) by firstorder.
           assert (addr <> a.(cis1_td_from)) by firstorder.
           subst. symmetry. now apply Hbal_not_addr.
        ** now symmetry.
      * cbn in *. now apply IHtransfers.
  Qed.


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
        apply same_owners_remove_all with (addrs:=[to]);intros;cbn in *;intuition;eauto.
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
        apply same_owners_remove_all with (addrs:=[to;from]);intros;cbn in *;intuition;eauto.
        intros addr H0. unfold is_true in *.
        apply get_balance_opt_default;try congruence.
        destruct (address_eqb_spec addr to);subst. exfalso;apply (remove_In _ _ _ H0).
        destruct (address_eqb_spec addr from);subst. apply In_remove in H0; auto. exfalso;apply (remove_In _ _ _ H0).
        eauto. }
      lia.
  Qed.

  (* NOTE: The same lemma as above, but stated using composition of transfers.
    (in this case it's just a one-transfer composition) *)
  Lemma transfer_single_spec_compose_preserves_sum_balances
        `{ChainBase}
        prev_st next_st pr
        (spec :
           compose_transfers prev_st next_st [pr]
                             (fun st1 st2 x p q => transfer_single_spec st1 st2 x.(cis1_td_token_id) p q x.(cis1_td_from) x.(cis1_td_to) x.(cis1_td_amount))) :
    let token_id := pr.(cis1_td_token_id) in
    (forall addr, addr <> pr.(cis1_td_from) -> addr <> pr.(cis1_td_to) -> get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr) ->
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    sum_balances next_st token_id owners2 =
    sum_balances prev_st token_id owners1.
  Proof.
    intros ? Hother_balances ? ?.
    cbn in spec.
    destruct spec as [st [p [q [Hspec Hst_eq]]]].
    subst.
    eapply transfer_single_spec_preserves_balances;eauto.
  Qed.

  Lemma transfer_preserves_sum_of_balances `{ChainBase} prev_st next_st ops transfers token_id
        (tr_spec : transfer_spec (Build_CIS1_transfer_params _ transfers) prev_st next_st ops) :
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    sum_balances prev_st token_id owners1 = sum_balances next_st token_id owners2.
  Proof.
    destruct tr_spec as [H1].
    revert dependent prev_st.
    revert dependent next_st.
    induction transfers;intros.
    - cbn in *. now subst.
    - cbn in *.
      destruct H1 as [st [p [q [Hsingle Htrs]]]].
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
      + now apply IHtransfers.
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
    intros. now apply same_owners.
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
    intros. now apply same_owners.
    intros. now apply get_balance_opt_default.
  Qed.

End CIS1Balances.
