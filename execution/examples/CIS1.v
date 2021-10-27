(** * Concordium's CIS-1 http://proposals.concordium.software/CIS/cis-1.html *)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Examples Require Import Common.
From MetaCoq.Template Require Import monad_utils.

From stdpp Require Import sets.
From stdpp Require Import base.
From stdpp Require Import mapset.
From stdpp Require Import fin_sets.

From Coq Require Import List.
From Coq Require Import JMeq.
From Coq Require Import ZArith.

Import ListNotations.

Definition AddrSet `{ChainBase} := (mapset (Containers.FMap Address)).

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

Definition transfer_to `{ChainBase} : CIS1_transfer_params -> list Address :=
  fun params => map cis1_td_to params.(cis_tr_transfers).

Definition transfer_from `{ChainBase} : CIS1_transfer_params -> list Address :=
  fun params => map cis1_td_from params.(cis_tr_transfers).

Inductive CIS1_operatorUpdate :=
  cis1_ou_remove_operator
| cis1_ou_add_operator.

Record CIS1_updateOperator_params `{ChainBase} :=
  { cis1_ou_update : CIS1_operatorUpdate;
    cis1_ou_address : Address }.

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

  (* Parameter get_balance : forall `{ChainBase} (st : Storage) *)
  (*                                (token_id : TokenID) *)
  (*                                (p : In token_id (get_token_ids st)), Address -> option TokenAmount. *)

  Parameter set_balance : forall `{ChainBase}, Storage -> TokenID -> Address -> TokenAmount -> Storage.

  Axiom set_balance_get_balance : forall `{ChainBase} st token_id amount addr,
      get_balance_opt (set_balance st token_id addr amount) token_id addr = Some amount.

  Parameter get_operators : forall `{ChainBase}, Storage -> Address -> list Address.

  Parameter set_operators : forall `{ChainBase}, Storage -> Address -> list Address -> Storage.

  Parameter get_owners : forall `{ChainBase}, Storage -> TokenID -> list Address.

  Axiom get_owners_balances : forall `{ChainBase} st owner token_id,
    In owner (get_owners st token_id) <->
    exists balance, get_balance_opt st token_id owner = Some balance.

  Parameter is_owner : forall `{ChainBase}, Storage -> Address -> bool.

  Parameter token_id_exists : Storage -> TokenID -> bool.

  Parameter get_token_ids : Storage -> list TokenID.

  Definition get_balance `{ChainBase} : Storage -> TokenID -> Address -> option TokenAmount :=
    fun st token_id addr => if token_id_exists st token_id then
                              match get_balance_opt st token_id addr with
                              | Some bal => Some bal
  (* CIS1 (currently in PR #14): The balance of an address not owning any amount of a token type SHOULD be treated as having a balance of zero*)
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

  Context `{ChainBase}.

  Import cis1_types.
  Import cis1_data.

  (** CIS1: A smart contract implementing CIS1 MUST export three functions [transfer], [updateOperator] and [balanceOf]. *)

  Axiom supports_transfer : exists msg, get_CIS1_entry_point msg = Some CIS1_transfer.

  Axiom supports_updateOperator : exists msg, get_CIS1_entry_point msg = Some CIS1_transfer.

  Axiom supports_blanceOf : exists msg, get_CIS1_entry_point msg = Some CIS1_balanceOf.

  Definition transfer_single_spec
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
    prev_from = next_from + amount /\
    next_to = prev_to + amount.

  Fixpoint compose_transfers
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
      exists (st : Storage)
        (p: token_id_exists init_st pr.(cis1_td_token_id) = true)
        (q : token_id_exists st pr.(cis1_td_token_id) = true),
      single_transfer init_st st pr p q /\ compose_transfers st final_st ps single_transfer
    end.

  Record transfer_spec (params : CIS1_transfer_params)
         (prev_st next_st : Storage)
         (ret_ops : list ActionBody) : Prop :=
    { transfer_other_balances_preserved :
        forall addr token_id,
          ~ In addr (transfer_from params) ->
          ~ In addr (transfer_to params)   ->
          get_balance_opt prev_st token_id addr = get_balance_opt next_st token_id addr;

      transfer_token_ids_preserved :
        forall token_id,
          token_id_exists prev_st token_id = true ->
          token_id_exists next_st token_id = true;

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

  Arguments transfer_token_ids_preserved {_ _ _ _}.

  Definition sum_balances (st : Storage) (token_id : TokenID) (p : token_id_exists st token_id) (owners : list Address) :=
    fold_right (fun addr s => get_balance_total st token_id p addr + s) 0 owners.

  Import Lia.

  Program Definition addr_eq_dec (a1 a2 : Address) : {a1 = a2} + {a1 <> a2} :=
    match address_eqb_spec a1 a2 with
    | ReflectT _ p => left p
    | ReflectF _ p => right p
    end.

  Lemma not_owner_zero_balance st token_id p (owner : Address) :
    ¬ In owner (get_owners st token_id) -> get_balance_total st token_id p owner = 0.
  Proof.
    intros Hin.
    unfold get_balance_total,get_balance.
    Admitted.


  Lemma not_in_remove_same {A : Type} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l : list A) (x : A):
    not (In x l) -> remove eq_dec x l = l.
  Proof.
    induction l.
    + auto.
    + intros Hnotin. cbn in *.
      destruct (eq_dec x a);intuition;congruence.
  Qed.

  Lemma remove_owner st token_id p (owners : list Address) (owner : Address) :
    In owner owners \/ get_balance_total st token_id p owner = 0 ->
    NoDup owners ->
    sum_balances st token_id p owners = get_balance_total st token_id p owner + sum_balances st token_id p (remove addr_eq_dec owner owners).
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

  Lemma sum_of_other_balances_eq from to addrs prev_st next_st token_id p q :
    (forall addr, addr <> from -> addr <> to -> get_balance_total next_st token_id p addr = get_balance_total prev_st token_id q addr) ->
    ~ In from addrs ->
    ~ In to addrs ->
    sum_balances next_st token_id p addrs = sum_balances prev_st token_id q addrs.
  Proof.
    intros Hbal Hform Hto.
    induction addrs;simpl in *;intuition;auto.
  Qed.

  Lemma sum_of_balances_eq addrs prev_st next_st token_id p q :
    (forall addr, In addr addrs ->get_balance_total next_st token_id p addr = get_balance_total prev_st token_id q addr) ->
    sum_balances next_st token_id p addrs = sum_balances prev_st token_id q addrs.
  Proof.
    intros Hbal.
    induction addrs;simpl in *;intuition;auto.
  Qed.


  Lemma not_in_remove {A : Type} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l : list A) (x y : A):
    not (In x l) -> ~ In x (remove eq_dec y l).
  Proof.
    induction l.
    + auto.
    + intros Hnotin. cbn in *.
      destruct (eq_dec y a);cbn in *;intuition;auto.
  Qed.


  Lemma remove_remove {A : Type} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l : list A) (x y : A) :
    ~ In x (remove eq_dec y (remove eq_dec x l)).
  Proof.
    induction l;auto;simpl in *.
    destruct (eq_dec x a);subst;intuition;simpl in *.
    destruct (eq_dec y a);subst;intuition;simpl in *.
    intuition;simpl in *.
  Qed.

  Lemma neq_not_removed {A : Type} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l : list A) (x y : A) :
    x <> y -> In x l -> In x (remove eq_dec y l).
  Proof.
    induction l;intros Hneq Hin; auto;simpl in *.
    destruct Hin.
    + subst. destruct (eq_dec y x);subst; try congruence. now cbn.
    + destruct (eq_dec y a);subst; try congruence; now cbn.
  Qed.

  Hint Constructors NoDup : hints.
  Hint Resolve remove_In not_in_remove_same not_in_remove remove_remove neq_not_removed : hints.

  Lemma NoDup_remove {A : Type} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l : list A) (x : A) :
    NoDup l -> NoDup (remove eq_dec x l).
  Proof.
    induction l;intros H;auto;simpl.
    inversion H; destruct (eq_dec x a);subst;intuition;simpl in *;eauto with hints.
  Qed.

  Hint Resolve NoDup_remove : hints.

  Lemma In_remove {A : Type} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l : list A) (x y : A) :
    x <> y -> In x (remove eq_dec y l) -> In x l.
  Proof.
    induction l;intros Hneq Hin; auto;simpl in *.
    subst. destruct (eq_dec y a);subst;cbn in *; auto;intuition;auto.
  Qed.


  Hint Resolve In_remove : hints.

  Lemma remove_extensional {A : Type} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l1 l2 : list A) (y : A) :
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

  Lemma sum_balances_extensional st token_id p owners1 owners2 :
    NoDup owners1 ->
    NoDup owners2 ->
    (forall addr, In addr owners1 <-> In addr owners2) ->
    sum_balances st token_id p owners1 = sum_balances st token_id p owners2.
  Proof.
    intros Hnodup1 Hnodup2 Hiff.
    revert dependent owners2.
    induction owners1;intros.
    + cbn in *. destruct owners2;auto.
      destruct (Hiff a);cbn in *;intuition.
    + simpl.
      destruct (Hiff a);cbn in *.
      specialize (H0 (or_introl eq_refl)) as HH.
      rewrite remove_owner with (st := st) (owner := a) (owners:=owners2);auto with hints.
      inversion Hnodup1;subst.
      rewrite IHowners1 with (owners2 := (remove addr_eq_dec a owners2));eauto with hints.
      intros. split.
      * intros Hin.
        destruct (Hiff addr);cbn in.
        specialize (H2 (or_intror Hin)) as HH1.
        destruct (address_eqb_spec a addr).
        ** now subst.
        ** auto with hints.
      * intros Hin.
        destruct (Hiff addr);cbn in.
        destruct (address_eqb_spec a addr).
        ** assert (~ In addr (remove addr_eq_dec a owners2)).
           { intros ?. subst. apply (remove_In _ _ _ H6). }
           easy.
        ** assert (In addr owners2) by eauto with hints.
           intuition.
  Qed.

  Lemma sum_of_balances_eq_extensional owners1 owners2 prev_st next_st token_id p q :
    NoDup owners1 ->
    NoDup owners2 ->
    (forall addr, In addr owners1 <-> In addr owners2) ->
    (forall addr, In addr owners1 -> get_balance_total next_st token_id p addr = get_balance_total prev_st token_id q addr) ->
    sum_balances next_st token_id p owners1 = sum_balances prev_st token_id q owners2.
  Proof.
    intros.
    erewrite sum_of_balances_eq by eauto.
    apply sum_balances_extensional;auto.
  Qed.

  Fixpoint remove_all {A} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (to_remove : list A) (xs : list A) :=
    match to_remove with
    | [] => xs
    | x :: tl => remove eq_dec x (remove_all eq_dec tl xs)
    end.

  Hint Constructors Forall.

  Lemma remove_all_In {A} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (to_remove : list A) (xs : list A) :
    Forall (fun x => ~ In x (remove_all eq_dec to_remove xs)) to_remove.
  Proof.
    revert dependent xs.
    induction to_remove;simpl;auto.
    constructor;eauto with hints.
    eapply (list.Forall_impl _ _ _ (IHto_remove xs)).
    intros x H HH.
    apply (not_in_remove _ _ _ _ H HH).
  Qed.

  Lemma In_remove_all {A} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (to_remove : list A) (xs : list A) (x : A):
    ~ (In x to_remove) -> In x (remove_all eq_dec to_remove xs) -> In x xs.
  Proof.
    Admitted.

  Lemma remove_all_not_in_to_remove {A} (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (to_remove : list A) (xs : list A) (x : A):
    ~ (In x to_remove) -> In x xs -> In x (remove_all eq_dec to_remove xs).
  Proof.
    intros H1 H2.
    induction to_remove;auto.
    Admitted.

  Lemma same_owners token_id addr next_st prev_st :
    get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr ->
    In addr (get_owners next_st token_id) <-> In addr (get_owners prev_st token_id).
  Proof.
    intros H.
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

  Lemma get_balance_opt_total next_st prev_st token_id p q addr :
    get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr ->
    get_balance_total next_st token_id q addr = get_balance_total prev_st token_id p addr.
  Proof.
    intros H.
    unfold get_balance_total,get_balance. rewrite p, q. cbn.
    destruct (get_balance_opt next_st token_id addr) eqn:Heq1;
    destruct (get_balance_opt prev_st token_id addr) eqn:Heq2;auto;
      inversion H;try congruence.
  Qed.

  Lemma same_owners_remove_all token_id addrs next_st prev_st :
    (forall addr1, ~ In addr1 addrs ->
    get_balance_opt next_st token_id addr1 = get_balance_opt prev_st token_id addr1) ->
    (forall addr1, In addr1 (remove_all addr_eq_dec addrs (get_owners next_st token_id))
              <-> In addr1 (remove_all addr_eq_dec addrs (get_owners prev_st token_id))).
  Proof.
    intros H addr1.
    assert (Hdec : forall (a1 a2 : Address), a1 = a2 \/ a1 <> a2).
    { intros. destruct (addr_eq_dec a1 a2);auto. }
    split.
    + intros Hin.
      destruct (ListDec.In_decidable Hdec addr1 addrs) as [Hin_addrs | Hnotin_addrs];subst.
      * exfalso.
        assert (Hall : Forall (fun x =>~In x (remove_all addr_eq_dec addrs ((get_owners next_st token_id)))) addrs)
          by apply remove_all_In.
        rewrite Forall_forall in Hall;easy.
      * specialize (H _ Hnotin_addrs).
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
      * specialize (H _ Hnotin_addrs).
        destruct (get_balance_opt next_st token_id addr1) eqn:Hnext;inversion Hnext.
        ** apply remove_all_not_in_to_remove;auto. apply get_owners_balances;eauto.
        ** apply In_remove_all in Hin;auto.
           apply get_owners_balances in Hin;destruct Hin;congruence.
  Qed.

  Lemma in_owners_or_zero_balance st token_id owner p :
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

  Hint Resolve in_owners_or_zero_balance : hints.

  Lemma transfer_single_spec_preserves_balances
        prev_st next_st token_id
        (p : token_id_exists prev_st token_id)
        (q : token_id_exists next_st token_id)
        from to amount
        (spec : transfer_single_spec prev_st next_st token_id p q from to amount) :
    (forall addr, addr <> from -> addr <> to -> get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr) ->
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    NoDup owners1 ->
    NoDup owners2 ->
    sum_balances next_st token_id q owners2 =
    sum_balances prev_st token_id p owners1.
  Proof.
    intros Hother_balances ? ? Hnodup1 Hnodup2.
    destruct spec as [H1 H2].
    destruct (address_eqb_spec from to) as [Haddr | Haddr].
    + subst.
      rewrite remove_owner with (st := prev_st) (owner := to)
        by (subst owners1;auto with hints).
      rewrite remove_owner with (st := next_st) (owner := to)
        by (subst owners2;auto with hints).
      assert (HH :
                sum_balances next_st token_id q (remove addr_eq_dec to owners2) =
                sum_balances prev_st token_id p (remove addr_eq_dec to owners1)).
      { apply sum_of_balances_eq_extensional;eauto with hints.
        intros addr.
        apply same_owners_remove_all with (addrs:=[to]);intros;cbn in *;intuition;eauto.
        intros addr H. apply get_balance_opt_total;auto.
        destruct (address_eqb_spec addr to);subst. exfalso;apply (remove_In _ _ _ H).
        eauto. }
      lia.
    + rewrite remove_owner with (st := prev_st) (owner := from)
        by (subst owners1;auto with hints).
      rewrite remove_owner with (st := prev_st) (owner := to)
        by (assert (In to owners1 \/ get_balance_total prev_st token_id p to = 0); subst owners1;auto with hints;intuition;auto with hints).
      rewrite remove_owner with (st := next_st) (owner := from)
        by (subst owners2;auto with hints).
      rewrite remove_owner with (st := next_st) (owner := to)
        by (assert (In to owners2 \/ get_balance_total next_st token_id q to = 0);
            subst owners2;auto with hints;intuition;auto with hints).
      rewrite H2. rewrite H1.
      assert (HH :
                sum_balances next_st token_id q (remove addr_eq_dec to (remove addr_eq_dec from owners2)) =
              sum_balances prev_st token_id p (remove addr_eq_dec to (remove addr_eq_dec from owners1))).
      { apply sum_of_balances_eq_extensional;eauto with hints.
        apply same_owners_remove_all with (addrs:=[to;from]);intros;cbn in *;intuition;eauto.
        intros addr H. apply get_balance_opt_total;auto.
        destruct (address_eqb_spec addr to);subst. exfalso;apply (remove_In _ _ _ H).
        destruct (address_eqb_spec addr from);subst. apply In_remove in H; auto. exfalso;apply (remove_In _ _ _ H).
        eauto. }
      lia.
  Qed.

  Lemma transfer_single_spec_compose_preserves_balances  prev_st next_st pr
        (spec :
           compose_transfers prev_st next_st [pr]
                             (fun st1 st2 x p q => transfer_single_spec st1 st2 x.(cis1_td_token_id) p q x.(cis1_td_from) x.(cis1_td_to) x.(cis1_td_amount))) :
    let token_id := pr.(cis1_td_token_id) in
    (forall addr, addr <> pr.(cis1_td_from) -> addr <> pr.(cis1_td_to) -> get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr) ->
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    NoDup owners1 ->
    NoDup owners2 ->
    exists p q,
    sum_balances next_st token_id q owners2 =
    sum_balances prev_st token_id p owners1.
  Proof.
    intros ? Hother_balances ? ? Hnodup1 Hnodup2.
    cbn in spec.
    destruct spec as [st [p [q [Hspec Hst_eq]]]].
    subst.
    exists p. exists q.
    eapply transfer_single_spec_preserves_balances;eauto.
  Qed.

  (* Fixpoint compose_sum_balances *)
  (*          (params : CIS1_transfer_data) *)
  (*          (init_st final_st : Storage) *)
  (*          (init_owners final_owners: list Address) := *)
  (*   match params with *)
  (*   | [] => True *)
  (*   | pr :: ps => *)
  (*     exists next_st, *)
  (*     let token_id := pr.(cis1_td_token_id) in *)
  (*     sum_balances init_st token_id p init_owners = sum_balances next_st token_id q owners2 /\ *)
  (*     compose_sum_balances ps init_st final_st init_owners final_owners *)
  (*   end. *)


  (* Lemma transfer_preserves_balances params prev_st next_st ops *)
  (*       (tr_spec : transfer_spec params prev_st next_st ops) : *)
  (*   let owners1 := get_owners prev_st token_id in *)
  (*   let owners2 := get_owners next_st token_id in *)
  (*   NoDup owners1 -> *)
  (*   NoDup owners2 -> *)
  (*   exists p q, *)
  (*   sum_balances next_st token_id q owners2 = *)
  (*   sum_balances prev_st token_id p owners1. *)

  (* Proof. *)
  (*   intros Htoken Hnd1 Hnd2. *)
  (*   destruct tr_spec as [H1 H2 H3]. cbn. *)
  (*   specialize (H3 Htoken). *)
  (*   induction (cis_tr_transfers params). *)
  (*   + admit. *)
  (*   + inversion H3;subst. clear H3. *)
  (*     destruct a as [token_id0 amount from to];cbn in *. *)
  (*   eapply transfer_single_spec_preserves_balances with (amount:=amount) (from:=from) (to:=to);eauto. *)
  (*   intros. *)
  (*   symmetry. apply H1. *)
  (*   intros ?. *)


  Record balanceOf_spec
         (params : CIS1_balanceOf_params)
         (prev_st next_st : Storage)
         (ret_ops : list ActionBody) : Prop :=

    { balanceOf_operators_preserved:
        forall addr, get_operators prev_st addr = get_operators next_st addr;

      balanceOf_balances_preserved :
        forall token_id addr, get_balance_opt next_st token_id addr = get_balance_opt prev_st token_id addr;

      balanceOf_callback :
        match monad_map (fun q => get_balance prev_st q.(cis1_bo_query_token_id) q.(cis1_bo_query_address)) params.(cis1_bo_query) with
        (** CIS1: The contract function MUST reject if any of the queries fail *)
        | Some balances =>
          let serialize_balances := map serialize balances in
          (* NOTE: It's assumed that the receiving contract accepts messages of type [TokenType] *)
          let ops := map (act_call params.(cis1_bo_result_address) 0%Z) serialize_balances in
          ret_ops = ops
        | None => False
        end
    }.

  Lemma balanceOf_preserves_balances params prev_st next_st token_id ops
    (p : token_id_exists prev_st token_id)
    (q : token_id_exists next_st token_id)
    (spec : balanceOf_spec params prev_st next_st ops) :
    let owners1 := get_owners prev_st token_id in
    let owners2 := get_owners next_st token_id in
    NoDup owners1 ->
    NoDup owners2 ->
    sum_balances next_st token_id q owners2 =
    sum_balances prev_st token_id p owners1.
  Proof.
    intros ?? Hnodup1 Hnodup2.
    destruct spec as [H1 H2 H3]. clear H3.
    apply sum_of_balances_eq_extensional;auto.
    intros. now apply same_owners.
    intros. now apply get_balance_opt_total.
  Qed.
