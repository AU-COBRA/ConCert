(**
  This file contains an implementation of the example token that complies with the Concordium's CIS1 standard.
  The development is inspired by the Rust implementation: https://github.com/Concordium/concordium-rust-smart-contracts/blob/b49a9f07131b2659de2f7b55eb5e8365d0ed4720/examples/cis1-wccd/src/lib.rs

  We also show that the implementation of the token complies with our formalization of the CIS1 standard.
*)

From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Logic.Eqdep_dec.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Examples.CIS1 Require Import CIS1Spec.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.

Import ListNotations.


Definition requireTrue (cond : bool) :=
  if cond then Some tt else None.

Section WccdToken.
  Context {BaseTypes : ChainBase}.
  Set Nonrecursive Elimination Schemes.

  (** Similarly to the Concordium implementation we use the smallest token id type, because
      the contract hold tokens of only one type *)
  Definition TokenID := unit.

  Open Scope bool.

  (** * Entry points *)

  Record wccd_transfer_params :=
    { wccd_td_token_id : TokenID;
      wccd_td_amount   : TokenAmount;
      wccd_td_from     : Address;
      wccd_td_to       : Address }.

  Inductive OpUpdateKind :=
  | opAdd
  | opDelete.

  Inductive Msg :=
  | wccd_msg_transfer (params : list wccd_transfer_params)
  | wccd_msg_balanceOf (query : list Address) (send_results_to : Address)
  | wccd_msg_updateOperator (params : list (OpUpdateKind * Address))
  | wccd_msg_mint (receiver : Address)
  | wccd_msg_burn (amount : TokenAmount).

  (** * Contract's state *)

  (** The state tracked for each address.*)
  Record AddressState := {
      wccd_balance   : TokenAmount;
      wccd_operators : list Address
    }.

  (* begin hide *)
  MetaCoq Run (make_setters AddressState).
  (* end hide *)


  (** The contract state: a mapping from addresses to [AddressState] *)

  Definition State := AddressMap.AddrMap AddressState.

  Section Serialization.

    Global Instance OpUpdateKind_serializable : Serializable OpUpdateKind :=
      Derive Serializable OpUpdateKind_rect <opAdd, opDelete>.

    Global Instance state_serializable : Serializable AddressState :=
      Derive Serializable AddressState_rect <Build_AddressState>.

    Global Instance wccd_transfer_params_serializable : Serializable wccd_transfer_params :=
      Derive Serializable wccd_transfer_params_rect <Build_wccd_transfer_params>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <wccd_msg_transfer, wccd_msg_balanceOf, wccd_msg_updateOperator, wccd_msg_mint, wccd_msg_burn>.

  End Serialization.

  (** * Transfer *)

  Definition increment_balance (st : State) (addr : Address) (inc : TokenAmount) : State :=
    match AddressMap.find addr st with
    | Some old => AddressMap.add addr (old<| wccd_balance := old.(wccd_balance) + inc |>) st
    | None => AddressMap.add addr {| wccd_balance := inc ; wccd_operators := [] |} st
    end.

  Definition decrement_balance (st : State) (addr : Address) (dec : TokenAmount) : option State :=
    do old <- AddressMap.find addr st;
    let old_balance := old.(wccd_balance) in
    do requireTrue (dec <=? old_balance);
    ret (AddressMap.add addr (old<| wccd_balance := old_balance - dec |>) st).


  Definition is_operator (addr owner : Address)(st : State) : bool :=
    match AddressMap.find owner st with
    | Some v => existsb (fun x => (addr =? x)%address) v.(wccd_operators)
    | None => false
    end.

  (** Single transfer of [amount] between [from] and [to] *)
  Definition wccd_transfer_single
             (token_id : TokenID)
             (amount : TokenAmount)
             (owner from to : Address)
             (prev_st : State) : option State :=
    do requireTrue ((owner =? from)%address || is_operator from owner prev_st);
    do st <- decrement_balance prev_st from amount;
    ret (increment_balance st to amount).

  (** Batch execution of all transfers in the list. Note that the
      operation succeeds only if all transfers in the batch succeed *)
  Definition wccd_transfer (ctx : ContractCallContext) (transfers : list wccd_transfer_params) (prev_st : State)
    : option State :=
    monad_foldl (fun acc x =>
                   let owner := ctx.(ctx_from) in
                   wccd_transfer_single tt x.(wccd_td_amount) owner x.(wccd_td_from) x.(wccd_td_to) acc)
                prev_st transfers.

  (** * balanceOf *)

  Definition get_balance_opt (addr : Address) (st : State) : option TokenAmount :=
    match AddressMap.find addr st with
    | Some data => Some data.(wccd_balance)
    | None => None
    end.

  Definition wccd_balanceOf (query : list Address) (st : State)
    : list (TokenID * Address * TokenAmount) :=
    map (fun addr => (tt, addr, with_default 0 (get_balance_opt addr st))) query.

  (** * updateOperator *)

  Definition add_remove (operators : list Address) (param : OpUpdateKind * Address) :=
    let '(updateKind,addr) := param in
    match updateKind with
    | opAdd => addr :: operators
    | opDelete => remove address_eqdec addr operators
    end.

  (** NOTE: in contrast to the Concordium's implementation, we do not
      allow adding operators to non-existing addresses *)
  Definition wccd_updateOperator (owner : Address) (params : list (OpUpdateKind * Address)) (prev_st : State)
    : option State :=
    do owner_data <- AddressMap.find owner prev_st;
    let updated_owner_data := owner_data<| wccd_operators := fold_left add_remove params owner_data.(wccd_operators) |> in
    ret (AddressMap.add owner updated_owner_data prev_st).

  (** * WCCD receive *)

  (** We dispatch on a message of type [Msg] and call the corresponding functions with received parameters *)
  Definition wccd_receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (prev_st : State)
             (msg : option Msg)
    : option (State * list ActionBody) :=
    match msg with
    | Some (wccd_msg_transfer params) =>
        do next_st <- wccd_transfer ctx params prev_st;
        let contract_accounts :=
          filter (fun x => address_is_contract x.(wccd_td_to)) params in
        let mk_callback x :=
        (* NOTE: we assume that the receiving contract accepts messages of type
           (TokenID * TokenAmount * Address) *)
          act_call x.(wccd_td_to) 0 (serialize (tt,x.(wccd_td_amount), x.(wccd_td_from))) in
        let ops := map mk_callback contract_accounts in
        ret (next_st, ops)
    | Some (wccd_msg_balanceOf query send_to) =>
        let balances := wccd_balanceOf query prev_st in
        do requireTrue (address_is_contract send_to);
        ret (prev_st, [act_call send_to 0 (serialize balances)])
    | Some (wccd_msg_updateOperator params) =>
        do next_st <- wccd_updateOperator ctx.(ctx_from) params prev_st;
        ret (next_st, [])
    | Some (wccd_msg_mint receiver) =>
        (* Check that the sender is not the receiver *)
        do requireTrue (address_neqb receiver ctx.(ctx_from));
        let next_st := increment_balance prev_st receiver (Z.to_nat ctx.(ctx_amount)) in
        (* NOTE: we only update the state and do not notify the receiver *)
        ret (next_st,[])
    | Some (wccd_msg_burn amt) =>
        (* Check that the sender is not the receiver *)
        do next_st <- decrement_balance prev_st ctx.(ctx_from) amt;
        ret (next_st, [act_transfer ctx.(ctx_from) (Z.of_nat amt)])
    | None => None
    end.

End WccdToken.

(** * WCCD complies with CIS1 *)

Module WccdTypes <: CIS1Types.

  Definition Msg `{ChainBase} := Msg.

  Definition Storage `{ChainBase} := State.

  Definition TokenID := TokenID.

  Definition serializable_token_id : Serializable TokenID := _.

  Definition token_id_eqb (id1 id2 : TokenID) := true.

  Lemma token_id_eqb_spec :
    forall (a b : TokenID), Bool.reflect (a = b) (token_id_eqb a b).
  Proof. intros. constructor. now destruct a,b. Qed.

End WccdTypes.

Module WccdView <: CIS1View WccdTypes.

  Import WccdTypes.

  Section WccdViewDefs.

    Context `{ChainBase}.

    Definition get_balance_opt st (token_id : TokenID) addr :=
      get_balance_opt addr st.

    Definition get_operators (st : Storage) (addr : Address) :=
      match AddressMap.find addr st with
      | Some v => v.(wccd_operators)
      | None => []
      end.

    Definition get_owners : Storage -> TokenID -> list Address :=
      fun st token_id => FMap.keys st.

    Lemma get_owners_no_dup : forall st token_id, NoDup (get_owners st token_id).
    Proof.
      intros. unfold get_owners; apply FMap.NoDup_keys.
    Qed.

    Lemma In_keys_In_elements_iff {K V : Type} `{countable.Countable K} (m : FMap K V) (k : K) :
      In k (FMap.keys m) <-> exists v, In (k,v) (FMap.elements m).
    Proof.
      split.
      - induction m using fin_maps.map_ind; intros Hin.
        + easy.
        + unfold FMap.keys in *.
          rewrite FMap.elements_add in Hin by assumption.
          cbn in *. destruct Hin.
          * exists x. rewrite FMap.elements_add by assumption. now left.
          * destruct (IHm H2) as [x0 Hx0]. exists x0.
            rewrite FMap.elements_add by assumption.
            now right.
      - induction m using fin_maps.map_ind; intros Hex.
        + now destruct Hex.
        + destruct Hex as [v Hv].
          unfold FMap.keys.
          rewrite FMap.elements_add in * by assumption; cbn in *.
          destruct Hv as [HH | HH]; try inversion HH; easy.
    Qed.

    Lemma get_owners_balances : forall st owner token_id,
        In owner (get_owners st token_id) <->
          exists balance, get_balance_opt st token_id owner = Some balance.
    Proof.
      split.
      + intros Hin. unfold get_owners in *.
        unfold get_balance_opt,Cis1wccd.get_balance_opt.
        apply In_keys_In_elements_iff in Hin.
        destruct Hin as [a_st HH].
        exists a_st.(wccd_balance).
        apply FMap.In_elements in HH.
        unfold AddressMap.find,FMap.find in *.
        now rewrite HH.
      + intros Hex.
        destruct Hex as [b Hb].
        unfold get_owners, FMap.keys.
        unfold get_balance_opt,Cis1wccd.get_balance_opt in *.
        destruct (AddressMap.find owner st) eqn:Heq; try congruence.
        unfold AddressMap.find in *.
        apply FMap.In_elements in Heq.
        apply In_keys_In_elements_iff.
        eauto.
    Qed.

    Definition token_id_exists (st : Storage) (token_id : TokenID) : bool := true.

  End WccdViewDefs.
End WccdView.

Module WccdReceiveSpec <: CIS1ReceiveSpec WccdTypes WccdView.

  Module cis1_axioms := CIS1Axioms WccdTypes WccdView.
  Import cis1_axioms.

  Module BalancesFacts := CIS1Balances WccdTypes WccdView.
  Import BalancesFacts.

  Section WccdReceiveDefs.

    Context `{ChainBase}.

    (** Converting _to_ the CIS1 standard parameters *)
    Definition to_cis1_transfer_data (p : wccd_transfer_params) : CIS1_transfer_data :=
      let '(Build_wccd_transfer_params token_id amt from_addr to_addr) := p in
      {| cis1_td_token_id := token_id;
         cis1_td_amount := amt;
         cis1_td_from := from_addr;
         cis1_td_to := to_addr |}.

    Definition to_cis1_updateOperator_kind (op : OpUpdateKind) : CIS1_updateOperator_kind :=
      match op with
      | opAdd => cis1_ou_add_operator
      | opDelete => cis1_ou_remove_operator
      end.

    Definition to_cis1_balanceOf_params (query : list Address) (send_to : Address)
      : option CIS1_balanceOf_params :=
      match Bool.bool_dec (address_is_contract send_to) true with
      | left p =>
          Some {|cis1_bo_query := map (fun addr => Build_CIS1_balanceOf_query _ tt addr) query;
                 cis1_bo_result_address := send_to;
                 cis1_bo_result_address_is_contract := p |}
      | right _ => None
      end.

    Definition get_CIS1_entry_point : Msg -> option CIS1_entry_points :=
      fun msg => match msg with
              | wccd_msg_transfer params =>
                  let params :=
                    {| cis_tr_transfers := map to_cis1_transfer_data params|} in
                  Some (CIS1_transfer params)
              | wccd_msg_balanceOf query send_results_to =>
                  do p <- to_cis1_balanceOf_params query send_results_to;
                  Some (CIS1_balanceOf p)
              | wccd_msg_updateOperator params =>
                  let upd_list :=
                    map (fun '(upd_kind, addr) =>
                           Build_CIS1_updateOperator_update _ (to_cis1_updateOperator_kind upd_kind) addr) params in
                  Some (CIS1_updateOperator {| cis1_ou_params := upd_list |})
              | wccd_msg_mint receiver => None
              | wccd_msg_burn amount => None
              end.

    (** Converting _from_ the CIS1 standard parameters *)

    Definition from_cis1_transfer_data (p : CIS1_transfer_data) : wccd_transfer_params :=
      let '(Build_CIS1_transfer_data _ token_id amt from_addr to_addr) := p in
      {| wccd_td_token_id := tt;
         wccd_td_amount := amt;
         wccd_td_from := from_addr;
         wccd_td_to := to_addr |}.

    Definition from_cis1_updateOperator_kind (op : CIS1_updateOperator_kind) : OpUpdateKind :=
      match op with
      | cis1_ou_remove_operator => opDelete
      | cis1_ou_add_operator => opAdd
      end.

    Definition from_cis1_balanceOf_params (query : CIS1_balanceOf_params) : list Address :=
      map cis1_bo_query_address query.(cis1_bo_query).

    Definition get_contract_msg : CIS1_entry_points -> Msg :=
      fun ep => match ep with
             | CIS1_transfer params =>
                 wccd_msg_transfer (map from_cis1_transfer_data params.(cis_tr_transfers))
             | CIS1_updateOperator params =>
                 let p := map (fun p => (from_cis1_updateOperator_kind p.(cis1_ou_update_kind), p.(cis1_ou_operator_address))) params.(cis1_ou_params) in
                 wccd_msg_updateOperator p
             | CIS1_balanceOf params =>
                 wccd_msg_balanceOf (from_cis1_balanceOf_params params)
                                    params.(cis1_bo_result_address)
             end.

    Lemma left_inverse_get_CIS1_entry_point (entry_point : CIS1_entry_points) :
      get_CIS1_entry_point (get_contract_msg entry_point) = Some entry_point.
    Proof.
      destruct entry_point; cbn.
      + destruct params as [xs]. repeat f_equal.
        induction xs; auto.
        cbn. destruct a as [tid ? ?]; cbn in *. destruct tid. repeat f_equal; auto.
      + destruct params as [xs]. repeat f_equal.
        rewrite map_map.
        induction xs; auto.
        destruct a as [ok ?]; cbn in *. destruct ok; repeat f_equal; auto.
      + destruct params as [xs send_to p]; cbn in *.
        unfold to_cis1_balanceOf_params.
        destruct (Bool.bool_dec (address_is_contract send_to) true) eqn:Heq; repeat f_equal.
        * induction xs; cbn in *; auto.
          destruct a as [tid ?]; destruct tid; cbn; now repeat f_equal.
        * apply UIP_dec. apply Bool.bool_dec.
        * congruence.
    Qed.

    Lemma inctement_balance_find_ne st addr1 addr2 amt :
      addr1 <> addr2 ->
      AddressMap.find addr1 (increment_balance st addr2 amt) = AddressMap.find addr1 st.
    Proof.
      intros Hneq.
      unfold increment_balance.
      destruct (AddressMap.find addr2 _);
        unfold AddressMap.add, AddressMap.find;
        now rewrite fin_maps.lookup_insert_ne.
    Qed.

    Import Lia.

    Lemma wccd_transfer_single_cis1 (token_id : TokenID)
          (amt : TokenAmount) (owner_addr from_addr to_addr : Address)
          (prev_st st : State) :
      wccd_transfer_single token_id amt owner_addr from_addr to_addr prev_st = Some st ->
      transfer_single_spec prev_st st token_id eq_refl eq_refl owner_addr from_addr to_addr amt.
    Proof.
      intros Haddr.
      cbn in *.
      destruct (requireTrue (_ || _)) eqn:Hpermissions; try congruence.
      destruct (AddressMap.find _ _) as [v |] eqn:Hv; try congruence.
      destruct (requireTrue (_ <=? _)) eqn:Hbalance; try congruence.
      inversion Haddr; subst; clear Haddr.
      destruct (amt <=? wccd_balance v) eqn:Hamt; cbn in *; try congruence.
      apply leb_complete in Hamt.
      repeat split; cbn.
      + intros.
        unfold setter_from_getter_AddressState_wccd_balance,set_AddressState_wccd_balance.
        unfold WccdView.get_balance_opt, get_balance_opt.
        rewrite inctement_balance_find_ne by assumption.
        unfold AddressMap.find,AddressMap.add.
        now erewrite fin_maps.lookup_insert_ne.
      + intros. now destruct other_token_id,token_id.
      + unfold requireTrue in *. destruct (orb _ _) eqn:Hp; try congruence.
        rewrite Bool.orb_true_iff in *.
        destruct Hp as [Hp | Hp].
        * now destruct (address_eqb_spec owner_addr from_addr).
        * right.
          unfold is_operator in *.
          unfold WccdView.get_operators.
          destruct (AddressMap.find owner_addr prev_st) eqn:Hfind; try congruence.
          apply existsb_exists in Hp.
          destruct Hp as [addr0 [Hin Heq]].
          now destruct (address_eqb_spec from_addr addr0).
      + repeat rewrite get_balance_total_get_balance_default.
        repeat unfold setter_from_getter_AddressState_wccd_balance,
          set_AddressState_wccd_balance,increment_balance.
        unfold get_balance_default,cis1_axioms.VExtra.get_balance in *. cbn.
        unfold setter_from_getter_AddressState_wccd_balance,set_AddressState_wccd_balance.
        destruct (AddressMap.find to_addr _) eqn:Haddr.
        * unfold WccdView.get_balance_opt,get_balance_opt,AddressMap.find,AddressMap.add in *.
          rewrite Hv.
          rewrite FMap.add_commute with (m := prev_st) by auto.
          rewrite FMap.find_add with (m := (FMap.add _ _ prev_st)); cbn.
          lia.
        * unfold WccdView.get_balance_opt,get_balance_opt,AddressMap.find,AddressMap.add in *.
          rewrite FMap.add_commute with (m := prev_st) by auto.
          rewrite FMap.find_add with (m := (FMap.add _ _ prev_st)).
          cbn. rewrite Hv.
          lia.
      + repeat rewrite get_balance_total_get_balance_default.
        repeat unfold setter_from_getter_AddressState_wccd_balance,
          set_AddressState_wccd_balance,increment_balance.
        unfold get_balance_default,cis1_axioms.VExtra.get_balance in *. cbn.
        unfold setter_from_getter_AddressState_wccd_balance,set_AddressState_wccd_balance.
        destruct (AddressMap.find to_addr _) eqn:Haddr.
        * unfold WccdView.get_balance_opt,get_balance_opt,AddressMap.find,AddressMap.add in *.
          rewrite FMap.find_add with (m := (FMap.add _ _ prev_st)); cbn.
          rewrite FMap.find_add_ne with (m := prev_st) in Haddr by auto.
          unfold FMap.find in *.
          now rewrite Haddr.
        * unfold WccdView.get_balance_opt,get_balance_opt,AddressMap.find,AddressMap.add in *.
          rewrite FMap.find_add with (m := (FMap.add _ _ prev_st)); cbn.
          rewrite FMap.find_add_ne with (m := prev_st) in Haddr by auto.
          unfold FMap.find in *.
          now rewrite Haddr.
      + subst. repeat rewrite get_balance_total_get_balance_default.
        repeat unfold setter_from_getter_AddressState_wccd_balance,
          set_AddressState_wccd_balance,increment_balance.
        unfold get_balance_default,cis1_axioms.VExtra.get_balance in *. cbn.
        unfold setter_from_getter_AddressState_wccd_balance,set_AddressState_wccd_balance.
        unfold WccdView.get_balance_opt,get_balance_opt. now rewrite Hv.
      + subst.
        repeat rewrite get_balance_total_get_balance_default.
        repeat unfold setter_from_getter_AddressState_wccd_balance,
          set_AddressState_wccd_balance,increment_balance.
        unfold get_balance_default,cis1_axioms.VExtra.get_balance in *. cbn.
        unfold WccdView.get_balance_opt,get_balance_opt.
        rewrite Hv.
        unfold AddressMap.find,AddressMap.add.
        rewrite FMap.find_add with (m := prev_st); cbn.
        rewrite FMap.find_add with (m := FMap.add _ _ prev_st); cbn.
        lia.
    Qed.

    Definition contract_receive := wccd_receive.

    Lemma get_balances_wccd_balanceOf next_st c query send_results_to :
      to_cis1_balanceOf_params query send_results_to = Some c ->
      get_balances next_st c = Some (wccd_balanceOf query next_st).
    Proof.
      intros Hparams.
      unfold to_cis1_balanceOf_params in *.
      destruct (Bool.bool_dec (address_is_contract send_results_to)) eqn:Haddr;
        inversion Hparams; subst; clear Hparams.
      cbn.
      revert dependent next_st.
      revert dependent send_results_to.
      induction query.
      - now intros ? ? ? Hparams; cbn in *.
      - intros. cbn.
        erewrite IHquery; eauto.
        unfold WccdView.get_balance_opt.
        now destruct (get_balance_opt _ _).
    Qed.

    (** ** Receive specification *)
    Theorem receive_spec :
    forall (chain : Chain)
      (ctx : ContractCallContext)
      (entry : CIS1_entry_points)
      (msg : Msg)
      (prev_st next_st : State)
      (ops : list ActionBody),
      get_CIS1_entry_point msg = Some entry ->
      wccd_receive chain ctx prev_st (Some msg) = Some (next_st, ops) ->
      match entry with
      | CIS1_transfer params => transfer_spec ctx params prev_st next_st ops
      | CIS1_updateOperator params => updateOperator_spec ctx params prev_st next_st ops
      | CIS1_balanceOf params => balanceOf_spec params prev_st next_st ops
      end.
    Proof.
      intros ? ? ? ? ? ? ? Hep Hreceive.
      destruct msg; cbn; inversion Hep as [HH]; subst; clear Hep; try easy.
      + simpl in *.
        destruct (wccd_transfer _ _) eqn:Htr; try congruence.
        inversion Hreceive; subst; clear Hreceive.
        constructor.
        * cbn.
          revert dependent next_st.
          revert dependent prev_st.
          induction params.
          ** cbn in *. congruence.
          ** intros prev_st next_st Hreceive.
             cbn -[wccd_transfer_single] in *.
             destruct (wccd_transfer_single _ _ _ _ _) as [st |] eqn:Haddr; try congruence.
             destruct a as [tid amt from_addr to_addr]; cbn.
             simpl in *.
             exists st, eq_refl, eq_refl.
             split.
             *** cbn in *. now apply wccd_transfer_single_cis1.
             *** now eapply IHparams.
        * cbn.
          revert dependent prev_st.
          revert dependent next_st.
          induction params.
          ** intros; cbn; auto.
          ** intros; cbn -[wccd_transfer_single] in *.
             destruct (wccd_transfer_single _ _ _ _ _) as [st |] eqn:Haddr; try congruence.
             destruct a as [token_id amt addr]; cbn.
             destruct (address_is_contract _).
             *** constructor; simpl in *.
                 eexists. split.
                 **** reflexivity.
                 **** destruct token_id.
                      exists (TokenID * TokenAmount * Address)%type. exists _. exists id.
                      eexists. split.
                      apply deserialize_serialize.
                      reflexivity.
                 **** eapply IHparams; eauto.
             *** eapply IHparams; eauto.
      + simpl in *.
        destruct (address_is_contract send_results_to) eqn:Haddr;
          inversion Hreceive; subst; clear Hreceive; cbn in *.
        destruct (to_cis1_balanceOf_params _ _) eqn:Hto_cis1; inversion HH; subst; clear HH.
        constructor; subst; auto.
        erewrite get_balances_wccd_balanceOf; eauto.
        cbn. repeat f_equal.
        unfold to_cis1_balanceOf_params in *.
        destruct (Bool.bool_dec (address_is_contract send_results_to)) eqn:HH;
          now inversion Hto_cis1.
      + cbn in *.
        unfold setter_from_getter_AddressState_wccd_operators,set_AddressState_wccd_operators in *.
        constructor; intros; cbn in *; auto.
        * unfold WccdView.get_balance_opt,get_balance_opt.
          destruct (AddressMap.find _ _) eqn:Haddr; inversion Hreceive; subst; clear Hreceive.
          destruct (address_eqb_spec addr ctx.(ctx_from)).
          ** subst.
             rewrite Haddr.
             unfold AddressMap.find,AddressMap.add.
             now rewrite FMap.find_add with (m := prev_st).
          ** unfold AddressMap.find,AddressMap.add.
             now rewrite fin_maps.lookup_insert_ne.
        * destruct (AddressMap.find _ _) eqn:Haddr; inversion Hreceive; subst; clear Hreceive.
          destruct a as [bal ops]; cbn in *.
          revert dependent ops.
          revert dependent prev_st.
          induction params; intros prev_st ops Haddr.
          ** cbn.
             unfold AddressMap.add,AddressMap.find in *.
             now symmetry; apply FMap.add_id.
          ** cbn.
             unfold AddressMap.add,AddressMap.find in *.
             destruct a as [ok oaddr]; cbn in *.
             unfold updateOperator_single_spec; cbn.
             destruct ok; cbn in *.
             *** set (st := FMap.add (ctx_from ctx)
                                     {| wccd_balance := bal;
                                       wccd_operators := oaddr :: ops |} prev_st).
                 exists st. split.
                 **** split.
                      ***** intros.
                      subst st. unfold WccdView.get_operators,AddressMap.find.
                      rewrite Haddr. rewrite FMap.find_add with (m := prev_st).
                      cbn.
                      split; intros; auto. destruct H1; subst; congruence.
                      ***** subst st. unfold WccdView.get_operators,AddressMap.find.
                      now rewrite FMap.find_add with (m := prev_st); cbn.
                 **** set (ops' := oaddr :: ops).
                      specialize (IHparams st ops'). subst ops' st; cbn in *.
                      repeat rewrite FMap.add_add with (m := prev_st)in IHparams.
                      apply IHparams.
                      now rewrite FMap.find_add with (m := prev_st).
             *** set (st := FMap.add (ctx_from ctx)
                                     {| wccd_balance := bal;
                                        wccd_operators := remove address_eqdec oaddr ops |} prev_st).
                 exists st. split.
                 **** split.
                      (* the cases are essentially just properties of [remove], which we
                         prove using the [hint] database *)
                      ***** intros.
                      subst st. unfold WccdView.get_operators,AddressMap.find.
                      rewrite Haddr. rewrite FMap.find_add with (m := prev_st).
                      cbn.
                      split; intros; eauto with hints.
                      ***** subst st. unfold WccdView.get_operators,AddressMap.find.
                      rewrite FMap.find_add with (m := prev_st); cbn; auto with hints.
                 **** set (ops' := remove address_eqdec oaddr ops).
                      specialize (IHparams st ops'). subst ops' st; cbn in *.
                      repeat rewrite FMap.add_add with (m := prev_st)in IHparams.
                      apply IHparams.
                      now rewrite FMap.find_add with (m := prev_st).
    Qed.
  End WccdReceiveDefs.
End WccdReceiveSpec.
