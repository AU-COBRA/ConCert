From ConCert Require Import Blockchain LocalBlockchain Escrow EscrowExtras.
From ConCert Require Import Serializable.
From ConCert Require Import ResultMonad.
From ConCert Require Import BoundedN.
From ConCert Require Import Extras.
From ConCert Require Import ChainedList.
From ConCert Require Import Containers.
Require Import ZArith.

From QuickChick Require Import QuickChick. Import QcNotation.
From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters TraceGens EscrowPrinters EscrowGens.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Import RecordSetNotations.
Close Scope string_scope. 

(* First we derive decidable equality on NextStep *)
Scheme Equality for NextStep.
Instance nextstep_dec_eq : Dec_Eq NextStep.
Proof. constructor. apply NextStep_eq_dec. Defined.

(* Fix seller and buyer *)
Definition seller := creator.
Definition buyer := person_1.

Definition escrow_setup := {|
  setup_buyer := buyer
|}.

Definition deploy_escrow amount := create_deployment amount Escrow.contract escrow_setup.
Definition escrow_contract_addr : Address := BoundedN.of_Z_const AddrSize 128%Z.
Definition escrow_chain : ChainBuilder :=
  unpack_result (TraceGens.add_block (lcb_initial AddrSize)
  [
    build_act creator (act_transfer buyer 10);
    build_act seller (deploy_escrow 2)
  ]).

(* To instantiate the EscrowGen module functor, we need to supply
   an EscrowGensInfo module. *)
Module TestInfo <: EscrowGensInfo.
  Definition contract_addr := escrow_contract_addr.
  Definition gAccount := elems_ person_1 test_chain_addrs.
  Definition gAccountWithout (ws : list Address) :=
    let addrs := filter (fun a => negb (existsb (address_eqb a) ws)) test_chain_addrs in   
    elems_opt addrs.
End TestInfo.
Module MG := EscrowGens.EscrowGens TestInfo. Import MG.

Definition forAllEscrowChainBuilder gEscrowTrace length cb := 
  forAllChainBuilder length cb gEscrowTrace .

(* For automation *)
Instance gEscrowChainBuilder : GenSized ChainBuilder := 
{|
  arbitrarySized := gEscrowTraceBetter escrow_chain
|}.
Instance shrinkChainBuilder : Shrink ChainBuilder := {| shrink a := [a] |}.

(* Sample (gEscrowMsg escrow_chain). *)
(* Sample (gEscrowTraceBetter escrow_chain 10). *)
(* QuickChick (forAll (gEscrowTraceBetter escrow_chain 10) (fun cb =>
  1 <? (chain_height cb)
)). *)
(* +++ Passed 10000 tests (0 discards) *)

(* This is the proposition we wish to test, but QuickChick cannot test arbitrary Props since they are not
   decidable in general. Therefore, we define a boolean version, escrow_correct_bool, below and
   show that it implies escrow_correct_Prop. We then test on escrow_correct_bool instead.
   An alternative approach is to prove that escrow_correct_Prop is decidable, since QuickChick can test any
   decidable proposition (by coercing it to a bool) *)
Local Open Scope Z_scope.
Definition escrow_correct_Prop {from to}
                            (caddr : Address)
                            (cstate : Escrow.State)
                            (trace : ChainTrace from to) 
                            (depinfo : DeploymentInfo Setup)
                            (inc_calls : list (ContractCallInfo Msg)) : Prop := 
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

(* bool version of escrow_correct_Prop *)
Definition escrow_correct_bool {from to}
                            (caddr : Address)
                            (cstate : Escrow.State)
                            (trace : ChainTrace from to) 
                            (depinfo : DeploymentInfo Setup)
                            (inc_calls : list (ContractCallInfo Msg)) := 
  let item_worth := deployment_amount depinfo / 2 in
  let seller := deployment_from depinfo in
  let buyer := setup_buyer (deployment_setup depinfo) in
  if is_escrow_finished cstate
  then (buyer_confirmed inc_calls buyer &&
    ((net_balance_effect trace caddr seller =? item_worth) &&
    (net_balance_effect trace caddr buyer =? -item_worth)) 
    ||
    (negb (buyer_confirmed inc_calls buyer)) && 
    ((net_balance_effect trace caddr seller =? 0) &&
    (net_balance_effect trace caddr buyer =? 0)))
  else true.

(* We show that the bool version implies the propositional version
   of the correctness property. *)
Lemma escrow_correct_bool_impl_prop {from to}
                                    (caddr : Address)
                                    (cstate : Escrow.State)
                                    (trace : ChainTrace from to) 
                                    (depinfo : DeploymentInfo Setup)
                                    (inc_calls : list (ContractCallInfo Msg)) : 
  escrow_correct_bool caddr cstate trace depinfo inc_calls = true ->
  escrow_correct_Prop caddr cstate trace depinfo inc_calls.
Proof. 
  unfold escrow_correct_bool.
  destruct (is_escrow_finished cstate) eqn:H1.
  - unfold escrow_correct_Prop. 
    intros. 
    propify. 
    apply H.
  - intros. unfold escrow_correct_Prop. left. rewrite H1 in H0. inversion H0. 
Qed.

Lemma escrow_correct_bool_false_impl_prop {from to}
(caddr : Address)
(cstate : Escrow.State)
(trace : ChainTrace from to) 
(depinfo : DeploymentInfo Setup)
(inc_calls : list (ContractCallInfo Msg)) : 
  escrow_correct_bool caddr cstate trace depinfo inc_calls = false ->
  ~(escrow_correct_Prop caddr cstate trace depinfo inc_calls).
Proof. 
  unfold escrow_correct_bool.
  destruct (is_escrow_finished cstate) eqn:H1.
  - unfold escrow_correct_Prop. 
    propify. 
    intros.
    repeat rewrite Z.eqb_neq in H.
    intuition.
  - intros. unfold escrow_correct_Prop. eauto. 
Qed.

(* Finally, we can show that escrow_correct_Prop is decidable (using escrow_correct_bool as 
   the decision procedure).  *)
Instance escrow_correct_P_dec {from to caddr cstate trace depinfo inc_calls} 
  : Dec (@escrow_correct_Prop from to caddr cstate trace depinfo inc_calls).
Proof. 
  constructor. unfold ssrbool.decidable. 
  destruct (escrow_correct_bool caddr cstate trace depinfo inc_calls) eqn:H.
  - left. apply escrow_correct_bool_impl_prop. apply H.
  - right. 
    unfold not. 
    intros.
    apply escrow_correct_bool_false_impl_prop in H.
    contradiction.
Defined.

Instance escrow_correct_P_checkable {from to caddr cstate trace depinfo inc_calls}
  : Checkable (@escrow_correct_Prop from to caddr cstate trace depinfo inc_calls).
Proof. apply testDec. Defined.

(* Wrapper for escrow_correct_bool. This is the Checker we will run QC on. *)
Definition escrow_correct_P (cb : ChainBuilder) := 
  let trace := builder_trace cb in
  let depinfo' := deployment_info Escrow.Setup trace escrow_contract_addr in
  let inc_calls' := incoming_calls Escrow.Msg trace escrow_contract_addr in
  isSomeCheck depinfo' (fun depinfo =>
    isSomeCheck inc_calls' (fun inc_calls =>
      match get_contract_state Escrow.State cb escrow_contract_addr with
      | Some cstate => is_escrow_finished cstate ==>
        ((escrow_correct_Prop escrow_contract_addr cstate trace depinfo inc_calls)?)
      | None => checker false
      end
    )
  ).

Extract Constant defNumDiscards => "(3 * defNumTests)".

QuickChick (forAllEscrowChainBuilder gEscrowTrace 7 escrow_chain escrow_correct_P).
(* *** Gave up! Passed only 8598 tests
Discarded: 20000 *)

(* Using the better generator, which avoid the discards: *)
(* QuickChick (forAllEscrowChainBuilder gEscrowTraceBetter 7 escrow_chain escrow_correct_P). *)
(* +++ Passed 10000 tests (0 discards) *)
(* Or alternatively we can just write: *)
(* QuickChick escrow_correct_P. *)
(* +++ Passed 10000 tests (40 discards) *)
(* Not sure where the 40 discards come from, but it's an acceptable amount for sure... *)

Definition escrow_next_states {from to} 
                              (escrow_caddr : Address) 
                              (trace : ChainTrace from to) : list NextStep :=
  let fix rec {from to} (trace : ChainTrace from to) acc :=
    match trace with
    | snoc trace' step => match acc, get_contract_state Escrow.State to escrow_caddr with
                          | nextstep::_, Some state => 
                            if (nextstep = state.(next_step))?
                            then rec trace' acc
                            else rec trace' (state.(next_step) :: acc)
                          | [], Some state => rec trace' (state.(next_step) :: acc)
                          | _, _ => rec trace' acc
                          end 
    | clnil => acc
    end in rec trace [].

(* We want to see what the length of the generated sequences of next_step are,
   so we use QuickChick's 'collect' to collect length distribution statistics *)
Definition collect_steps_length_distribution g :=
  forAll (g escrow_chain 10%nat) (fun cb =>
    collect (length (escrow_next_states escrow_contract_addr (cb.(builder_trace))))
    true).

(* QuickChick (collect_steps_length_distribution gEscrowTrace). *)
(* 
4812 : 2
2470 : 1
2244 : 3
474 : 4
+++ Passed 10000 tests (0 discards) *)
(* QuickChick (collect_steps_length_distribution gEscrowTraceBetter). *)
(* 
6636 : 4
3364 : 2
+++ Passed 10000 tests (0 discards) *)

(* We see that the "better" generator more often generates the full sequence of states, namely the sequence:
   buyer_commit -> buyer_confirm -> withdrawals -> no_next_step
   The sequence of length 2 is the sequence:
   buyer_commit -> no_next_step
   Corresponding to the case where the seller withdraws their funds before the buyer commits & confirms their purchase. *)

Fixpoint is_valid_step_sequence_fix steps prev_step :=
  match prev_step, steps with
  | _, [] => true
  | None, step::steps' => is_valid_step_sequence_fix steps' (Some step) 
  | Some prev_step, step::steps' => match prev_step, step with
                                    | buyer_commit, buyer_confirm
                                    | buyer_commit, no_next_step 
                                    | buyer_confirm, withdrawals
                                    | withdrawals, no_next_step => is_valid_step_sequence_fix steps' (Some step)
                                    | _, _ => false
                                    end
  end.

Definition is_valid_step_sequence steps := 
  is_valid_step_sequence_fix steps None.


Conjecture escrow_valid_steps_P : forall trace : {to : ChainState & ChainTrace empty_state to},
  let steps := escrow_next_states escrow_contract_addr (projT2 trace) in
  is_valid_step_sequence steps = true.
(* Note that we are implicitly using the "better" generator here to generate arbitrary ChainTraces *)
(* QuickChick escrow_valid_steps_P. *)
(* +++ Passed 10000 tests (0 discards) *)

Corollary escrow_correct
            {ChainBuilder : ChainBuilderType}
            prev new header acts :
    builder_add_block prev header acts = Ok new ->
    let trace := builder_trace new in
    forall caddr,
      env_contracts new caddr = Some (Escrow.contract : WeakContract) ->
      let next_states := escrow_next_states caddr trace in
      is_valid_step_sequence next_states = true.
Proof.
Admitted.  (* intros after_add trace caddr escrow_at_caddr next_states. *)
  (* unfold trace.
  contract_induction.
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
    lia. *)

(* 
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

*)
