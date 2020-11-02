(* QuickChick tests of the Escrow contract. The properties tested are:
   - functional correctness (also proved in Escrow.v)
   - the next_step field satisfies a certain ordering (e.g. buyer_commit -> buyer_confirm -> withdrawals)
*)

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
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Import RecordSetNotations.
Close Scope string_scope. 

Section TestSetup.
  (* Fix seller and buyer *)
  Definition seller := creator.
  Definition buyer := person_1.

  Definition escrow_setup := {|
    setup_buyer := buyer
  |}.

  Definition deploy_escrow amount := create_deployment amount Escrow.contract escrow_setup.
  Definition escrow_contract_addr : Address := BoundedN.of_Z_const AddrSize 128%Z.
  (* The initial blockchain with the escrow contract deployed, and with buyer balance = 10 *)
  Definition escrow_chain : ChainBuilder :=
    unpack_result (TraceGens.add_block (lcb_initial AddrSize)
    [
      build_act creator (act_transfer buyer 10);
      build_act seller (deploy_escrow 2)
    ]).
    
End TestSetup.

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
Section TestGenInstances.
  
  Definition forAllEscrowChainBuilder gEscrowTrace length cb := 
    forAllChainBuilder length cb gEscrowTrace .
  
  (* For automation *)
  Global Instance gEscrowChainBuilder : GenSized ChainBuilder := 
  {|
    arbitrarySized := gEscrowTraceBetter escrow_chain
  |}.
  Global Instance shrinkChainBuilder : Shrink ChainBuilder := {| shrink a := [a] |}.

End TestGenInstances.

Section TestProperties.

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
  Lemma escrow_correct_bool_refl_prop {from to}
                                      (caddr : Address)
                                      (cstate : Escrow.State)
                                      (trace : ChainTrace from to) 
                                      (depinfo : DeploymentInfo Setup)
                                      (inc_calls : list (ContractCallInfo Msg)) : 
    escrow_correct_bool caddr cstate trace depinfo inc_calls = true <->
    escrow_correct_Prop caddr cstate trace depinfo inc_calls.
  Proof. 
    unfold escrow_correct_bool.
    split.
    - destruct (is_escrow_finished cstate) eqn:H1.
      + unfold escrow_correct_Prop. 
        intros. 
        propify. 
        apply H.
      + intros. unfold escrow_correct_Prop. 
        left. rewrite H1 in H0.
        inversion H0.
    - destruct (is_escrow_finished cstate) eqn:H1.
      + unfold escrow_correct_Prop. 
        propify. 
        intros. 
        repeat rewrite Z.eqb_eq.
        apply H.
        apply H1.
      + intros. reflexivity.
  Qed.

  (* Finally, we can show that escrow_correct_Prop is decidable (using escrow_correct_bool as 
    the decision procedure).  *)
  Global Instance escrow_correct_P_dec {from to caddr cstate trace depinfo inc_calls} 
    : Dec (@escrow_correct_Prop from to caddr cstate trace depinfo inc_calls).
  Proof. 
    constructor. unfold ssrbool.decidable.
    destruct (escrow_correct_bool caddr cstate trace depinfo inc_calls) eqn:H.
    - left. apply escrow_correct_bool_refl_prop. apply H.
    - right. 
      unfold not. 
      intros.
      apply escrow_correct_bool_refl_prop in H0.
      eauto.
  Defined.

  Global Instance escrow_correct_P_checkable {from to caddr cstate trace depinfo inc_calls}
    : Checkable (@escrow_correct_Prop from to caddr cstate trace depinfo inc_calls).
  Proof. apply testDec. Defined.

  Notation "a ===> f" := (isSomeCheck a f) (at level 44).

  (* Wrapper for escrow_correct_bool. This is the Checker we will run QC on. *)
  Definition escrow_correct_P (cb : ChainBuilder) := 
    let trace := builder_trace cb in
    let depinfo' := deployment_info Escrow.Setup trace escrow_contract_addr in
    let inc_calls' := incoming_calls Escrow.Msg trace escrow_contract_addr in
    depinfo'  ===>  (fun depinfo =>
    inc_calls' ===>  (fun inc_calls =>
      match get_contract_state Escrow.State cb escrow_contract_addr with
      (* main part of the property: *)
      | Some cstate => 
        is_escrow_finished cstate ==>
        ((escrow_correct_Prop escrow_contract_addr cstate trace depinfo inc_calls)?)
      | None => checker false
      end
    )).

  (* we derive decidable equality on NextStep *)
  Scheme Equality for NextStep.
  Instance nextstep_dec_eq : Dec_Eq NextStep.
  Proof. constructor. apply NextStep_eq_dec. Defined.
  
  Definition escrow_next_states {from to} 
                                (escrow_caddr : Address) 
                                (trace : ChainTrace from to) : list NextStep :=
    let fix rec {from to} (trace : ChainTrace from to) acc :=
      match trace with
      | snoc trace' step => 
        match acc, get_contract_state Escrow.State to escrow_caddr with
        | nextstep::_, Some state => if (nextstep = state.(next_step))?
                                     then rec trace' acc
                                     else rec trace' (state.(next_step) :: acc)
        | [], Some state => rec trace' (state.(next_step) :: acc)
        | _, _ => rec trace' acc
        end 
      | clnil => acc
      end in 
  rec trace [].

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

  (* Test property *)
  Conjecture escrow_valid_steps_P : forall trace : {to : ChainState & ChainTrace empty_state to},
  let steps := escrow_next_states escrow_contract_addr (projT2 trace) in
  is_valid_step_sequence steps = true.

End TestProperties.

(* ---------- Test execution ---------- *)

Extract Constant defNumDiscards => "(2 * defNumTests)".

(* QuickChick (forAllEscrowChainBuilder gEscrowTrace 7 escrow_chain escrow_correct_P). *)
(* *** Gave up! Passed only 8598 tests
Discarded: 20000 *)

(* Using the better generator, which avoid the discards: *)
(* QuickChick (forAllEscrowChainBuilder gEscrowTraceBetter 7 escrow_chain escrow_correct_P). *)
(* +++ Passed 10000 tests (0 discards) *)
(* Or alternatively we can just write: *)
(* QuickChick escrow_correct_P. *)
(* +++ Passed 10000 tests (40 discards) *)
(* Not sure where the 40 discards come from, but it's an acceptable amount for sure... *)

(* Note that we are implicitly using the "better" generator here to generate arbitrary ChainTraces *)
(* QuickChick escrow_valid_steps_P. *)
(* +++ Passed 10000 tests (0 discards) *)
