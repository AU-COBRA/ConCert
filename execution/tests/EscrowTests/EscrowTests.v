From ConCert Require Import Blockchain LocalBlockchain Escrow EscrowExtras.
From ConCert Require Import Serializable.
From ConCert Require Import ResultMonad.
From ConCert Require Import BoundedN.
From ConCert Require Import Extras.
From ConCert Require Import ChainedList.
From ConCert Require Import Containers.
Require Import ZArith Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
(* From ExtLib.Structures Require Import Functor Applicative. *)
From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters SerializablePrinters TraceGens EscrowPrinters EscrowGens.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Import RecordSetNotations.

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
    (* build_act creator (act_transfer person_2 10); *)
    (* build_act creator (act_transfer person_3 10); *)
    (* build_act creator (act_transfer person_4 10); *)
    build_act seller (deploy_escrow 2)
  ]).

(* Compute (escrow_chain.(account_balance) seller). *)
(* = 0%Z
     : Amount 
*)
(* Compute (escrow_chain.(account_balance) buyer). *)
(* = 10%Z
     : Amount
*)

(* Compute (get_contract_state Escrow.State escrow_chain escrow_contract_addr). *)

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
    repeat rewrite Z.eqb_eq in H. 
    apply H.
  - intros. unfold escrow_correct_Prop. left. rewrite H1 in H0. inversion H0. 
Qed.

(* Wrapper for escrow_correct_bool. This is the Checker we will run QC on. *)
Definition escrow_correct_P (cb : ChainBuilder) := 
  let trace := builder_trace cb in
  let depinfo' := deployment_info Escrow.Setup trace escrow_contract_addr in
  let inc_calls' := incoming_calls Escrow.Msg trace escrow_contract_addr in
  isSomeCheck depinfo' (fun depinfo =>
    isSomeCheck inc_calls' (fun inc_calls =>
      match get_contract_state Escrow.State cb escrow_contract_addr with
      | Some cstate => 
          (escrow_correct_bool escrow_contract_addr cstate trace depinfo inc_calls)
      | None => false
      end
    )
  ).

(* QuickChick (forAllEscrowChainBuilder gEscrowTrace 7 escrow_chain escrow_correct_P). *)
(* *** Gave up! Passed only 8598 tests
Discarded: 20000 *)

(* Using the better generator, which avoid the discards: *)
(* QuickChick (forAllEscrowChainBuilder gEscrowTraceBetter 7 escrow_chain escrow_correct_P). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition next_step_eqb s1 s2 := 
  match s1, s2 with
  | buyer_commit, buyer_commit => true 
  | buyer_confirm, buyer_confirm => true
  | withdrawals, withdrawals => true
  | no_next_step, no_next_step => true
  | _, _ => false
  end.


Definition escrow_next_states {from to} 
                              (escrow_caddr : Address) 
                              (trace : ChainTrace from to) : list NextStep :=
  let fix rec {from to} (trace : ChainTrace from to) acc :=
    match trace with
    | snoc trace' step => match acc, get_contract_state Escrow.State to escrow_caddr with
                          | nextstep::_, Some state => 
                            if next_step_eqb nextstep state.(next_step)
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

Sample (
  bindGen (gEscrowTrace escrow_chain 10) (fun cb =>
    returnGen (escrow_next_states escrow_contract_addr (cb.(builder_trace))))
).

Definition is_valid_step_sequence steps := 
  let fix rec steps prev_step :=
  match prev_step, steps with
  | _, [] => true
  | None, step::steps' => rec steps' (Some step) 
  | Some prev_step, step::steps' => match prev_step, step with
                                    | buyer_commit, buyer_confirm
                                    | buyer_commit, no_next_step 
                                    | buyer_confirm, withdrawals
                                    | withdrawals, no_next_step => rec steps' (Some step)
                                    | _, _ => false
                                    end
  end in
  rec steps None.

Definition escrow_valid_steps_P cb := 
  let trace := builder_trace cb in
  let steps := escrow_next_states escrow_contract_addr trace in
  is_valid_step_sequence steps.

(* QuickChick (forAllEscrowChainBuilder gEscrowTrace 7 escrow_chain (checker o escrow_valid_steps_P)). *)
(* +++ Passed 10000 tests (0 discards) *)
 

(* Import Bool.
Import ssrbool.
Import Logic.Decidable.
Print Bool. *)


(* Lemma escrow_correct_bool_false_impl_prop {from to}
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
    intros. 
    propify. 
    repeat rewrite Z.eqb_neq in H.
    unfold not. intros.
    apply H0 in H1. 
    apply H.
  - intros. unfold escrow_correct_P. left. rewrite H1 in H0. inversion H0. 
Qed. *)
(* 

Instance escrow_correct_P_dec {from to caddr cstate trace depinfo inc_calls} 
  : Dec (@escrow_correct_Prop from to caddr cstate trace depinfo inc_calls).
  Proof. 
  constructor. unfold ssrbool.decidable. 
  destruct (escrow_correct_bool caddr cstate trace depinfo inc_calls) eqn:H.
  - left. apply escrow_correct_bool_impl_prop. apply H.
  - right. unfold escrow_correct_bool in H.   apply escrow_correct_bool_impl_prop in H. 

   
  rewrite (escrow_correct_bool_impl_prop caddr cstate trace depinfo inc_calls).
  remember (setup_buyer (deployment_setup depinfo)) as buyer.
  remember (deployment_from depinfo) as seller.
  remember (deployment_amount depinfo / 2) as item_worth.
  unfold escrow_correct_Prop;
  destruct (is_escrow_finished cstate) eqn:H1; 
  destruct (buyer_confirmed inc_calls buyer) eqn:H2; 
  destruct (net_balance_effect trace caddr seller =? item_worth) eqn:H3;
  destruct (net_balance_effect trace caddr buyer =? -item_worth) eqn:H4;
  rewrite <- Heqbuyer;
  rewrite <- Heqitem_worth;
  rewrite <- Heqseller;
  rewrite H2.
  - rewrite Z.eqb_eq in H3. rewrite H3.
    rewrite Z.eqb_eq in H4. rewrite H4.
    constructor.
    auto.
  - rewrite Z.eqb_eq in H3. rewrite H3.
    rewrite Z.eqb_neq in H4.
    right. unfold not. intros.
    destruct H; try reflexivity;
    destruct H; destruct H0. 
    + contradiction.
    + inversion H.
  - rewrite Z.eqb_neq in H3. 
    rewrite Z.eqb_eq in H4.


Admitted.
    apply eq_refl in H.
    inversion H.
     in H.
     
    constructor. intros. left. destr_bool.
    apply orb_l.
  -  apply bool_dec.
  - admit.
  -; unfold escrow_correct_P *)