From ConCert Require Import Blockchain LocalBlockchain Escrow.
From ConCert Require Import Serializable.
From ConCert Require Import ResultMonad.
From ConCert Require Import BoundedN.
From ConCert Require Import Extras.
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
(* Sanity check: *)
(* QuickChick (forAll (gEscrowTraceBetter escrow_chain 10) (fun cb =>
  5 =? (chain_height cb)
)). *)
(* +++ Passed 10000 tests (0 discards) *)
(* This implies that all generated traces follow the pattern: 
   commit_money -> confirm_item_received -> withdraw (buyer/seller) -> withdraw (buyer/seller) *)
Local Open Scope Z_scope.
Definition escrow_correct_bool {from to}
                            (caddr : Address)
                            (cstate : Escrow.State)
                            (trace : ChainTrace from to) 
                            (depinfo : DeploymentInfo Setup)
                            (inc_calls : list (ContractCallInfo Msg)) := 
  let item_worth := deployment_amount depinfo / 2 in
  let seller := deployment_from depinfo in
  let buyer := setup_buyer (deployment_setup depinfo) in
  is_escrow_finished cstate ==>
  ((buyer_confirmed inc_calls buyer &&
    (net_balance_effect trace caddr seller =? item_worth) &&
    (net_balance_effect trace caddr buyer =? -item_worth)) 
    ||
    ((negb (buyer_confirmed inc_calls buyer)) && 
    (net_balance_effect trace caddr seller =? 0) &&
    (net_balance_effect trace caddr buyer =? 0))).


Definition escrow_correct_P (cb : ChainBuilder) := 
  let trace := builder_trace cb in
  let depinfo' := deployment_info Escrow.Setup trace escrow_contract_addr in
  let inc_calls' := incoming_calls Escrow.Msg trace escrow_contract_addr in
  conjoin [
    (* checker (isSome depinfo'); *)
    (* checker (negb (isSome inc_calls')); *)
    isSomeCheck depinfo' (fun depinfo =>
      isSomeCheck inc_calls' (fun inc_calls =>
        match get_contract_state Escrow.State cb escrow_contract_addr with
        | Some cstate => 
            (escrow_correct_bool escrow_contract_addr cstate trace depinfo inc_calls)
        | None => checker false
        end
      )
    )
  ].

(* QuickChick (forAllEscrowChainBuilder gEscrowTrace 7 escrow_chain escrow_correct_P). *)
(* *** Gave up! Passed only 8598 tests
Discarded: 20000 *)

(* Using the better generator, which avoid the discards: *)
(* QuickChick (forAllEscrowChainBuilder gEscrowTraceBetter 7 escrow_chain escrow_correct_P). *)
(* +++ Passed 10000 tests (0 discards) *)




(* 

From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import List.
From Equations Require Import Equations.
From MetaCoq Require Import utils.

Derive Signature for Forall.
Derive Signature for Forall2.
Derive Signature for OnOne2.

Ltac propify :=
  unfold is_true in *;
  repeat
    match goal with
    | [H: context[Nat.eqb _ _ = false] |- _] => rewrite Nat.eqb_neq in H
    | [H: context[Nat.eqb _ _ = true] |- _] => rewrite Nat.eqb_eq in H
    | [H: context[Nat.ltb _ _ = false] |- _] => rewrite Nat.ltb_ge in H
    | [H: context[Nat.ltb _ _ = true] |- _] => rewrite Nat.ltb_lt in H
    | [H: context[Nat.leb _ _ = false] |- _] => rewrite Nat.leb_gt in H
    | [H: context[Nat.leb _ _ = true] |- _] => rewrite Nat.leb_le in H
    | [H: context[andb _ _ = false] |- _] => rewrite Bool.andb_false_iff in H
    | [H: context[andb _ _ = true] |- _] => rewrite Bool.andb_true_iff in H
    | [H: context[negb _ = false] |- _] => rewrite Bool.negb_false_iff in H
    | [H: context[negb _ = true] |- _] => rewrite Bool.negb_true_iff in H
    | [H: context[orb _ _ = false] |- _] => rewrite Bool.orb_false_iff in H
    | [H: context[orb _ _ = true] |- _] => rewrite Bool.orb_true_iff in H
    | [|- context[Nat.eqb _ _ = false]] => rewrite Nat.eqb_neq
    | [|- context[Nat.eqb _ _ = true]] => rewrite Nat.eqb_eq
    | [|- context[Nat.ltb _ _ = false]] => rewrite Nat.ltb_ge
    | [|- context[Nat.ltb _ _ = true]] => rewrite Nat.ltb_lt
    | [|- context[Nat.leb _ _ = false]] => rewrite Nat.leb_gt
    | [|- context[Nat.leb _ _ = true]] => rewrite Nat.leb_le
    | [|- context[andb _ _ = false]] => rewrite Bool.andb_false_iff
    | [|- context[andb _ _ = true]] => rewrite Bool.andb_true_iff
    | [|- context[negb _ = false]] => rewrite Bool.negb_false_iff
    | [|- context[negb _ = true]] => rewrite Bool.negb_true_iff
    | [|- context[orb _ _ = false]] => rewrite Bool.orb_false_iff
    | [|- context[orb _ _ = true]] => rewrite Bool.orb_true_iff
    end.
*)

(* Definition escrow_correct_P {from to}
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

Lemma asd {from to}
(caddr : Address)
(cstate : Escrow.State)
(trace : ChainTrace from to) 
(depinfo : DeploymentInfo Setup)
(inc_calls : list (ContractCallInfo Msg)) : 
  escrow_correct_bool caddr cstate trace depinfo inc_calls ->
  escrow_correct_P caddr cstate trace depinfo inc_calls.
Proof. 
  unfold escrow_correct_bool.
  destruct (is_escrow_finished cstate) eqn:H1.
  - unfold escrow_correct_P. intros. admit.
  - intros. unfold escrow_correct_P. left. rewrite H1 in H0. inversion H0. 
Admitted.

Import Bool.
Import ssrbool.
Import Logic.Decidable.
Print Bool.
Instance escrow_correct_P_dec {from to caddr cstate trace depinfo inc_calls} 
  : Dec (@escrow_correct_P from to caddr cstate trace depinfo inc_calls).
  Proof. 
  constructor.
  remember (setup_buyer (deployment_setup depinfo)) as buyer.
  remember (deployment_from depinfo) as seller.
  remember (deployment_amount depinfo / 2) as item_worth.
  unfold escrow_correct_P;
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
    right. unfold not. intros. 
    inversion H.
     in H.
     
    constructor. intros. left. destr_bool.
    apply orb_l.
  -  apply bool_dec.
  - admit.
  -; unfold escrow_correct_P *)