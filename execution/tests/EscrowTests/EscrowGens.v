(* Generators for the Escrow contract, to be used for QuickChick testing.
   Main functions of interest: gEscrowMsg and gEscrowMsgBetter.
*)

From ConCert Require Import Blockchain Escrow.
From ConCert Require Import Serializable.
From ConCert.Execution.QCTests Require Import TestUtils TraceGens.

Require Import ZArith.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
Require Import Containers.

Module Type EscrowGensInfo.
  Parameter contract_addr : Address.
  Parameter gAccount : G Address.
  Parameter gAccountWithout : list Address -> GOpt Address.
End EscrowGensInfo.

Module EscrowGens (Info : EscrowGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.

(* Try to generate an account which has balance > 0. Returns None whenever no such address could be found.  *)
Definition gAccountWithBalance (e : Env) (gAccOpt : GOpt Address) : GOpt (Address * Amount) :=
  addr <- suchThatMaybeOpt gAccOpt (fun addr => 0 <? e.(account_balance) addr) ;;
  returnGenSome (addr, e.(account_balance) addr).

Definition gEscrowMsg (e : Env) : GOpt Action :=
  let call caller amount msg :=
  returnGenSome {|
    act_from := caller;
    act_body := act_call contract_addr amount (@serialize Escrow.Msg _ msg)
  |} in
  state <- returnGen (get_contract_state Escrow.State e contract_addr) ;;
  let buyer := state.(buyer) in
  let seller := state.(seller) in
  (* pick one generator uniformly at random from the given list.
     backtrack if one fails. *)
  backtrack [
    (* commit money *)
    (1%nat, 
        (* amount <- choose (0%Z, e.(account_balance) buyer) ;; *)
        if e.(account_balance) buyer <? 2
        then returnGen None
        else call buyer 2 commit_money
    ) ;
    (* confirm received item *)
    (1%nat, call buyer 0 confirm_item_received) ;
    (* withdraw money *)
    (1%nat, addr <- elems [seller; buyer] ;;
            call addr 0 withdraw
    )
  ].


(* This generator uses the 'next_step' state of the Escrow contract to determine which message to generate.
   This should lead to much fewer discards during testing, but at the cost of the generator being more complex
   and less "blackbox-like" *)
Definition gEscrowMsgBetter (e : Env) : GOpt Action :=
  let call caller amount msg :=
  returnGenSome {|
    act_from := caller;
    act_body := act_call contract_addr amount (@serialize Escrow.Msg _ msg)
  |} in
  state <- returnGen (get_contract_state Escrow.State e contract_addr) ;;
  let buyer := state.(buyer) in
  let seller := state.(seller) in
  match state.(next_step) with
  (* Waiting for buyer to commit itemvalue * 2. In this state, the seller can also choose to withdraw their deposit *)
  | buyer_commit => backtrack [
                      (2%nat, if e.(account_balance) buyer <? 2
                              then returnGen None
                              else call buyer 2 commit_money
                      );
                      (1%nat, call seller 0 withdraw)
                    ]
  | buyer_confirm => call buyer 0 confirm_item_received
  | _ => if 0 <? state.(buyer_withdrawable)
         then call buyer 0 withdraw
         else if 0 <? state.(seller_withdrawable)
         then call seller 0 withdraw
         else returnGen None
  end.

Close Scope Z_scope.

Definition gEscrowTrace cb length :=
  let max_act_depth := 1 in
  let max_acts_per_block := 1 in
  gChain cb (fun e _ => gEscrowMsg e) length max_act_depth max_acts_per_block.

Definition gEscrowTraceBetter cb length :=
  let max_act_depth := 1 in
  let max_acts_per_block := 1 in
  gChain cb (fun e _ => gEscrowMsgBetter e) length max_act_depth max_acts_per_block.

End EscrowGens.

Module DummyTestInfo <: EscrowGensInfo.
  Definition contract_addr := zero_address.
  Definition gAccount := returnGen zero_address.
  Definition gAccountWithout (ws : list Address) := returnGenSome zero_address.
End DummyTestInfo.
Module MG := EscrowGens.EscrowGens DummyTestInfo. Import MG.