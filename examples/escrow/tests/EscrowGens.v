(* Generators for the Escrow contract, to be used for QuickChick testing.
   Main functions of interest: gEscrowMsg and gEscrowMsgBetter.
*)

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Escrow Require Import Escrow.
Import MonadNotation.
From Coq Require Import ZArith.
From Coq Require Import List. Import ListNotations.

Module Type EscrowGensInfo.
  Parameter contract_addr : Address.
End EscrowGensInfo.

Module EscrowGens (Info : EscrowGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.

(* Try to generate an account which has balance > 0.
   Returns None whenever no such address could be found. *)
Definition gAccountWithBalance (e : Env)
                               (gAccOpt : GOpt Address)
                               : GOpt (Address * Amount) :=
  addr <-- suchThatMaybeOpt gAccOpt (fun addr => 0 <? e.(env_account_balances) addr) ;;
  returnGenSome (addr, e.(env_account_balances) addr).

Definition gEscrowMsg (e : Env) : GOpt Action :=
  let call caller amount msg :=
      returnGenSome {|
          act_origin := caller;
          act_from := caller;
          act_body := act_call contract_addr amount (@serialize Escrow.Msg _ msg)
        |} in
  state <-- returnGen (get_contract_state Escrow.State e contract_addr) ;;
  let buyer := state.(buyer) in
  let seller := state.(seller) in
  (* Pick one generator uniformly at random from the given list.
     Backtrack if one fails. *)
  backtrack [
    (* commit money *)
    (1%nat,
        (* amount <- choose (0%Z, e.(account_balance) buyer) ;; *)
        if e.(env_account_balances) buyer <? 2
        then returnGen None
        else
          call buyer 2 commit_money
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
          act_origin := caller;
          act_from := caller;
          act_body := act_call contract_addr amount (@serialize Escrow.Msg _ msg)
  |} in
  state <-- returnGen (get_contract_state Escrow.State e contract_addr) ;;
  let buyer := state.(buyer) in
  let seller := state.(seller) in
  match state.(next_step) with
  (* Waiting for buyer to commit itemvalue * 2.
     In this state, the seller can also choose to withdraw their deposit *)
  | buyer_commit => backtrack [
                      (2%nat, if e.(env_account_balances) buyer <? 2
                              then returnGen None
                              else
                                call buyer 2 commit_money
                      );
                     (1%nat,
                      call seller 0 withdraw)
                    ]
  | buyer_confirm => call buyer 0 confirm_item_received
  | _ => if 0 <? state.(buyer_withdrawable)
        then
          call buyer 0 withdraw
         else if 0 <? state.(seller_withdrawable)
              then
                call seller 0 withdraw
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

Definition forAllEscrowChainBuilder `{Show ChainBuilder}
                                    gEscrowTrace
                                    length
                                    (cb : ChainBuilder) :=
  forAllChainBuilder length cb gEscrowTrace.
End EscrowGens.
