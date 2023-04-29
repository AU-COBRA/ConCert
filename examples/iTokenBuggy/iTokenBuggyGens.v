From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.iTokenBuggy Require Import iTokenBuggy.
Import MonadNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.

Module Type iTokenBuggyGensInfo.
  Parameter contract_addr : Address.
  Parameter gAccount : G Address.
End iTokenBuggyGensInfo.

Module iTokenBuggyGens (Info : iTokenBuggyGensInfo).
  Import Info.
  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.

  Definition serializeMsg := @serialize iTokenBuggy.Msg _.

  Local Open Scope N_scope.

  Definition sampleFMapOpt {A B : Type}
                          `{countable.Countable A}
                          `{base.EqDecision A}
                           (m : FMap A B)
                           : GOpt (A * B) :=
    TestUtils.sampleFMapOpt m.

  (* Note: not optimal implementation. Should filter on
     balances map instead of first sampling and then filtering *)
  Definition gApprove (state : iTokenBuggy.State) : GOpt (Address * Msg) :=
    '((addr1, balance1), (addr2, balance2)) <-- sample2UniqueFMapOpt state.(balances) ;;
    if 0 <? balance1
    then amount <- choose (0, balance1) ;;
         returnGenSome (addr1, approve addr2 amount)
    else if 0 <? balance2
    then amount <- choose (0, balance2) ;;
         returnGenSome (addr2, approve addr1 amount)
    else returnGen None.

  Definition gTransfer_from (state : iTokenBuggy.State) : GOpt (Address * Msg) :=
    '(allower, allowance_map) <-- sampleFMapOpt state.(allowances) ;;
    '(delegate, allowance) <-- sampleFMapOpt allowance_map ;;
    '(receiver,_) <-- sampleFMapOpt state.(balances) ;;
    let allower_balance := (FMap_find_ allower state.(balances) 0) in
    amount <- (if allower_balance =? 0
              then returnGen 0
              else choose (0, N.min allowance allower_balance)) ;;
    returnGenSome (delegate, transfer_from allower receiver amount).

  Definition gMint (c : Environment)
                   (state : iTokenBuggy.State)
                   : GOpt (Address * Msg) :=
    addr <- gAccount ;;
    (* fix the number of minted tokens to 0, 1, or 2*)
    amount <- choose (0, 2) ;;
    returnGenSome (addr, mint amount ).

  Definition gBurn (state : iTokenBuggy.State) : GOpt (Address * Msg) :=
    '(addr, balance) <-- sampleFMapOpt_filter state.(balances) (fun '(_,balance) => 0 <? balance) ;;
    (* we purposely give it a small chance to try to burn more than allowed, hence +2*)
    amount <- choose (0, balance + 2) ;;
    returnGenSome (addr, burn amount).

  Local Close Scope N_scope.
  (* Main generator. *)
  Definition giTokenBuggyAction (env : Environment) : GOpt Action :=
    let call caller_addr contract_addr msg :=
        returnGenSome {|
            act_origin := caller_addr;
            act_from := caller_addr;
            act_body := act_call contract_addr 0%Z (serializeMsg msg)
          |} in
    state <-- returnGen (get_contract_state iTokenBuggy.State env contract_addr) ;;
    backtrack [
      (* mint *)
      (1, '(caller, msg) <-- gMint env state ;;
          call caller contract_addr msg
      ) ;
      (* burn *)
      (1, '(caller, msg) <-- gBurn state ;;
          call caller contract_addr msg
      ) ;
      (* transfer_from *)
      (4, '(caller, msg) <-- gTransfer_from state ;;
          call caller contract_addr msg
      );
      (* approve *)
      (2, '(caller, msg) <-- gApprove state ;;
          call caller contract_addr msg
      )
    ].

End iTokenBuggyGens.
