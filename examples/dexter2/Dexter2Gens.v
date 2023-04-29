From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2LegacyInterface.
From ConCert.Examples.Dexter2 Require Import Dexter2CPMM.
From ConCert.Examples.Dexter2 Require Import Dexter2Printers.
Import MonadNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.

Module Type Dexter2Info.
  Parameter accounts : list Address.
  Parameter gAddr : Chain -> G Address.
  Parameter cpmm_contract_addr : Address.
  Parameter token_contract_addr : Address.
  Parameter token_id : N.
End Dexter2Info.

Module Dexter2Gens (Info : Dexter2Info).
  Import Info.
  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.

  (** * Dexter2 CPMM generators *)

  Definition gNonBrokeAddr (env : Environment) : GOpt Address :=
    let freq_accounts := map (fun addr =>
      (Z.to_nat ((env_account_balances env) addr), returnGenSome addr)) accounts in
    freq_ (returnGen None) freq_accounts.

  Definition gUpdateTokenPool (env : Environment) : G (Address * Amount * Dexter2CPMM.Msg) :=
    from_addr <- gAddr env ;;
    returnGen (from_addr, 0%Z, FA2Token.other_msg UpdateTokenPool).

  Definition gXtzToToken (env : Environment) : GOpt (Address * Amount * Dexter2CPMM.Msg) :=
    from_addr <-- gNonBrokeAddr env ;;
    deadline <- (choose (env.(current_slot) + 1, env.(current_slot) + 10)) ;;
    amount <- (choose (1%Z, (env_account_balances env) from_addr)) ;;
    let param := {|
      tokens_to := from_addr;
      minTokensBought := 1%N;
      xtt_deadline := deadline
    |} in
    returnGenSome (from_addr, amount, FA2Token.other_msg (XtzToToken param)).

  Definition gTokenToXtz (env : Environment) : G (Address * Amount * Dexter2CPMM.Msg) :=
    from_addr <- gAddr env ;;
    deadline <- choose (env.(current_slot) + 1, env.(current_slot) + 10) ;;
    amount <- choose (30, 50)%N ;;
    let param := {|
      xtz_to := from_addr;
      tokensSold := amount;
      minXtzBought := 1;
      ttx_deadline := deadline
    |} in
    returnGen (from_addr, 0%Z, FA2Token.other_msg (TokenToXtz param)).

  (** * FA2 generators *)
  Definition gBalanceOf (env : Environment) : G (Address * Amount * FA2Token.Msg) :=
    from_addr <- gAddr env ;;
    request_addr <- gAddr env ;;
    let param := {|
      bal_requests := [
        {|
          FA2LegacyInterface.owner := request_addr;
          bal_req_token_id := token_id
        |}
      ];
      bal_callback := FA2LegacyInterface.Build_callback _ None cpmm_contract_addr
    |} in
    returnGen (from_addr, 0%Z, FA2Token.msg_balance_of param).

  (** * Combined generators *)
  Definition gAction (env : Environment) : GOpt Action :=
    let call contract_addr caller_addr value msg :=
      returnGenSome (build_act caller_addr caller_addr (act_call contract_addr value msg)) in
    let call_cpmm caller_addr value msg :=
      call cpmm_contract_addr caller_addr value (@serialize Dexter2CPMM.Msg _ msg) in
    let call_token caller_addr value msg :=
      call token_contract_addr caller_addr value (@serialize FA2Token.Msg _ msg) in
    backtrack [
      (* UpdateTokenPool *)
      (1, '(caller, value, msg) <- gUpdateTokenPool env ;;
          call_cpmm caller value msg
      );
      (* XtzToToken *)
      (1, bindOpt (gXtzToToken env)
          (fun '(caller, value, msg) =>
            call_cpmm caller value msg
          )
      );
      (* TokenToXtz *)
      (1, '(caller, value, msg) <- gTokenToXtz env ;;
          call_cpmm caller value msg
      );
      (* BalanceOf *)
      (1, '(caller, value, msg) <- gBalanceOf env ;;
          call_token caller value msg
      )].
End Dexter2Gens.
