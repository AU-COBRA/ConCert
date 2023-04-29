From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Dexter Require Import Dexter.
From ConCert.Examples.EIP20 Require Import EIP20Token.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith_base.
Import MonadNotation.

Module Type DexterTestsInfo.
  Parameter token_caddr : Address.
  Parameter dexter_contract_addr : Address.
  Parameter test_accounts : list Address.
End DexterTestsInfo.

Module DexterGens (Info : DexterTestsInfo).
  Import Info.

  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.

  Definition gTokensToExchange (balance : N) : GOpt N :=
    if N.eqb 0%N balance
    then returnGen None
    else
      amount <- choose (1%N, balance) ;;
      returnGenSome amount.

  Definition gTokenExchange (state : EIP20Token.State)
                            (caller : Address)
                            : GOpt Dexter.Msg :=
    let caller_tokens : N := Extras.with_default 0%N (FMap.find caller state.(balances)) in
    tokens_to_exchange <-- gTokensToExchange caller_tokens ;;
    let exchange_msg := {|
      exchange_owner := caller;
      tokens_sold := tokens_to_exchange;
    |} in
    returnGenSome (tokens_to_asset exchange_msg).

  Definition gDexterAction (env : Environment) : GOpt Action :=
    let mk_call caller_addr amount msg :=
      returnGenSome {|
        act_from := caller_addr;
        act_origin := caller_addr;
        act_body := act_call dexter_contract_addr amount (serialize Dexter.Msg _ msg)
      |} in
    token_state <-- returnGen (get_contract_state EIP20Token.State env token_caddr) ;;
    backtrack [
      (2, caller <- gAddrWithout [token_caddr; dexter_contract_addr] test_accounts ;;
          msg <-- gTokenExchange token_state caller ;;
          mk_call caller 0%Z msg
      )
    ].

  Definition gDexterChain max_acts_per_block cb length :=
    gChain cb (fun e _ => gDexterAction e) length 1 max_acts_per_block.

End DexterGens.
