From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.ExchangeBuggy Require Import ExchangeBuggy.
From ConCert.Examples.ExchangeBuggy Require Import ExchangeBuggyPrinters.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Import MonadNotation.

Module Type ExchangeTestsInfo.
  Parameter fa2_contract_addr : Address.
  Parameter exchange_contract_addr : Address.
  Parameter exploit_contract_addr : Address.
  Parameter accounts : list Address.
End ExchangeTestsInfo.

Module ExchangeGens (Info : ExchangeTestsInfo).
  Import Info.

  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.


  Section ExchangeContractGens.

    Definition gTokensToExchange (balance : N)
                                 : GOpt N :=
      if N.eqb 0%N balance
      then returnGen None
      else
        amount <- choose (0%N, balance) ;;
        returnGenSome amount.

    Definition gTokenExchange (state : FA2Token.State)
                              : GOpt (Address * ExchangeBuggy.Msg) :=
      let has_balance p :=
        let ledger := snd p in
        0 <? FMap.size ledger.(balances) in
      '(tokenid, ledger) <-- (sampleFMapOpt_filter state.(assets) has_balance) ;;
      let has_tokens p := N.ltb 0 (snd p) in
      '(addr, nr_tokens) <-- sampleFMapOpt_filter ledger.(balances) has_tokens ;;
      tokens_to_exchange <-- gTokensToExchange nr_tokens ;;
      let exchange_msg := {|
        exchange_owner := addr;
        exchange_token_id := tokenid;
        tokens_sold := tokens_to_exchange;
        callback_addr := exploit_contract_addr;
      |} in
      returnGenSome (addr, other_msg (ExchangeBuggy.tokens_to_asset exchange_msg)).

    Definition gAddTokensToReserve (env : Environment)
                                   (state : FA2Token.State)
                                   : GOpt (Address * Amount * ExchangeBuggy.Msg) :=
      tokenid <-- liftOpt fst (sampleFMapOpt state.(assets)) ;;
      caller <- gAddress accounts ;;
      amount <- choose (0%Z, env.(env_account_balances) caller) ;;
      returnGenSome (caller, amount, (other_msg (add_to_tokens_reserve tokenid))).

    (* NOTE: all call considered top-level calls (from users) *)
    Definition gExchangeAction (env : Environment) : GOpt Action :=
      let mk_call caller_addr amount msg :=
        returnGenSome {|
          act_origin := caller_addr;
          act_from := caller_addr;
          act_body := act_call exchange_contract_addr amount (serialize ExchangeBuggy.Msg _ msg)
        |} in
      fa2_state <-- returnGen (get_contract_state FA2Token.State env fa2_contract_addr) ;;
      backtrack [
      (1, '(caller, amount, msg) <-- gAddTokensToReserve env fa2_state ;;
            mk_call caller amount msg
        ) ;
        (2, caller <- gAddrWithout [fa2_contract_addr; exchange_contract_addr] accounts ;;
            '(_, msg) <-- gTokenExchange fa2_state ;;
            mk_call caller 0%Z msg
        )
      ].

  End ExchangeContractGens.

  Definition gExchangeChain max_acts_per_block cb length :=
    gChain cb (fun e _ => gExchangeAction e) length 1 max_acts_per_block.

  (* The '1' fixes the number of actions per block to 1 *)
  Definition token_reachableFrom max_acts_per_block cb pf : Checker :=
    reachableFrom_chaintrace cb (gExchangeChain max_acts_per_block) pf.

  Definition token_reachableFrom_implies_reachable {A}
                                                   length
                                                   max_acts_per_block
                                                   cb
                                                   (pf1 : ChainState -> option A)
                                                   pf2
                                                   : Checker :=
    reachableFrom_implies_chaintracePropSized length cb (gExchangeChain max_acts_per_block) pf1 pf2.

End ExchangeGens.
