From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.BAT Require Import BATCommon.
From ConCert.Examples.BAT Require Import BATPrinters.
From ConCert.Examples.EIP20 Require Import EIP20TokenGens.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Import MonadNotation.


Module Type BATGensInfo.
  Parameter trace_length : nat.
  Parameter gAccount : G Address.
  Parameter contract_addr : Address.
  Parameter accounts : list Address.
  Parameter accounts_total_balance : Z.
  Parameter bat_addr : Address.
  Parameter fund_addr : Address.
  Parameter bat_addr_refundable : bool.
  Parameter bat_addr_fundable : bool.
  Parameter eip20_transactions_before_finalized : bool.
End BATGensInfo.

Module BATGens (Info : BATGensInfo).
  Import Info.
  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.

  Definition account_balance (env : Environment) (addr : Address) : Amount :=
    (env_account_balances env) addr.

  Definition get_refundable_accounts state : list (GOpt Address) :=
    let balances_list := FMap.elements (balances state) in
    let filtered_balances := filter (fun x => (bat_addr_refundable || (address_neqb bat_addr (fst x))) && (0 <? (snd x))%N) balances_list in
      map returnGen (map Some (map fst filtered_balances)).

  Definition get_fundable_accounts env : GOpt Address :=
    let freq_accounts := map (fun addr => (if bat_addr_fundable || (address_neqb addr bat_addr) then Z.to_nat (account_balance env addr) else 0, returnGenSome addr)) accounts in
      freq_ (returnGen None) freq_accounts.

  Definition gFund_amount env state addr : G Z :=
    (choose (1, Z.min (account_balance env addr) (Z.of_N ((state.(tokenCreationCap) - (total_supply state)) / state.(tokenExchangeRate)))))%Z.

  Definition gCreateTokens (env : Environment) (state : BATCommon.State) : GOpt (Address * Amount * Msg) :=
    let current_slot := S (current_slot (env_chain env)) in
    if (state.(isFinalized)
            || (Nat.ltb current_slot state.(fundingStart))
            || (Nat.ltb state.(fundingEnd) current_slot) (* Funding can only happen in funding period *)
            || (N.ltb (state.(tokenCreationCap) - (total_supply state)) state.(tokenExchangeRate))) (* No funding if cap was hit or if we are too close to it *)
    then
      returnGen None
    else
      from_addr <-- get_fundable_accounts env ;;
      value <- gFund_amount env state from_addr ;;
      returnGenSome (from_addr, value, create_tokens).

  Definition gCreateTokensInvalid (env : Environment) (state : BATCommon.State) : GOpt (Address * Amount * Msg) :=
    from_addr <-- get_fundable_accounts env ;;
    value <- choose (1, account_balance env from_addr)%Z ;;
    returnGenSome (from_addr, value, create_tokens).

  Definition gRefund (env : Environment) (state : BATCommon.State) : GOpt (Address * Msg) :=
    let current_slot := S (current_slot (env_chain env)) in
    let accounts := get_refundable_accounts state in
    if ((state.(isFinalized)
            || (Nat.leb current_slot state.(fundingEnd))
            || (state.(tokenCreationMin) <=? (total_supply state))%N))
    then
      returnGen None
    else
      from_addr <-- oneOf_ (returnGen None) accounts ;;
      returnGenSome (from_addr, refund).

  Definition gRefundInvalid (env : Environment) (state : BATCommon.State) : G (Address * Msg) :=
    from_addr <- gAccount ;;
    returnGen (from_addr, refund).

  Definition gFinalize (env : Environment) (state : BATCommon.State) : GOpt (Address * Msg) :=
    let current_slot := S (current_slot (env_chain env)) in
    if (state.(isFinalized)
          || ((total_supply state) <? state.(tokenCreationMin))%N
          || ((Nat.leb current_slot state.(fundingEnd)) && negb ((total_supply state) =? state.(tokenCreationCap))%N))
    then
      returnGen None
    else
      returnGenSome (fund_addr, finalize).

  Definition gFinalizeInvalid (env : Environment) (state : BATCommon.State) : G (Address * Msg) :=
    from_addr <- gAccount ;;
    returnGen (from_addr, finalize).

  Module EIP20 := EIP20Gens Info.

  Definition gTransfer (env : Environment) (state : BATCommon.State) : GOpt (Address * Msg) :=
    if eip20_transactions_before_finalized || state.(isFinalized)
    then
      '(caller, msg) <- EIP20.gTransfer env (token_state state) ;;
      returnGenSome (caller, tokenMsg msg)
    else
      returnGen None.

  Definition gApprove (state : BATCommon.State) : GOpt (Address * Msg) :=
    if eip20_transactions_before_finalized || state.(isFinalized)
    then
      bindOpt (EIP20.gApprove (token_state state))
          (fun '(caller, msg) => returnGenSome (caller, tokenMsg msg))
    else
      returnGen None.

  Definition gTransfer_from (state : BATCommon.State) : GOpt (Address * Msg) :=
    if eip20_transactions_before_finalized || state.(isFinalized)
    then
      bindOpt (EIP20.gTransfer_from (token_state state))
          (fun '(caller, msg) => returnGenSome (caller, tokenMsg msg))
    else
      returnGen None.

  (* BAT valid call generator.
    Generator that will always return BAToken contract calls that are valid on their own,
    i.e. guaranteed to be valid if it is the first action executed in the block.
  *)
  Definition gBATActionValid (env : Environment) : GOpt Action :=
    let call contract_addr caller_addr value msg :=
      returnGenSome (build_call caller_addr contract_addr value msg) in
    state <-- returnGen (get_contract_state BATCommon.State env contract_addr) ;;
    backtrack [
      (* transfer *)
      (1, bindOpt (gTransfer env state)
          (fun '(caller, msg) =>
            call contract_addr caller (0%Z) msg
          )
      );
      (* transfer_from *)
      (2, bindOpt (gTransfer_from state)
          (fun '(caller, msg) =>
            call contract_addr caller (0%Z) msg
          )
      );
      (* approve *)
      (1, bindOpt (gApprove state)
          (fun '(caller, msg) =>
            call contract_addr caller (0%Z) msg
          )
      );
      (* create_tokens *)
      (5, bindOpt (gCreateTokens env state)
          (fun '(caller, value, msg) =>
            call contract_addr caller value msg
          )
      );
      (* refund *)
      (10, bindOpt (gRefund env state)
          (fun '(caller, msg) =>
            call contract_addr caller (0%Z) msg
          )
      );
      (* finalize *)
      (10, bindOpt (gFinalize env state)
          (fun '(caller, msg) =>
            call contract_addr caller (0%Z) msg
          )
      )
    ].

  (* BAT invalid call generator.
    Generator likely to generate invalid BAToken contract calls.
    It treats the BAToken code mostly as blackbox and only know the expected types of input
      but does not make any assumptions/checks on which values will result in valid or invalid calls
  *)
  Definition gBATActionInvalid (env : Environment) : GOpt Action :=
    let call contract_addr caller_addr value msg :=
      returnGenSome (build_call caller_addr contract_addr value msg) in
    state <-- returnGen (get_contract_state BATCommon.State env contract_addr) ;;
    backtrack [
      (* transfer *)
      (1, '(caller, msg) <- EIP20.gTransfer env (token_state state) ;;
          call contract_addr caller (0%Z) (tokenMsg msg)
      ) ;
      (* transfer_from *)
      (2, bindOpt (EIP20.gTransfer_from (token_state state))
          (fun '(caller, msg) =>
            call contract_addr caller (0%Z) (tokenMsg msg)
          )
      );
      (* approve *)
      (1, bindOpt (EIP20.gApprove (token_state state))
          (fun '(caller, msg) =>
            call contract_addr caller (0%Z) (tokenMsg msg)
          )
      );
      (* create_tokens *)
      (5, bindOpt (gCreateTokensInvalid env state)
          (fun '(caller, value, msg) =>
            call contract_addr caller value msg
          )
      );
      (* refund *)
      (1, '(caller, msg) <- gRefundInvalid env state ;;
          call contract_addr caller (0%Z) msg
      );
      (* finalize *)
      (1, '(caller, msg) <- gFinalizeInvalid env state ;;
          call contract_addr caller (0%Z) msg
      )
    ].

  (* BAT call generator
    Has a 7% chance to attempt to generate an invalid contract call
      More specifically it has:
      - 0.5% chance of generating a valid call and then replacing the amount of money sent with that call.
        For BAT contract this is likely to result in an invalid call as most contract calls on BAToken are
        not allowed to include money in them.
      - 6.5% chance of using the invalid action generator. This generator is likely to generate an invalid call
        since it treats the contract as a black box and thus does not check any of the expected requirements for
        a contract call to be valid.
      The remaining 90% of the time it will generate a call that is guaranteed to be valid (only guaranteed to
      be valid on its own, since the generator cannot know what other calls may be included in the same block and
      which order they will be executed in)
  *)
  Definition gBATAction (env : Environment) : GOpt Action :=
    state <-- returnGen (get_contract_state BATCommon.State env contract_addr) ;;
    freq [
      (5, bindOpt (gBATActionValid env)
          (fun '(action) =>
            match action.(act_body) with
            | act_transfer _ _ => returnGen None
            | act_deploy _ _ _ => returnGen None
            | act_call to _ msg =>
              amount <- choose (0, account_balance env action.(act_from))%Z ;;
              returnGenSome (build_call action.(act_from) to amount msg)
            end
          ));
      (65, gBATActionInvalid env);
      (930, gBATActionValid env)
    ].

  Definition gBATSetup : G Setup :=
    fundingStart <- choose (0, (trace_length - 1)) ;;
    fundingEnd <- choose (0, (trace_length - 1)) ;;
    exchangeRate <- choose (0, Z.to_N accounts_total_balance)%N ;;
    initSupply <- choose (0, Z.to_N accounts_total_balance)%N ;;
    tokenMin <- choose (0, Z.to_N accounts_total_balance)%N ;;
    tokenCap <- choose (0, Z.to_N accounts_total_balance)%N ;;
    returnGen (BATCommon.build_setup initSupply
                              fund_addr
                              bat_addr
                              fundingStart
                              fundingEnd
                              exchangeRate
                              tokenCap
                              tokenMin).

End BATGens.
