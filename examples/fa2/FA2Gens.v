From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2LegacyInterface.
From ConCert.Examples.FA2 Require Import FA2Printers.
From ConCert.Examples.FA2 Require Import TestContracts.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Import MonadNotation.

Module Type FA2TestsInfo.
  Parameter fa2_contract_addr : Address.
  Parameter fa2_client_addr : Address.
  Parameter fa2_hook_addr : Address.
  Parameter accounts : list Address.
End FA2TestsInfo.

Module FA2Gens (Info : FA2TestsInfo).
  Import Info.
  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.

  (* --------------------- FA2 Contract Generators --------------------- *)
  Section FA2ContractGens.

    Definition policy_allows_operator_transfer (policy : permissions_descriptor) : bool :=
      match policy.(descr_operator) with
      | operator_transfer_permitted => true
      | operator_transfer_denied => false
      end.

    Definition policy_allows_self_transfer (policy : permissions_descriptor) : bool :=
      match policy.(descr_self) with
      | self_transfer_permitted => true
      | self_transfer_denied => false
      end.

    Local Open Scope N_scope.
    Definition gTransferCallerFromTo (state : FA2Token.State)
                                     (ledger : TokenLedger)
                                     (tokenid : token_id)
                                     : GOpt (Address * Address * Address) := 
      let gAccountWithTokens := liftOpt fst (sampleFMapOpt_filter ledger.(balances) (fun p => 0 <? (snd p))) in
      let policy := state.(permission_policy) in
      let gSelfTransfer :=
        caller <-- gAccountWithTokens ;;
        to <- gAddrWithout [caller] accounts ;;
        returnGenSome (caller, caller, to) in
      let gOperatorTransfer :=
        (* make sure caller is an operator, with the given tokenid *)
        let op_tokens_contains_tokenid op_tokens :=
          match op_tokens with
          | all_tokens => true
          | some_tokens tids => existsb (fun tid => N.eqb tid tokenid) tids
          end in
        let owner_has_tokens owner := 0 <? (with_default 0 (FMap.find owner ledger.(balances))) in
        let filter_ op_tokens_map := (Nat.ltb 0%nat (FMap.size op_tokens_map)) &&
                                    (existsb op_tokens_contains_tokenid (FMap.values op_tokens_map)) in
        '(from, ops_map) <-- sampleFMapOpt_filter state.(operators) (fun p => (owner_has_tokens (fst p)) && (filter_ (snd p))) ;;
        '(caller, _) <-- sampleFMapOpt_filter ops_map (fun p => op_tokens_contains_tokenid (snd p)) ;;
        to <- gAddrWithout [caller; from] accounts ;;
        returnGenSome (from, from, to) in
      match (policy.(descr_self), policy.(descr_operator)) with
      | (self_transfer_permitted, operator_transfer_denied) => gSelfTransfer
        (* caller and from must be the same *)
      | (self_transfer_denied, operator_transfer_permitted) => gOperatorTransfer
        (* allows operator transfer, but not self transfer, so caller != from *)
      | (self_transfer_permitted, operator_transfer_permitted) => backtrack [ (1%nat, gSelfTransfer);
                                                                              (1%nat, gOperatorTransfer)]
      | _ => returnGen None
      end.

    Definition gSingleTransfer (state : FA2Token.State)
                               : GOpt (Address * transfer) :=
      tokenid <-- liftOpt fst (sampleFMapOpt state.(tokens)) ;;
      match FMap.find tokenid state.(assets) with
      | Some ledger =>
        bindOpt (gTransferCallerFromTo state ledger tokenid)
        (fun '(caller, from, to) =>
          let from_balance := with_default 0 (FMap.find from ledger.(balances)) in
          if from_balance =? 0 then
            returnGen None
          else
            amount <- choose (1, from_balance) ;;
            returnGenSome
              (caller, {|
                from_ := from;
                txs := [{|
                  to_ := to;
                  dst_token_id := tokenid;
                  amount := amount;
                |}];
                sender_callback_addr := None
              |})
        )
      | None => returnGen None
      end.

    Fixpoint groupBy_fix {A B : Type}
                        `{countable.Countable A}
                        `{base.EqDecision A}
                         (l : list (A * B))
                         : FMap A (list B) :=
      match l with
      | [] => FMap.empty
      | (a,b) ::xs => let res := groupBy_fix xs in
                    match FMap.find a res with
                    | Some bs => FMap.add a (b :: bs) res
                    | None => FMap.add a [b] FMap.empty
                    end
      end.

    Fixpoint gTransfersFix (state : FA2Token.State)
                           (maxNrTransfers : nat)
                           (acc : list (Address * transfer))
                           : GOpt (Address * list transfer) :=
      match maxNrTransfers with
      | 0%nat => match acc with
                | [] => returnGen None
                | _ =>
                  (* group transfers by caller *)
                  let trx_groups := groupBy_fix acc in
                  sampleFMapOpt_filter trx_groups (fun p => Nat.ltb 0%nat (List.length (snd p)))
                end
      | S n => trx <-- gSingleTransfer state ;;
              gTransfersFix state n (trx :: acc)
      end.

    Definition gTransfer (state : FA2Token.State)
                         (maxNrTransfers : nat)
                         : GOpt (Address * FA2Token.Msg) :=
      '(caller,trxs) <-- (gTransfersFix state maxNrTransfers []) ;;
      returnGenSome (caller, msg_transfer trxs).


    Local Close Scope N_scope.
    Local Open Scope Z_scope.
    Definition gCreateTokens (env : Environment)
                             (caller : Address)
                             (state : FA2Token.State)
                             : GOpt (Z * FA2Token.Msg) :=
      let balance := env.(env_account_balances) caller in
      bindOpt (liftOpt fst (sampleFMapOpt state.(assets)))
      (fun tokenid =>
        if 0 <? balance then
          nr_tokens <- (choose (1, balance)) ;;
          returnGenSome (nr_tokens, msg_create_tokens tokenid)
        else returnGen None
      ).
    Local Close Scope Z_scope.

    Definition gOperatorParam (chain : Chain)
                              (state : FA2Token.State)
                              : GOpt operator_param :=
      owner <- gAddress accounts ;;
      addr <- gAddrWithout [owner] accounts ;;
      tokenid <-- liftOpt fst (sampleFMapOpt state.(tokens)) ;;
      tokens <-- (elems [Some all_tokens; Some (some_tokens [tokenid])]) ;;
      returnGenSome {|
        op_param_owner := owner;
        op_param_operator := addr;
        op_param_tokens := tokens;
      |}.

    Local Open Scope nat_scope.
    Definition gUpdateOperators (chain : Chain)
                                (state : FA2Token.State)
                                (maxSize : nat)
                                : GOpt FA2Token.Msg :=
      if maxSize =? 0 then
        returnGen None
      else
        n <- choose (1, maxSize) ;;
        let gUpdateOp : GOpt update_operator :=
          bindOpt (gOperatorParam chain state)
          (fun param =>
            op <- elems [add_operator ; remove_operator] ;;
            returnGenSome (op param)
          ) in
        ops <- optToVector n gUpdateOp ;;
        if List.length ops =? 0 then
          returnGen None
        else
          returnGenSome (msg_update_operators ops).


    Definition gFA2TokenAction (env : Environment) : GOpt Action :=
      let mk_call caller_addr amount msg :=
          returnGenSome {|
              act_origin := caller_addr;
              act_from := caller_addr;
              act_body := act_call fa2_contract_addr amount (serialize FA2Token.Msg _ msg)
        |} in
      fa2_state <-- returnGen (get_contract_state FA2Token.State env fa2_contract_addr) ;;
      backtrack [
        (* transfer tokens *)
        (4, '(caller, trx) <-- gTransfer fa2_state 4 ;;
            mk_call caller 0%Z trx
        ) ;
        (* create tokens *)
        (1, let has_balance amount := Z.ltb 0 amount in
            let is_not_contract_addr addr := address_not_contract addr in
            caller <- gAddress accounts ;;
            (* caller <- liftM fst (sampleFMapOpt_filter lc.(lc_account_balances)
                                (fun p => (is_not_contract_addr (fst p)) && (has_balance (snd p)))) ;; *)
            '(amount, msg) <-- gCreateTokens env caller fa2_state ;;
            mk_call caller amount msg
        ) ;
        (* update operators *)
        (2, caller <- gAddress accounts ;;
            upd <-- gUpdateOperators env fa2_state 2 ;;
            mk_call caller 0%Z upd
        )
      ].
  End FA2ContractGens.


  (* --------------------- FA2 Client Generators --------------------- *)
  (* The generators for this section assume that 'fa2_client_addr' is an address to a fa2 client contract
    with message type ClientMsg *)
  Section FA2ClientGens.
    Let client_other_msg := @other_msg _ FA2ClientMsg.

    Definition gIsOperatorMsg : GOpt ClientMsg :=
    '(addr1, addr2) <-- gUniqueAddrPair accounts ;;
      op_tokens <-- elems_opt [all_tokens ; some_tokens [0%N]] ;;
      let params := Build_is_operator_param
          (Build_operator_param addr1 addr2 op_tokens)
          (Build_callback is_operator_response None fa2_client_addr) in
        returnGenSome (client_other_msg (Call_fa2_is_operator params)).

    Definition gClientAction (env : Environment) : GOpt Action :=
      let mk_call_fa2 caller fa2_caddr msg :=
          returnGenSome {|
              act_origin := caller;
              act_from := caller;
              act_body := act_call fa2_client_addr 0%Z (serialize ClientMsg _ msg)
            |} in
      state <-- returnGen (get_contract_state ClientState env fa2_client_addr) ;;
      let fa2_caddr := state.(fa2_caddr) in
      caller <- gAddress accounts ;;
      msg <-- gIsOperatorMsg ;;
      mk_call_fa2 caller fa2_caddr msg.

  End FA2ClientGens.

  (* Combine fa2 action generator, client action generator, and hook generator into one generator *)
  Definition gFA2Actions (env : Environment)
                         (size : nat)
                         : GOpt Action :=
    backtrack [
      (2, gFA2TokenAction env);
      (1, gClientAction env)
    ].

  Definition gFA2ChainTraceList max_acts_per_block cb length :=
    let max_act_depth := 1 in
    gChain cb gFA2Actions length 1 max_acts_per_block.

  (* the '1' fixes the number of actions per block to 1 *)
  Definition token_reachableFrom (cb : ChainBuilder) pf : Checker :=
    reachableFrom_chaintrace cb (gFA2ChainTraceList 1) pf.

  Definition token_reachableFrom_implies_reachable {A}
                                                   (size : nat)
                                                   (cb : ChainBuilder)
                                                   (pf1 : ChainState -> option A)
                                                   pf2
                                                   : Checker :=
    reachableFrom_implies_chaintracePropSized size cb (gFA2ChainTraceList 1) pf1 pf2.

End FA2Gens.
