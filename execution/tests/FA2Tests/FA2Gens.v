From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface.
From ConCert Require Import Serializable.
From ConCert Require Import LocalBlockchainTests.
(* From Coq Require Import Morphisms. *)
From ConCert Require Import Extras.
From ConCert Require Import Containers.
From ConCert Require Import BoundedN.
Global Set Warnings "-extraction-logical-axiom".

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ConCert.Execution.QCTests Require Import 
	TestUtils ChainPrinters SerializablePrinters TraceGens FA2Printers TestContracts.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import ZArith List.
Import ListNotations.
Import RecordSetNotations.
(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

Module Type FA2TestsInfo.
  Parameter fa2_contract_addr : Address.
  Parameter fa2_client_addr : Address.
  Parameter fa2_hook_addr : Address.
End FA2TestsInfo.

Module FA2Gens (Info : FA2TestsInfo).
Import Info.
Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.
Definition LocalChainBase : ChainBase := TestUtils.LocalChainBase.

Definition returnGenSome {A : Type} (a : A) := returnGen (Some a).

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
  end .

Local Open Scope N_scope.

Definition gTransferCallerFromTo (lc : LocalChain) 
                           (state : FA2Token.State) 
                           (ledger : TokenLedger)
                           (tokenid : token_id) 
                           : G (option (Address * Address * Address)) :=
  let gAccountWithTokens := liftM fst (sampleFMapOpt_filter ledger.(balances) (fun p => 0 <? (snd p))) in
  let policy := state.(permission_policy) in
  let gSelfTransfer :=
    caller <- gAccountWithTokens ;;
    to <- gAddrFromLCWithoutAddrs lc [caller] ;;
    returnGenSome (caller, caller, to) in
  let gOperatorTransfer :=
    (* make sure caller is an operator, with the given tokenid *)
    let op_tokens_contains_tokenid op_tokens := match op_tokens with
                                                | all_tokens => true
                                                | some_tokens tids => existsb (fun tid => N.eqb tid tokenid) tids
                                                end in
    let owner_has_tokens owner := 0 <? (with_default 0 (FMap.find owner ledger.(balances))) in
    let filter_ op_tokens_map := (Nat.ltb 0%nat (FMap.size op_tokens_map)) && 
                                (existsb op_tokens_contains_tokenid (FMap.values op_tokens_map)) in
    p <- sampleFMapOpt_filter state.(operators) (fun p => (owner_has_tokens (fst p)) && (filter_ (snd p))) ;;
    let from := fst p in 
    p' <- sampleFMapOpt_filter (snd p) (fun p => op_tokens_contains_tokenid (snd p)) ;;
    let caller : Address := fst p' in
    to <- gAddrFromLCWithoutAddrs lc [caller; from] ;;
    returnGenSome (fst p, from, to) in
  match (policy.(descr_self), policy.(descr_operator)) with
  | (self_transfer_permitted, operator_transfer_denied) => gSelfTransfer
    (* caller and from must be the same *)
  | (self_transfer_denied, operator_transfer_permitted) => gOperatorTransfer
    (* allows operator transfer, but not self transfer, so caller != from *)
  | (self_transfer_permitted, operator_transfer_permitted) => backtrack [ (1%nat, gSelfTransfer); 
                                                                          (1%nat, gOperatorTransfer)]
  | _ => returnGen None
  end.

Definition gSingleTransfer (lc : LocalChain)
                           (state : FA2Token.State)
                           : G (option (Address * transfer)) :=
  tokenid <- liftM fst (sampleFMapOpt state.(tokens)) ;;
  match FMap.find tokenid state.(assets) with
  | Some ledger =>
    bindGenOpt (gTransferCallerFromTo lc state ledger tokenid)
    (fun pp =>
      let caller := fst (fst pp) in
      let from := snd (fst pp) in
      let to := snd pp in
      let from_balance := with_default 0 (FMap.find from ledger.(balances)) in
      if from_balance =? 0 then
        returnGen None
      else
        amount <- choose (1, from_balance) ;;
        returnGenSome
          (caller, {|
            from_ := from;
            to_ := to;
            transfer_token_id := tokenid;
            amount := amount;
            sender_callback_addr := None;
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
  | (a,b)::xs => let res := groupBy_fix xs in 
                 match FMap.find a res with
                 | Some bs => FMap.add a (b :: bs) res 
                 | None => FMap.add a [b] FMap.empty
                 end
  end.

Fixpoint gTransfersFix (lc : LocalChain)
                     (state : FA2Token.State)
                     (maxNrTransfers : nat)
                     (acc : list (Address * transfer))
                     : G (option (Address * list transfer)) :=
  match maxNrTransfers with
  | 0%nat => match acc with
             | [] => returnGen None
             | _ => 
              (* group transfers by caller *)
              let trx_groups := groupBy_fix acc in
              sampleFMapOpt_filter trx_groups (fun p => Nat.ltb 0%nat (List.length (snd p)))
             end
  | S n => trx <- gSingleTransfer lc state ;;
           gTransfersFix lc state n (trx :: acc)
  end.

Definition gTransfer (lc : LocalChain)
                     (state : FA2Token.State)
                     (maxNrTransfers : nat)
                     : G (option (Address * FA2Token.Msg)) := 
  p <- (gTransfersFix lc state maxNrTransfers []) ;;
  let trxs := snd p in
  returnGenSome (fst p, msg_transfer trxs).


Local Close Scope N_scope.
Local Open Scope Z_scope.
Definition gCreateTokens (lc : LocalChain)
                         (caller : Address)
                         (state : FA2Token.State)
                         : G (option (Z * FA2Token.Msg)) :=
  let balance := with_default 0 (FMap.find caller lc.(lc_account_balances)) in
  bindGenOpt (liftM fst (sampleFMapOpt state.(assets)))
  (fun tokenid =>
    if 0 <? balance then
      nr_tokens <- (choose (1, balance)) ;;
      returnGenSome (nr_tokens, msg_create_tokens tokenid)
    else returnGen None
  ).
Local Close Scope Z_scope.

Definition gOperatorParam (lc : LocalChain)
                          (state : FA2Token.State)
                          : G (option operator_param) :=
  owner <- gAccountAddrFromLocalChain lc ;;
  addr <- gAccountAddrFromLCWithoutAddrs lc [owner] ;;
  tokenid <- liftM fst (sampleFMapOpt state.(tokens)) ;;
  tokens <- (elems [Some all_tokens; Some (some_tokens [tokenid])]) ;;
  returnGenSome {|
    op_param_owner := owner;
    op_param_operator := addr;
    op_param_tokens := tokens;
  |}.

Local Open Scope nat_scope.
Definition gUpdateOperators (lc : LocalChain)
                            (state : FA2Token.State)
                            (maxSize : nat)
                            : G (option FA2Token.Msg) :=
  if maxSize =? 0 then
    returnGen None
  else
    n <- choose (1, maxSize) ;;
    let gUpdateOp : G (option update_operator) :=
      bindGenOpt (gOperatorParam lc state)
      (fun param =>
        op <- elems [add_operator ; remove_operator] ;;
        returnGenSome (op param)
      ) in
    ops <- optToVector n gUpdateOp ;;
    if List.length ops =? 0 then
      returnGen None
    else
      returnGenSome (msg_update_operators ops).
    

Definition gFA2TokenAction (lc : LocalChain) : G (option Action) :=
  let mk_call caller_addr amount msg :=
		returnGenSome {|
			act_from := caller_addr;
			act_body := act_call fa2_contract_addr amount (serialize FA2Token.Msg _ msg) 
    |} in
  match FMap.find fa2_contract_addr (lc_contract_state_deserialized FA2Token.State lc) with
  | Some fa2_state => 
    backtrack [
      (* transfer tokens *)
      (4, p <- gTransfer lc fa2_state 4 ;; 
          let caller := fst p in
          let trx := snd p in
          mk_call caller 0%Z trx
      ) ;
      (* create tokens *)
      (1, let has_balance amount := Z.ltb 0 amount in
          let is_not_contract_addr addr := negb (address_is_contract addr) in
          caller <- liftM fst (sampleFMapOpt_filter lc.(lc_account_balances) 
                              (fun p => (is_not_contract_addr (fst p)) && (has_balance (snd p)))) ;;
          p <- gCreateTokens lc caller fa2_state ;;
          let amount := fst p in
          let msg := snd p in
          mk_call caller amount msg 
      ) ;
      (* update operators *)
      (2, caller <- gAccountAddrFromLocalChain lc ;;
          upd <- gUpdateOperators lc fa2_state 2 ;;
          mk_call caller 0%Z upd
      )
    ]
  | None => returnGen None
  end.

End FA2ContractGens.


(* --------------------- FA2 Client Generators --------------------- *)
(* The generators for this section assume that 'fa2_client_addr' is an address to an fa2 client contract 
  with message type ClientMsg *) 
Section FA2ClientGens.
Let client_other_msg := @other_msg _ FA2ClientMsg _.

Definition gIsOperatorMsg (lc : LocalChain) : G (option ClientMsg) := 
  bindGenOpt (sample2UniqueFMapOpt lc.(lc_account_balances))
  (fun p =>
    let addr1 := fst (fst p) in
    let addr2 := fst (snd p) in
    op_tokens <- elems [all_tokens ; some_tokens [0%N]] ;;
    let params := Build_is_operator_param 
      (Build_operator_param addr1 addr2 op_tokens)
      (Build_callback is_operator_response None) in
    returnGenSome (client_other_msg (Call_fa2_is_operator params))
  ).
    
Definition gClientAction (lc : LocalChain) : G (option Action) :=
  let mk_call_fa2 caller fa2_caddr msg :=
		returnGenSome {|
			act_from := caller;
			act_body := act_call fa2_client_addr 0%Z (serialize ClientMsg _ msg) 
    |} in
  match FMap.find fa2_client_addr (lc_contract_state_deserialized ClientState lc) with
  | Some state =>
    let fa2_caddr := state.(fa2_caddr) in
    backtrack [
      (1, caller <- gAccountAddrFromLocalChain lc ;;
          msg <- gIsOperatorMsg lc ;;
          mk_call_fa2 caller fa2_caddr msg 
      )
    ]
  | None => returnGen None
  end.

End FA2ClientGens.

(* --------------------- FA2 Hook Generators --------------------- *)
Section FA2HookGens.
  
End FA2HookGens.

(* Combine fa2 action generator, client action generator, and hook generator into one generator *)
Definition gFA2Actions (lc : LocalChain) (size : nat) : G (option Action) :=
  backtrack [
    (1, gFA2TokenAction lc);
    (1, gClientAction lc)
  ].

Definition gFA2ChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc gFA2Actions length max_acts_per_block.


(* the '1' fixes nr of actions per block to 1 *)
Definition token_reachableFrom (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc (gFA2ChainTraceList 1) pf.

Definition token_reachableFrom_implies_reachable (lc : LocalChain) pf1 pf2 : Checker := 
  reachableFrom_implies_reachable lc (gFA2ChainTraceList 1) pf1 pf2.

End FA2Gens.

Module DummyTestInfo <: FA2TestsInfo.
  Definition fa2_contract_addr := zero_address.
  Definition fa2_client_addr := zero_address.
  Definition fa2_hook_addr := zero_address.
End DummyTestInfo.
Module MG := FA2Gens.FA2Gens DummyTestInfo. Import MG.