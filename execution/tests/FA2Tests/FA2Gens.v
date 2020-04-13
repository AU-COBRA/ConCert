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
	ChainGens TestUtils ChainPrinters SerializablePrinters TraceGens FA2Printers TestContracts.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import ZArith List.
Import ListNotations.
Import RecordSetNotations.
(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
(* Notation "f 'o' g" := (compose f g) (at level 50). *)

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
Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

Definition returnGenSome {A : Type} (a : A) := returnGen (Some a).

(* --------------------- FA2 Contract Generators --------------------- *)
Section FA2ContractGens.

(* 
  generates a fa2 transfer message, where the following properties hold:
  - 0 < amount <= to_ balance 
  - if operators are allowed, then caller must be a valid operator for this transfer
  - token_id is among existing token_ids of the FA2 Token state.
*)
(* Definition gTransfer : G transfer := 
  from <- arbitrary ;;
  to <- arbitrary ;;
  tokenid <- arbitrary ;;
  amount <- arbitrary ;;
  returnGen {|
    from_ := from;
    to_ := to;
    transfer_token_id := tokenid;
    amount := amount;
  |}.

Local Open Scope N_scope.
Definition valid_transfer_prop state trx :=
  let from_balance := address_balance trx.(transfer_token_id) trx.(from_) state in
  (trx.(amount) <=? from_balance ) && (
    isSome (FMap.find trx.(transfer_token_id) state.(tokens))
  ).
Definition gValidTransfer (state : FA2Token.State) :=
  suchThatMaybe gTransfer (valid_transfer_prop state). *)

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

(* TODO: check specification if transfers between contract addresses are allowed *)
Definition gTransferFrom (lc : LocalChain) 
                         (state : FA2Token.State) 
                         (ledger : TokenLedger)
                         (caller : Address) 
                         : G (option Address) :=
  let policy := state.(permission_policy) in
  if policy_disallows_operator_transfer policy then
    if policy_allows_self_transfer policy then
      (* caller and from must be the same *)
      returnGenSome caller
    else
      returnGen None
  else
    (* allows operator transfer, but not self transfer, so caller != from *)
    from <- (gAddrFromLCWithoutAddrs lc [caller]) ;;
    returnGenSome from
.

Local Open Scope N_scope.
Definition gSingleTransfer (lc : LocalChain)
                           (state : FA2Token.State)
                           (caller : Address)
                           : G (option transfer) :=
  p <- (sampleFMapOpt state.(tokens)) ;;
  let tokenid := fst p in
  match FMap.find tokenid state.(assets) with
  | Some ledger =>
    from <- (gTransferFrom lc state ledger caller) ;;
    bindGenOpt (gAddrFromLCWithoutAddrs lc [from])
    (fun to =>
      let from_balance := with_default 0 (FMap.find from ledger.(balances)) in
      if from_balance =? 0 then
        returnGen None
      else
        amount <- choose (0, from_balance) ;;
        returnGen (
          Some {|
            from_ := from;
            to_ := to;
            transfer_token_id := tokenid;
            amount := amount;
          |})
    )
  | None => returnGen None
  end.

Fixpoint gTransfersFix (lc : LocalChain)
                     (state : FA2Token.State)
                     (caller : Address)
                     (maxNrTransfers : nat)
                     (acc : list transfer)
                     : G (option (list transfer)) :=
  match maxNrTransfers with
  | 0%nat => match acc with
             | [] => returnGen None
             | _ => returnGenSome acc
             end
  | S n => trx <-  (gSingleTransfer lc state caller) ;;
           gTransfersFix lc state caller n (trx :: acc)
  end.

Definition gTransfer (lc : LocalChain)
                     (state : FA2Token.State)
                     (caller : Address)
                     (maxNrTransfers : nat)
                     : G (option FA2Token.Msg) := 
  trxs <- (gTransfersFix lc state caller maxNrTransfers []) ;;
  returnGenSome (msg_transfer trxs).


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

Definition gFA2TokenAction (lc : LocalChain) : G (option Action) :=
  let mk_call caller_addr amount msg :=
		returnGenSome {|
			act_from := caller_addr;
			act_body := act_call fa2_contract_addr amount (serialize FA2Token.Msg _ msg) 
    |} in
  match FMap.find fa2_contract_addr (lc_contract_state_deserialized FA2Token.State lc) with
  | Some fa2_state => 
    backtrack [
      (4, caller <- gAddrFromLCWithoutAddrs lc [] ;;
          trx <- gTransfer lc fa2_state caller 1 ;; 
          mk_call caller 0%Z trx
      ) ;
      (1, caller <- liftM fst (gAccountBalanceFromLocalChain lc) ;;
          p <- gCreateTokens lc caller fa2_state ;;
          let amount := fst p in
          let msg := snd p in
          mk_call caller amount msg 
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
  let mk_call_fa2 fa2_caddr msg :=
		returnGenSome {|
			act_from := fa2_client_addr;
			act_body := act_call fa2_caddr 0%Z (serialize ClientMsg _ msg) 
    |} in
  match FMap.find fa2_client_addr (lc_contract_state_deserialized ClientState lc) with
  | Some state =>
    let fa2_caddr := state.(fa2_caddr) in
    backtrack [
      (1, msg <- gIsOperatorMsg lc ;;
          mk_call_fa2 fa2_caddr msg 
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