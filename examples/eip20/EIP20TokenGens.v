From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.EIP20 Require Import EIP20Token.
Import MonadNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.

Module Type EIP20GensInfo.
  Parameter contract_addr : Address.
  Parameter gAccount : G Address.
End EIP20GensInfo.

Module EIP20Gens (Info : EIP20GensInfo).
  Import Info.
  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.

  Definition serializeMsg := @serialize EIP20Token.Msg _.

  (* This function tries to generate a transfer between existing accounts in the token contract's state.
    Otherwise, tries to use accounts in the Blockchain state.
    Has a small chance to transfer between "fresh" accounts. *)
  Definition gTransfer (env : Environment)
                       (state : EIP20Token.State)
                       : G (Address * Msg) :=
    let nr_accounts_in_state := FMap.size state.(balances) in
    let weight_1 := 2 * nr_accounts_in_state + 1 in
    let randomize_mk_gen g := (* the probability of sampling fresh accounts grows smaller over time *)
      freq [
        (weight_1, returnGen g) ;
        (0, from_addr <- arbitrary ;;
            to_addr <- arbitrary ;;
            returnGen (from_addr, transfer to_addr 0%N))
      ] in
    sample <- sampleFMapOpt state.(balances) ;;
    match sample with
    | Some (addr, balance) =>
      transfer_amount <- choose (0%N, balance) ;;
      account <- gAccount ;;
      randomize_mk_gen (addr, transfer account transfer_amount)
    (* if the contract state contains no accounts, just transfer 0 tokens between two arbitrary accounts *)
    | None => from_addr <- arbitrary ;;
              to_addr <- arbitrary ;;
              returnGen (from_addr, transfer to_addr 0%N)
    end.
  Local Open Scope N_scope.

  (* Note: not optimal implementation. Should filter on balances map instead of first sampling and then filtering *)
  Definition gApprove (state : EIP20Token.State) : GOpt (Address * Msg) :=
    bindOpt (sample2UniqueFMapOpt state.(balances)) (fun p =>
      let addr1 := fst (fst p) in
      let balance1 := snd (fst p) in
      let addr2 := fst (snd p) in
      let balance2 := snd (snd p) in
      if 0 <? balance1
      then amount <- choose (0, balance1) ;; returnGenSome (addr1, approve addr2 amount)
      else if 0 <? balance2
      then amount <- choose (0, balance2) ;; returnGenSome (addr2, approve addr1 amount)
      else returnGen None
    ).

  Definition gTransfer_from (state : EIP20Token.State) : GOpt (Address * Msg) :=
    bindOpt (sampleFMapOpt state.(allowances)) (fun '(allower, allowance_map) =>
    bindOpt (sampleFMapOpt allowance_map) (fun '(delegate, allowance) =>
      bindOpt (sampleFMapOpt state.(balances)) (fun '(receiver, _) =>
        let allower_balance := (FMap_find_ allower state.(balances) 0) in
        amount <- (if allower_balance =? 0
                  then returnGen 0
                  else choose (0, N.min allowance allower_balance)) ;;
        returnGenSome (delegate, transfer_from allower receiver amount)
      )
    )).

  Local Close Scope N_scope.
  (* Main generator. *)
  Definition gEIP20TokenAction (env : Environment) : GOpt Action :=
    let call contract_addr caller_addr msg :=
        returnGenSome {|
            act_origin := caller_addr;
            act_from := caller_addr;
            act_body := act_call contract_addr 0%Z (serializeMsg msg)
          |} in
    state <-- returnGen (get_contract_state EIP20Token.State env contract_addr) ;;
    backtrack [
      (* transfer *)
        (2, '(caller, msg) <- gTransfer env state ;;
            call contract_addr caller msg
      ) ;
      (* transfer_from *)
      (3, bindOpt (gTransfer_from state)
          (fun '(caller, msg) =>
            call contract_addr caller msg

          )
      );
      (* approve *)
      (2, bindOpt (gApprove state)
          (fun '(caller, msg) =>
            call contract_addr caller msg
          )
      )
    ].

End EIP20Gens.
