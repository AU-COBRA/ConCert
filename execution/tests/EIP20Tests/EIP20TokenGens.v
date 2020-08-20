From ConCert Require Import Blockchain LocalBlockchain EIP20Token.
From ConCert Require Import Serializable.
From ConCert.Execution.QCTests Require Import TestUtils ChainPrinters EIP20TokenPrinters SerializablePrinters.

Require Import ZArith Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
Require Import Containers.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

Definition LocalChainBase : ChainBase := TestUtils.LocalChainBase.
Definition serializeMsg := @serialize EIP20Token.Msg _.

Definition lc_token_contracts_states_deserialized (lc : LocalChain) : FMap Address EIP20Token.State :=
  let els_list : list (Address * SerializedValue) := FMap.elements (lc_contract_state lc) in
  FMap.of_list (List.fold_left
                (fun acc '(addr, ser_val) =>
                  match deserialize EIP20Token.State _ ser_val with
                  | Some state => (addr, state) :: acc
                  | None => acc
                  end)
                els_list []).

(* This function tries to generate a transfer between existing accounts in the token contract's state.
   Otherwise tries to use accounts in the Blockchain state.
   Has a small chance to transfer between "fresh" accounts. *)
Definition gTransfer (lc : LocalChain) (state : EIP20Token.State) : G (Address * Msg) :=
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
    account_opt <- gAccountAddrFromLocalChain lc ;; (* ensures no contract addresses are generated *)
    match account_opt with
    | Some account => randomize_mk_gen (addr, transfer account transfer_amount)
    | None => to_addr <- arbitrary ;; randomize_mk_gen (addr, transfer to_addr transfer_amount)
    end
  (* if the contract state contains no accounts, just transfer 0 tokens between two arbitrary accounts *)
  | None => from_addr <- arbitrary ;;
            to_addr <- arbitrary ;;
            returnGen (from_addr, transfer to_addr 0%N)
  end.
Local Open Scope N_scope.

(* Note: not optimal implementation. Should filter on balances map instead of first sampling and then filtering *)
Definition gApprove (state : EIP20Token.State) : G (option (Address * Msg)) :=
  bindGenOpt (sample2UniqueFMapOpt state.(balances)) (fun p =>
    let addr1 := fst (fst p) in
    let balance1 := snd (fst p) in
    let addr2 := fst (snd p) in
    let balance2 := snd (snd p) in
    if 0 <? balance1
    then amount <- choose (0, balance1) ;; returnGen (Some (addr1, approve addr2 amount))
    else if 0 <? balance2
    then amount <- choose (0, balance2) ;; returnGen (Some (addr2, approve addr1 amount))
    else returnGen None
  ).

Definition gTransfer_from (state : EIP20Token.State) : G (option (Address * Msg)) :=
  bindGenOpt (sampleFMapOpt state.(allowances)) (fun '(allower, allowance_map) =>
  bindGenOpt (sampleFMapOpt allowance_map) (fun '(delegate, allowance) =>
    bindGenOpt (sampleFMapOpt state.(balances)) (fun '(receiver, _) =>
      let allower_balance := (FMap_find_ allower state.(balances) 0) in
      amount <- (if allower_balance =? 0
                then returnGen 0
                else choose (0, N.min allowance allower_balance)) ;;
      returnGen (Some (delegate, transfer_from allower receiver  amount))
    )
  )).

Local Close Scope N_scope.
(* Main generator. *)
Definition gEIP20TokenAction (lc : LocalChain) (contract_addr : Address) : G (option Action) :=
  let mk_call contract_addr caller_addr msg :=
    returnGen (Some {|
      act_from := caller_addr;
      act_body := act_call contract_addr 0%Z (serializeMsg msg)
    |}) in
  backtrack [
    (* transfer *)
    (1, bindGenOpt (sampleFMapOpt (lc_token_contracts_states_deserialized lc))
        (fun '(contract_addr', state) =>
        '(caller, msg) <- gTransfer lc state ;;
        mk_call contract_addr' caller msg
        )
    ) ;
    (* transfer_from *)
    (2, bindGenOpt (sampleFMapOpt (lc_token_contracts_states_deserialized lc))
        (fun '(contract_addr', state) =>
        bindGenOpt (gTransfer_from state)
        (fun '(caller, msg) =>
        mk_call contract_addr' caller msg
        ))
    );
    (* approve *)
    (1, bindGenOpt (sampleFMapOpt (lc_token_contracts_states_deserialized lc))
        (fun '(contract_addr', state) =>
        bindGenOpt (gApprove state)
        (fun '(caller, msg) =>
        mk_call contract_addr' caller msg
        ))
    )
  ].
