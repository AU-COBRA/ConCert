From ConCert Require Import Blockchain LocalBlockchain EIP20Token.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters EIP20TokenPrinters SerializablePrinters.

Require Import ZArith Strings.Ascii Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Require Import Containers.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

Notation "f 'o' g" := (compose f g) (at level 50).

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

Definition serializeMsg := @serialize EIP20Token.Msg _.


Definition lc_token_contracts_states_deserialized (lc : LocalChain) : FMap Address EIP20Token.State :=
  let els_list : list (Address * SerializedValue) := FMap.elements (lc_contract_state lc) in
  FMap.of_list (List.fold_left 
                (fun acc p => 
                  match deserialize EIP20Token.State _ (snd p) with
                  | Some state => (fst p, state) :: acc
                  | None => acc
                  end)  
                els_list []).


(* TODO: for some reason in the 'fresh' case the blockchain execution rejects the transfer - why? Does it only allow existing accounts? *)
(* Will try to generate a transfer between existing accounts in the token contract's state.
	 Otherwise tries to use accounts in the Blockchain state.
	 Has a small chance to transfer between "fresh" accounts. *)
Definition gTransfer (lc : LocalChain) (state : EIP20Token.State) : G (Address * Msg) := 
	let nr_accounts_in_state := FMap.size state.(balances) in
	let weight_1 := 2 * nr_accounts_in_state + 1 in
	let randomize_mk_gen g := (* the probability of sampling fresh accounts grows smaller over time *)
		freq [
			(weight_1, returnGen g) ;
			(0, from_addr <- arbitrary ;; (* TODO: temporarily set to 0 *)
					to_addr <- arbitrary ;;
					returnGen (from_addr, transfer to_addr 0))
		] in
	sample <- sampleFMapOpt state.(balances) ;;
	match sample with
	| Some (addr, balance) =>
		transfer_amount <- choose (0, balance) ;;
		sample' <- sampleFMapOpt lc.(lc_account_balances) ;;
		match sample' with
		| Some (account, _) => randomize_mk_gen (addr, transfer account transfer_amount) 
		| None => to_addr <- arbitrary ;; randomize_mk_gen (addr, transfer to_addr transfer_amount)
		end	
	(* if the contract state contains no accounts, just transfer 0 tokens between two arbitrary accounts *)
	| None => from_addr <- arbitrary ;;
						to_addr <- arbitrary ;;
						returnGen (from_addr, transfer to_addr 0)
	end.


(* Main generator *)
Definition gEIP20TokenAction (lc : LocalChain) (contract_addr : Address) : G (option Action) := 
  let mk_call contract_addr caller_addr msg := 
    amount <- match lc_account_balance lc caller_addr with
              | Some caller_balance => choose (0%Z, caller_balance)
              | None => returnGen 0%Z
              end ;;
    returnGen (Some (build_act caller_addr 
			(eip20token_action_to_chain_action (eip_act_call contract_addr amount (serializeMsg msg))))) in 
	backtrack [
		(* transfer *)
		(1, bindGenOpt (sampleFMapOpt (lc_token_contracts_states_deserialized lc))
				(fun c_state_pair =>
				let contract_addr' := fst c_state_pair in
				let state := snd c_state_pair in
				caller_msg_pair <- gTransfer lc state ;;
				mk_call contract_addr' (fst caller_msg_pair) (snd caller_msg_pair)
				) 		
		) ;
		(* transfer_from *)
		(0, returnGen None) ;
		(* approve *)
		(0, returnGen None)
	].