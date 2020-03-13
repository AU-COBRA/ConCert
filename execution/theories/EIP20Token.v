(* 
	This file contains an implementation of the EIP 20 Token Specification (https://eips.ethereum.org/EIPS/eip-20).
	The implementation is essentially a port of https://github.com/ConsenSys/Tokens/blob/fdf687c69d998266a95f15216b1955a4965a0a6d/contracts/eip20/EIP20.sol

*)

From Coq Require Import ZArith.
From Coq Require Import Morphisms.
From Coq Require Import Psatz.
From Coq Require Import Permutation.
Require Import Monads.
Require Import Extras.
Require Import ChainedList.
Require Import Containers.
Require Import Automation.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.

Import ListNotations.
Import RecordSetNotations.

Section EIP20Token.
Context {BaseTypes : ChainBase}.
(* Local Open Scope Z. *)
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
(* Definition MaxValue : N := 2^8%N. *)
Definition TokenValue := nat.


Inductive EIP20TokenAction :=
	| eip_act_transfer (to : Address) (amount : Amount)
	| eip_act_call (to : Address) (amount : Amount) (msg : SerializedValue).

Inductive Msg := 
	(* | total_supply : Msg *)
	(* | balance_of : Address -> Msg *)

	(* transfer tokens to this address *)
	| transfer : Address -> TokenValue -> Msg
	(* 								from 		   to *)
	| transfer_from : Address -> Address -> TokenValue -> Msg
	| approve : Address -> TokenValue -> Msg.
	(* 						owner			 spender*)
	(* | allowance : Address -> Address -> Msg. *)

Record State :=
	build_state {
		total_supply : TokenValue;
		balances : FMap Address TokenValue;
		allowances : FMap Address (FMap Address TokenValue)
	}.

Record Setup :=
	build_setup {
		owner : Address;
		init_amount : TokenValue;
		
	}.

Instance state_settable : Settable _ :=
  settable! build_state <total_supply; balances; allowances>.
Instance setup_settable : Settable _ :=
  settable! build_setup <owner; init_amount>.


Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance eiptoken20_action_serializable : Serializable EIP20TokenAction :=
  Derive Serializable EIP20TokenAction_rect <eip_act_transfer, eip_act_call>.


Global Instance msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <transfer, transfer_from, approve>.

Global Instance state_serializable : Serializable State :=
	Derive Serializable State_rect <build_state>.
	
End Serialization.

Definition eip20token_action_to_chain_action (act : EIP20TokenAction) : ActionBody :=
  match act with
  | eip_act_transfer to amt => act_transfer to amt
  | eip_act_call to amt msg => act_call to amt msg
  end.

Definition validate_setup (setup : Setup) : bool := 
	0 <=? setup.(init_amount).


Definition init (chain : Chain)
								(ctx : ContractCallContext)
								(setup : Setup) : option State := 
	if validate_setup setup
	then Some 
	{|
		total_supply := setup.(init_amount);
		balances := FMap.add setup.(owner) setup.(init_amount) FMap.empty;
		allowances := FMap.empty;
	|}
	else None.

(* Transfers <amount> tokens, if <from> has enough tokens to transfer *)
Definition try_transfer (from : Address) 
												(to : Address) 
												(amount : TokenValue) 
												(state : State) : option State := 
	(* TODO *)
	match FMap.find from state.(balances) with
	| Some from_balance =>
		if from_balance <? amount 
		then None 
		else 
			let new_balances' := FMap.add from (from_balance - amount) state.(balances) in
			let new_balances := match FMap.find to new_balances' with
													| Some balance => FMap.add to (balance + amount) new_balances'
													| None => FMap.add to amount new_balances'
													end in
			Some (state<|balances := new_balances|>)
	| None => if amount =? 0 
						(* TODO: maybe also check if 'to' has a balance, and if not, make one with value 0. *)
						then Some (state<|balances ::= FMap.add from 0|>)
						else None
	end.

(* The delegate tries to transfer <amount> tokens from <from> to <to>.
	 Succeeds if <from> has indeed allowed the delegate to spend at least <amount> tokens on its behalf.
*)
Local Open Scope bool_scope.
Definition try_transfer_from (delegate : Address)
														 (from : Address)
														 (to : Address)
														 (amount : TokenValue)
														 (state : State) : option State :=
	do from_allowances_map <- FMap.find from state.(allowances) ;
	do delegate_allowance <- FMap.find delegate from_allowances_map ;
	match FMap.find from state.(balances) with
	| Some balance_from =>
		if (delegate_allowance <? amount) || (balance_from <? amount)
		then None
		else let new_allowances := (FMap.add delegate (delegate_allowance - amount) from_allowances_map) in 
				 let new_balances' := FMap.add from (balance_from - amount) state.(balances) in
				 let new_balances := match FMap.find to new_balances' with
														| Some balance => FMap.add to (balance + amount) new_balances'
														| None => FMap.add to amount new_balances'
														end in
					Some (state<|balances := new_balances|><|allowances ::= FMap.add from new_allowances|>)
	| None => if amount =? 0 
						(* TODO: maybe also check if 'to' has a balance, and if not, make one with value 0. *)
						then Some (state<|balances ::= FMap.add from 0|>)
						else None
	end.

(* The caller approves the delegate to transfer up to <amount> tokens on behalf of the caller *)
Definition try_approve (caller : Address) 
											 (delegate : Address)
											 (amount : TokenValue)
											 (state : State) : option State :=
	match FMap.find caller state.(allowances) with
	| Some caller_allowances => 
			Some (state<|allowances ::= FMap.add caller (FMap.add delegate amount caller_allowances) |>)
	| None => 
			Some (state<|allowances ::= FMap.add caller (FMap.add delegate amount FMap.empty) |>)
	end.

Definition receive
           (chain : Chain)
           (ctx : ContractCallContext)
           (state : State)
           (maybe_msg : option Msg)
  : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
	match maybe_msg with
	| Some (transfer to amount) => without_actions (try_transfer sender to amount state)
	| Some (transfer_from from to amount) => without_actions (try_transfer_from sender from to amount state)
	| Some (approve delegate amount) => without_actions (try_approve sender delegate amount state)
	(* Always allow people to donate money for the Congress to spend *)
  | None => Some (state, [])

	end.



Ltac solve_contract_proper :=
  repeat
    match goal with
    | [|- ?x _  = ?x _] => unfold x
    | [|- ?x _ _ = ?x _ _] => unfold x
    | [|- ?x _ _ _ = ?x _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ _ = ?x _ _ _ _ _] => unfold x
    | [|- Some _ = Some _] => f_equal
    | [|- pair _ _ = pair _ _] => f_equal
    | [|- (if ?x then _ else _) = (if ?x then _ else _)] => destruct x
    | [|- match ?x with | _ => _ end = match ?x with | _ => _ end ] => destruct x
    | [H: ChainEquiv _ _ |- _] => rewrite H in *
    | _ => subst; auto
    end.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) init.
Proof. repeat intro; solve_contract_proper. Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive.
Proof. repeat intro; solve_contract_proper. Qed.

Definition contract : Contract Setup Msg State :=
  build_contract init init_proper receive receive_proper.


Close Scope bool_scope.
End EIP20Token.
