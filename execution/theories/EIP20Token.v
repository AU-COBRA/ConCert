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
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Definition TokenValue := N.
Open Scope N_scope.

Inductive Msg := 
	| transfer : Address -> TokenValue -> Msg
	| transfer_from : Address -> Address -> TokenValue -> Msg
	| approve : Address -> TokenValue -> Msg.

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

Global Instance msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <transfer, transfer_from, approve>.

Global Instance state_serializable : Serializable State :=
	Derive Serializable State_rect <build_state>.
	
End Serialization.

Definition init (chain : Chain)
								(ctx : ContractCallContext)
								(setup : Setup) : option State := 
	Some {|
		total_supply := setup.(init_amount);
		balances := FMap.add setup.(owner) setup.(init_amount) FMap.empty;
		allowances := FMap.empty;
	|}.

(* Transfers <amount> tokens, if <from> has enough tokens to transfer *)
Definition try_transfer (from : Address) 
												(to : Address) 
												(amount : TokenValue) 
												(state : State) : option State :=
	let from_balance := with_default 0 (FMap.find from state.(balances)) in 
	if from_balance <? amount 
	then None 
	else let new_balances := FMap.add from (from_balance - amount) state.(balances) in
		 let new_balances := FMap.partial_alter (fun balance => Some (with_default 0 balance + amount)) to new_balances in
		 Some (state<|balances := new_balances|>).

(* The delegate tries to transfer <amount> tokens from <from> to <to>.
	 Succeeds if <from> has indeed allowed the delegate to spend at least <amount> tokens on its behalf. *)
Local Open Scope bool_scope.
Definition try_transfer_from (delegate : Address)
														 (from : Address)
														 (to : Address)
														 (amount : TokenValue)
														 (state : State) : option State :=
	do from_allowances_map <- FMap.find from state.(allowances) ;
	do delegate_allowance <- FMap.find delegate from_allowances_map ;
	let from_balance := with_default 0 (FMap.find from state.(balances)) in 
	if (delegate_allowance <? amount) || (from_balance <? amount)
	then None
	else let new_allowances := FMap.add delegate (delegate_allowance - amount) from_allowances_map in 
			 let new_balances := FMap.add from (from_balance - amount) state.(balances) in
			 let new_balances := FMap.partial_alter (fun balance => Some (with_default 0 balance + amount)) to new_balances in
			 Some (state<|balances := new_balances|><|allowances ::= FMap.add from new_allowances|>).

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

Open Scope Z_scope.
Definition receive (chain : Chain)
						 			 (ctx : ContractCallContext)
									 (state : State)
									 (maybe_msg : option Msg)
					         : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
	let without_actions := option_map (fun new_state => (new_state, [])) in
	(* Only allow calls to this contract with no payload *)
	if ctx.(ctx_amount) >? 0
	then None
	else match maybe_msg with
	| Some (transfer to amount) => without_actions (try_transfer sender to amount state)
	| Some (transfer_from from to amount) => without_actions (try_transfer_from sender from to amount state)
	| Some (approve delegate amount) => without_actions (try_approve sender delegate amount state)
	(* transfer actions to this contract are not allowed *)
  | None => None
	end.
Close Scope Z_scope.

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

End EIP20Token.
