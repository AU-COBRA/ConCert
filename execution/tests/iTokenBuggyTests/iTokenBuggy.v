(*
  This file contains an implementation of core parts of the bZx iToken *BEFORE* the transferFrom bug was fixed:
  https://github.com/bZxNetwork/contractsV2/commit/862d44ae5782263f6d99e32bfc270d58e7c2dd56#diff-660efc38dbeb9cb6ec2c1c7888a75d0e
*)

From Coq Require Import ZArith.
From Coq Require Import Morphisms.
From ConCert Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.

Import ListNotations.
Import RecordSetNotations.

Section iTokenBuggy.
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  Open Scope N_scope.

  Inductive Msg :=
  | transfer_from : Address -> Address -> N -> Msg
  | approve : Address -> N -> Msg
  | mint : N -> Msg
  | burn : N -> Msg.

  Record State :=
    build_state {
      total_supply : N;
      balances : FMap Address N;
      allowances : FMap Address (FMap Address N)
    }.

  Record Setup :=
    build_setup {
      owner : Address;
      init_amount : N;
    }.

  MetaCoq Run (make_setters State).
  MetaCoq Run (make_setters Setup).

  Section Serialization.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <transfer_from, approve, mint, burn>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.

  Definition init (chain : Chain)
       (ctx : ContractCallContext)
       (setup : Setup) : option State :=
    Some {| total_supply := setup.(init_amount);
            balances := FMap.add setup.(owner) setup.(init_amount) FMap.empty;
            allowances := FMap.empty |}.

  (* In this implementation we always let users arbitrarily mint (create) tokens. *)
  Definition try_mint caller amount state : State :=
    let new_balances := FMap.partial_alter (fun balance => Some (with_default 0 balance + amount)) caller in
    state<|total_supply ::= N.add amount|><| balances ::= new_balances|>.

  (* If the caller tries to burn more tokens than they have, fail *)
  Definition try_burn caller burn_amount state : option State :=
    let caller_balance := with_default 0 (FMap.find caller state.(balances)) in
    if caller_balance <? burn_amount
    then None
    else
      let new_balances := FMap.add caller (caller_balance - burn_amount) in
      Some (state<|total_supply := state.(total_supply) - burn_amount|>
                 <|balances ::= new_balances|>).


(* The delegate tries to transfer <amount> tokens from <from> to <to>.
   Succeeds if <from> has indeed allowed the delegate to spend at least <amount> tokens on its behalf. *)
  Local Open Scope bool_scope.
  Definition try_transfer_from_buggy (delegate : Address)
                                     (from : Address)
                                     (to : Address)
                                     (amount : N)
                                     (state : State) : option State :=
    do from_allowances_map <- FMap.find from state.(allowances) ;
    do delegate_allowance <- FMap.find delegate from_allowances_map ;
    let from_balance := with_default 0 (FMap.find from state.(balances)) in
    (* Bug starts here! to_balance is calculated too early! *)
    let to_balance := with_default 0 (FMap.find to state.(balances)) in
    if ((delegate_allowance <? amount) && negb (from =? to)%address) || (from_balance <? amount)
    then None
    else let new_allowances := FMap.add delegate (delegate_allowance - amount) from_allowances_map in
        let new_balances := FMap.add from (from_balance - amount) state.(balances) in
        (* Bug here! new balance of 'to' is calculated from to_balance. The commented line below is the correct implementation. *)
        let new_balances := FMap.add to (to_balance + amount) new_balances in
        (* let new_balances := FMap.partial_alter (fun balance => Some (with_default 0 balance + amount)) to new_balances in *)
        Some (state<|balances := new_balances|><|allowances ::= FMap.add from new_allowances|>).

  (* The caller approves the delegate to transfer up to <amount> tokens on behalf of the caller *)
  Definition try_approve (caller : Address)
       (delegate : Address)
       (amount : N)
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
    (* Only allow calls with no money attached *)
    if ctx.(ctx_amount) >? 0
    then None
    else match maybe_msg with
   | Some (transfer_from from to amount) => without_actions (try_transfer_from_buggy sender from to amount state)
   | Some (approve delegate amount) => without_actions (try_approve sender delegate amount state)
   | Some (mint amount) => without_actions (Some (try_mint sender amount state))
   | Some (burn amount) => without_actions (try_burn sender amount state)
   (* transfer actions to this contract are not allowed *)
         | None => None
   end.
  Close Scope Z_scope.

  Definition contract : Contract Setup Msg State :=
    build_contract init receive.

End iTokenBuggy.
