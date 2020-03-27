From Coq Require Import ZArith.
(* From Coq Require Import Morphisms. *)
Require Import Monads.
Require Import Extras.
Require Import Containers.
(* Require Import Automation. *)
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Import ListNotations.
Import RecordSetNotations.

Section FA2Token.
Context {BaseTypes : ChainBase}.
Require Import FA2Interface. 
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Inductive Msg := 
  | msg_transfer : list transfer -> Msg
  | msg_balance_of : balance_of_param -> Msg
  | msg_total_supply : total_supply_param -> Msg
  | msg_token_metadata : token_metadata_param -> Msg
  | msg_permissions_descriptor : permissions_descriptor -> Msg (* TODO fix callback type *)
  | msg_update_operators : list update_operator -> Msg
  | msg_is_operator : is_operator_param -> Msg.

Record TokenLedger := 
  build_token_ledger {
    fungible : bool;
    balances : FMap Address N
}.

Record State :=
  build_state {
    assets: FMap token_id TokenLedger 
  }.

Record Setup :=
  build_setup {
    setup_total_supply : list (token_id * N);
  }.

Instance token_ledger_settable : Settable _ :=
  settable! build_token_ledger <fungible; balances>.
Instance state_settable : Settable _ :=
  settable! build_state <assets>.
Instance setup_settable : Settable _ :=
  settable! build_setup <setup_total_supply>.

Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <msg_transfer, msg_balance_of, msg_total_supply, msg_token_metadata, msg_permissions_descriptor, msg_update_operators, msg_is_operator>.

Global Instance TokenLedger_serializable : Serializable TokenLedger :=
  Derive Serializable TokenLedger_rect <build_token_ledger>.

Global Instance state_serializable : Serializable State :=
	Derive Serializable State_rect <build_state>.
	
End Serialization.

Definition returnIf (cond : bool) := if cond then None else Some tt.

Definition address_has_sufficient_asset_balance (token_id : token_id) 
                                                (owner : Address) 
                                                (transaction_amount : N) 
                                                (state : State) 
                                                : option unit :=
  do ledger <- FMap.find token_id state.(assets) ;
  do owner_balance <- FMap.find owner ledger.(balances) ;
  if transaction_amount <=? owner_balance
  then Some tt
  else None. 

(* TODO: dummy implementation for now - only owner has permission to transfer token*)
Definition address_has_transfer_permission (caller owner : Address) : option unit := 
  if address_eqb caller owner then Some tt else None.


Definition address_balance (token_id : token_id)
                           (addr : Address)
                           (state : State) : option N := 
  do ledger <- FMap.find token_id state.(assets) ;
  FMap.find addr ledger.(balances).

Definition try_transfer (caller : Address)
                        (params : transfer)
                        (state : State)
                        : option TokenLedger :=
  (* do _ <- address_has_sufficient_asset_balance transfer_params.(transfer_token_id) transfer_params.(from_) transfer_params.(amount) ; *)
  do _ <- address_has_transfer_permission caller params.(from_) ;
  do ledger <- FMap.find params.(transfer_token_id) state.(assets) ;
  do current_owner_balance <- address_balance params.(transfer_token_id) params.(from_) state ;
  let new_balances : FMap Address N := FMap.add params.(from_) (current_owner_balance - params.(amount)) ledger.(balances) in
  let new_balances : FMap Address N := FMap.partial_alter (fun balance => Some ((with_default 0 balance) + params.(amount))) params.(to_) new_balances in
  Some (ledger<|balances := new_balances|>).
  
End FA2Token.