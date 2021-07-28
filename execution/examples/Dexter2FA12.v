From Coq Require Import ZArith.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Import ListNotations.
Import RecordSetNotations.

Section LQTFA12.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

(* Dummy implementation of callbacks. *)
Record callback (A : Type) := {
  blob : option A;
}.

Record transfer_param :=
  build_transfer_param{
    from : Address;
    to : Address;
    value : N
}.

Record approve_param :=
  build_approve_param{
    spender : Address;
    value_ : N
}.

Record mintOrBurn_param :=
  build_mintOrBurn_param{
    quantity : Z;
    target : Address
}.

Record getAllowance_param :=
  build_getAllowance_param{
    request : (Address * Address);
    allowance_callbak : callback N
}.

Record getBalance_param :=
  build_getBalance_param{
    owner_ : Address;
    balance_callbak : callback N
}.

Record getTotalSupply_param :=
  build_getTotalSupply_param{
    request_ : unit;
    supply_callbak : callback N
}.

Record State :=
  build_state {
    tokens : FMap Address N;
    allowances : FMap (Address * Address) N;
    admin : Address;
    total_supply : N
}.

Record Setup :=
  build_setup {
    admin_ : Address
}.

(* Any contract that wants to receive callback messages from the FA1.2 liquidity contract
   should have this type as its Msg type. The contract may have other endpoints,
   as composed in the 'other_msg' constructor. *)
Inductive FA12ReceiverMsg {Msg' : Type} `{Serializable Msg'} :=
  | receive_allowance : N ->  FA12ReceiverMsg
  | receive_balance_of : N -> FA12ReceiverMsg
  | receive_total_supply : N -> FA12ReceiverMsg
  | other_msg : Msg' -> FA12ReceiverMsg.

(* Liquidity FA1.2 Endpoints. *)
Inductive Msg :=
  | msg_transfer : transfer_param -> Msg
  | msg_approve : approve_param -> Msg
  | msg_mint_or_burn : mintOrBurn_param -> Msg
  | msg_get_allowance : getAllowance_param -> Msg
  | msg_get_balance : getBalance_param -> Msg
  | msg_get_total_supply : getTotalSupply_param -> Msg.

MetaCoq Run (make_setters transfer_param).
MetaCoq Run (make_setters approve_param).
MetaCoq Run (make_setters mintOrBurn_param).
MetaCoq Run (make_setters getAllowance_param).
MetaCoq Run (make_setters getBalance_param).
MetaCoq Run (make_setters getTotalSupply_param).
MetaCoq Run (make_setters State).
MetaCoq Run (make_setters Setup).

Section Serialization.

Instance callback_serializable {A : Type} `{serA : Serializable A} : Serializable (callback A) :=
Derive Serializable (callback_rect A) <(Build_callback A)>.

Global Instance transfer_param_serializable : Serializable transfer_param :=
  Derive Serializable transfer_param_rect <build_transfer_param>.

Global Instance approve_param_serializable : Serializable approve_param :=
  Derive Serializable approve_param_rect <build_approve_param>.

Global Instance mintOrBurn_param_serializable : Serializable mintOrBurn_param :=
  Derive Serializable mintOrBurn_param_rect <build_mintOrBurn_param>.

Global Instance getAllowance_param_serializable : Serializable getAllowance_param :=
  Derive Serializable getAllowance_param_rect <build_getAllowance_param>.

Global Instance getBalance_param_serializable : Serializable getBalance_param :=
  Derive Serializable getBalance_param_rect <build_getBalance_param>.

Global Instance getTotalSupply_param_serializable : Serializable getTotalSupply_param :=
  Derive Serializable getTotalSupply_param_rect <build_getTotalSupply_param>.

Global Instance FA12ReceiverMsg_serializable {Msg : Type} `{serMsg : Serializable Msg} : Serializable (@FA12ReceiverMsg Msg serMsg) :=
  Derive Serializable (@FA12ReceiverMsg_rect Msg serMsg) <
    (@receive_allowance Msg serMsg),
    (@receive_balance_of Msg serMsg),
    (@receive_total_supply Msg serMsg),
    (@other_msg Msg serMsg)>.

Global Instance msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <msg_transfer,
                                msg_approve,
                                msg_mint_or_burn,
                                msg_get_allowance,
                                msg_get_balance,
                                msg_get_total_supply>.

Global Instance state_serializable : Serializable State :=
  Derive Serializable State_rect <build_state>.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

End Serialization.

Definition returnIf (cond : bool) := if cond then None else Some tt.

(* Transfers <amount> tokens, if <from> has enough tokens to transfer
    and <sender> is allowed to send that much on behalf of <from> *)
Definition try_transfer (sender : Address) (param : transfer_param) (state : State) : option State :=
  let allowances_ := state.(allowances) in
  let tokens_ := state.(tokens) in
  do allowances_ <- (* Update allowances *)
    (if address_eqb sender param.(from)
    then Some allowances_
    else
      let allowance_key := (param.(from), sender) in
      let authorized_value := with_default 0 (FMap.find allowance_key allowances_) in
        do _ <- returnIf (authorized_value <? param.(value)) ; (* NotEnoughAllowance *)
        Some (FMap.add allowance_key (authorized_value - param.(value)) allowances_)
    ) ;
  do tokens_ <- (* Update from balance *)
    (let from_balance := with_default 0 (FMap.find param.(from) tokens_) in
      do _ <- returnIf (from_balance <? param.(value)) ; (* NotEnoughBalance *)
      Some (FMap.add param.(from) (from_balance - param.(value)) tokens_)
    ) ;
  let tokens_ :=
    let to_balance := with_default 0 (FMap.find param.(to) tokens_) in
      FMap.add param.(to) (to_balance + param.(value)) tokens_ in
    Some (state<|tokens := tokens_|>
               <|allowances := allowances_|>).

(* The caller approves the <spender> to transfer up to <amount> tokens on behalf of the <sender> *)
Definition try_approve (sender : Address) (param : approve_param) (state : State) : option State :=
  let allowances_ := state.(allowances) in
  let allowance_key := (sender, param.(spender)) in
  let previous_value := with_default 0 (FMap.find allowance_key allowances_) in
  do _ <- returnIf (andb (0 <? previous_value) (0 <? param.(value_))) ; (* UnsafeAllowanceChange *)
  let allowances_ := FMap.add allowance_key param.(value_) allowances_ in
    Some (state<|allowances := allowances_|>).

(* If <quantitiy> is positive
   then creates <quantity> tokens and gives them to <target> 
   else removes <quantity> tokens from <target>.
   Can only be called by <admin> *)
Definition try_mint_or_burn (sender : Address) (param : mintOrBurn_param) (state : State) : option State :=
  do _ <- returnIf (negb (address_eqb sender state.(admin))) ;
  let tokens_ := state.(tokens) in
  let old_balance := with_default 0 (FMap.find param.(target) tokens_) in
  let new_balance := (Z.of_N old_balance + param.(quantity))%Z in
  do _ <- returnIf (new_balance <? 0)%Z ; (* Cannot burn more than the target's balance. *)
  let tokens_ := FMap.add param.(target) (Z.to_N new_balance) tokens_ in
  let total_supply_ := Z.abs_N (Z.of_N state.(total_supply) + param.(quantity))%Z in
    Some (state<|tokens := tokens_|>
               <|total_supply := total_supply_|>).

(* Get the quantity that <snd request> is allowed to spend on behalf of <fst request> *)
Definition try_get_allowance (sender : Address) (param : getAllowance_param) (state : State) : list ActionBody :=
  let value := with_default 0 (FMap.find param.(request) state.(allowances)) in
    [act_call sender 0 (serialize (receive_allowance value))].

(* Get the quantity of tokens belonging to <owner> *)
Definition try_get_balance (sender : Address) (param : getBalance_param) (state : State) : list ActionBody :=
  let value := with_default 0 (FMap.find param.(owner_) state.(tokens)) in
    [act_call sender 0 (serialize (receive_balance_of value))].

(* Get the total supply of tokens *)
Definition try_get_total_supply (sender : Address) (param : getTotalSupply_param) (state : State) : list ActionBody :=
  let value := state.(total_supply) in
    [act_call sender 0 (serialize (receive_total_supply value))].

Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : option State :=
  Some {|
    tokens := FMap.empty;
    allowances := FMap.empty;
    admin := setup.(admin_);
    total_supply := 0
  |}.

Open Scope Z_scope.
Definition receive (chain : Chain) (ctx : ContractCallContext)
                   (state : State) (maybe_msg : option Msg)
                    : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
  let without_statechange acts := Some (state, acts) in
  if ctx.(ctx_amount) >? 0
  then None (* DontSendTez *)
  else match maybe_msg with
  | Some (msg_transfer param) => without_actions (try_transfer sender param state)
  | Some (msg_approve param) => without_actions (try_approve sender param state)
  | Some (msg_mint_or_burn param) => without_actions (try_mint_or_burn sender param state)
  | Some (msg_get_allowance param) => without_statechange (try_get_allowance sender param state)
  | Some (msg_get_balance param) => without_statechange (try_get_balance sender param state)
  | Some (msg_get_total_supply param) => without_statechange (try_get_total_supply sender param state)
  | None => None (* Transfer actions to this contract are not allowed *)
  end.
Close Scope Z_scope.

End LQTFA12.
