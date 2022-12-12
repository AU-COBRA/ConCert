
[@inline] let addInt (i : int) (j : int) = i + j
[@inline] let subInt (i : int) (j : int) = i - j
[@inline] let subIntTruncated (a : int) (b : int) = let res = a - b in if res < 0 then 0 else res
[@inline] let multInt (i : int) (j : int) = i * j
[@inline] let divInt (i : int) (j : int) = i / j
[@inline] let modInt (a : int)(b : int) : int = int (a mod b)
[@inline] let leInt (i : int) (j : int) = i <= j
[@inline] let ltInt (i : int) (j : int) = i < j
[@inline] let eqInt (i : int) (j : int) = i = j

[@inline] let addTez (n : tez) (m : tez) = n + m
[@inline] let subTez (n : tez) (m : tez) = n - m
[@inline] let leTez (a : tez ) (b : tez ) = a <= b
[@inline] let ltTez (a : tez ) (b : tez ) =  a < b
[@inline] let gtbTez (a : tez ) (b : tez ) =  a > b
[@inline] let eqTez (a : tez ) (b : tez ) = a = b
[@inline] let natural_to_mutez (a: nat): tez = a * 1mutez
[@inline] let divTez (a : tez) (b : tez) : tez = natural_to_mutez (a/b)
[@inline] let multTez (n : tez) (m : tez) = (n/1tez) * m
[@inline] let evenTez (i : tez) = (i mod 2n) = 0tez

[@inline] let addN (a : nat ) (b : nat ) = a + b
[@inline] let multN (a : nat ) (b : nat ) = a * b
[@inline] let modN (a : nat ) (b : nat ) = a mod b
[@inline] let divN (a : nat ) (b : nat ) = a / b
[@inline] let eqN (a : nat ) (b : nat ) = a = b
[@inline] let lebN (a : nat ) (b : nat ) = a <= b
[@inline] let ltbN (a : nat ) (b : nat ) = a < b
let divN_opt (n : nat) (m : nat) : nat option = match ediv n m with | Some (q,_) -> Some q | None -> None
let moduloN (n : nat) (m : nat) : nat = match ediv n m with | Some (_,r) -> r | None -> 0n
let subOption (n : nat) (m : nat) : nat option = if n < m then None else Some (abs (n-m))
let z_to_N (i : int) : nat = if i < 0 then 0n else abs i
let z_of_N (n : nat) : int = int (n)

[@inline] let andb (a : bool ) (b : bool ) = a && b
[@inline] let orb (a : bool ) (b : bool ) = a || b

[@inline] let eqb_time (a1 : timestamp) (a2 : timestamp) = a1 = a2
[@inline] let leb_time (a1 : timestamp) (a2 : timestamp) = a1 <= a2
[@inline] let ltb_time (a1 : timestamp) (a2 : timestamp) = a1 < a2

[@inline] let eq_addr (a1 : address) (a2 : address) = a1 = a2

let get_contract_unit (a : address) : unit contract  =
  match (Tezos.get_contract_opt a : unit contract option) with
    Some c -> c
  | None -> (failwith ("Contract not found.") : unit contract)

(* ConCert's call context *)
type cctx = {
  ctx_origin_ : address;
  ctx_from_ : address;
  ctx_contract_address_ : address;
  ctx_contract_balance_ : tez;
  ctx_amount_ : tez
}
(* a call context instance with fields filled in with required data *)
let cctx_instance : cctx= 
{ ctx_origin_ = Tezos.source;
  ctx_from_ = Tezos.sender;
  ctx_contract_address_ = Tezos.self_address;
  ctx_contract_balance_ = Tezos.balance;
  ctx_amount_ = Tezos.amount
}

(* context projections as functions *)
let ctx_from (c : cctx) = c.ctx_from_
let ctx_origin (c : cctx) = c.ctx_origin_
let ctx_contract_address (c : cctx) = c.ctx_contract_address_
let ctx_contract_balance (c : cctx) = c.ctx_contract_balance_
let ctx_amount (c : cctx) = c.ctx_amount_
type chain = {
  chain_height_     : nat;
  current_slot_     : nat;
  finalized_height_ : nat;
}

let dummy_chain : chain = {
chain_height_     = Tezos.level;
current_slot_     = Tezos.level;
finalized_height_ = Tezos.level;
}

(* chain projections as functions *)
let chain_height (c : chain ) = c.chain_height_
let current_slot (c : chain ) = c.current_slot_
let finalized_height (c : chain) = c.finalized_height_

let call_to_token (type msg) (addr : address) (amt : nat) (msg : msg) : operation =
  let token_ : msg contract =
  match (Tezos.get_contract_opt (addr) : msg contract option) with
    Some contract -> contract
  | None -> (failwith "Contract not found." : msg contract) in
  Tezos.transaction msg (natural_to_mutez amt) token_

[@inline] let mk_callback (type msg)(addr : address) (msg : msg) : operation = call_to_token addr 0n msg

[@inline] let natural_to_mutez (a: nat): tez = a * 1mutez

[@inline] let mutez_to_natural (a: tez): nat = a / 1mutez

let xtz_transfer (to_ : address) (amount_ : nat) : operation option =
  match (Tezos.get_contract_opt to_ : unit contract option) with
    | None -> None
    | Some c -> Some (Tezos.transaction () (natural_to_mutez amount_) c)

let subNTruncated (n : nat) (m : nat) : nat = if n < m then 0n else abs (n-m)

type dexter2FA12_Setup = 
  Dext_build_setup of (address * address * nat)


type dexter2FA12_State = 
  Dext_build_state of ( (address, nat) map *  ((address * address), nat) map * address * nat)


type dexter2FA12_transfer_param = 
  Dext_build_transfer_param of (address * address * nat)


type dexter2FA12_approve_param = 
  Dext_build_approve_param of (address * nat)


type dexter2FA12_mintOrBurn_param = 
  Dext_build_mintOrBurn_param of (int * address)


type dexter2FA12_callback = 
  Dext_Build_callback of address


type dexter2FA12_getAllowance_param = 
  Dext_build_getAllowance_param of ((address * address) * dexter2FA12_callback)


type dexter2FA12_getBalance_param = 
  Dext_build_getBalance_param of (address * dexter2FA12_callback)


type dexter2FA12_getTotalSupply_param = 
  Dext_build_getTotalSupply_param of (unit * dexter2FA12_callback)


type dexter2FA12_Msg = 
  Dext_msg_transfer of dexter2FA12_transfer_param
| Dext_msg_approve of dexter2FA12_approve_param
| Dext_msg_mint_or_burn of dexter2FA12_mintOrBurn_param
| Dext_msg_get_allowance of dexter2FA12_getAllowance_param
| Dext_msg_get_balance of dexter2FA12_getBalance_param
| Dext_msg_get_total_supply of dexter2FA12_getTotalSupply_param


type 'a0 dexter2FA12_FA12ReceiverMsg = 
  Dext_receive_allowance of nat
| Dext_receive_balance_of of nat
| Dext_receive_total_supply of nat
| Dext_other_msg of 'a0


let lqt_provider(s : dexter2FA12_Setup) : address = match s with 
Dext_build_setup (admin_, lqt_provider, initial_pool) -> lqt_provider

let initial_pool(s : dexter2FA12_Setup) : nat = match s with 
Dext_build_setup (admin_, lqt_provider, initial_pool) -> initial_pool

let admin_(s : dexter2FA12_Setup) : address = match s with 
Dext_build_setup (admin_, lqt_provider, initial_pool) -> admin_

let throwIf(cond : bool) :  (unit) option = if cond then (None: (unit) option) else Some (())

let allowances(s : dexter2FA12_State) :  ((address * address), nat) map = match s with 
Dext_build_state (tokens, allowances, admin, total_supply) -> allowances

let tokens(s : dexter2FA12_State) :  (address, nat) map = match s with 
Dext_build_state (tokens, allowances, admin, total_supply) -> tokens

let from(t : dexter2FA12_transfer_param) : address = match t with 
Dext_build_transfer_param (from, to0, value) -> from

let value(t : dexter2FA12_transfer_param) : nat = match t with 
Dext_build_transfer_param (from, to0, value) -> value

let maybe(n : nat) :  (nat) option = if eqN n 0n then (None: (nat) option) else Some (n)

let to(t : dexter2FA12_transfer_param) : address = match t with 
Dext_build_transfer_param (from, to0, value) -> to0

let admin(s : dexter2FA12_State) : address = match s with 
Dext_build_state (tokens, allowances, admin, total_supply) -> admin

let total_supply(s : dexter2FA12_State) : nat = match s with 
Dext_build_state (tokens, allowances, admin, total_supply) -> total_supply

let set_State_allowances(f :  ((address * address), nat) map ->  ((address * address), nat) map) (r : dexter2FA12_State) : dexter2FA12_State = Dext_build_state ((tokens r), (f (allowances r)), (admin r), (total_supply r))

let setter_from_getter_State_allowances : ( ((address * address), nat) map ->  ((address * address), nat) map) -> dexter2FA12_State -> dexter2FA12_State = set_State_allowances

let set_State_tokens(f :  (address, nat) map ->  (address, nat) map) (r : dexter2FA12_State) : dexter2FA12_State = Dext_build_state ((f (tokens r)), (allowances r), (admin r), (total_supply r))

let setter_from_getter_State_tokens : ( (address, nat) map ->  (address, nat) map) -> dexter2FA12_State -> dexter2FA12_State = set_State_tokens

let try_transfer(sender0 : address) (param : dexter2FA12_transfer_param) (state : dexter2FA12_State) :  (dexter2FA12_State) option = let allowances_ = allowances state in 
let tokens_ = tokens state in 
match if eq_addr sender0 (from param) then Some (allowances_) else let allowance_key =  ((from param), sender0) in 
let authorized_value = match Map.find_opt allowance_key allowances_ with 
Some (v) -> v
 | None  -> 0n in 
match throwIf (ltbN authorized_value (value param)) with 
Some (val0) -> (Some ((Map.update allowance_key (maybe (subNTruncated authorized_value (value param))) allowances_)))
 | None  -> (None: ( ((address * address), nat) map) option) with 
Some (val0) -> (match let from_balance = match Map.find_opt (from param) tokens_ with 
Some (v) -> v
 | None  -> 0n in 
match throwIf (ltbN from_balance (value param)) with 
Some (val1) -> (Some ((Map.update (from param) (maybe (subNTruncated from_balance (value param))) tokens_)))
 | None  -> (None: ( (address, nat) map) option) with 
Some (val1) -> (let tokens_0 = let to_balance = match Map.find_opt (to param) val1 with 
Some (v) -> v
 | None  -> 0n in 
Map.update (to param) (maybe (addN to_balance (value param))) val1 in 
Some ((setter_from_getter_State_allowances (fun (a :  ((address * address), nat) map) -> val0) (setter_from_getter_State_tokens (fun (a :  (address, nat) map) -> tokens_0) state))))
 | None  -> (None: (dexter2FA12_State) option))
 | None  -> (None: (dexter2FA12_State) option)

let spender(a : dexter2FA12_approve_param) : address = match a with 
Dext_build_approve_param (spender, value_) -> spender

let value_(a : dexter2FA12_approve_param) : nat = match a with 
Dext_build_approve_param (spender, value_) -> value_

let try_approve(sender0 : address) (param : dexter2FA12_approve_param) (state : dexter2FA12_State) :  (dexter2FA12_State) option = let allowances_ = allowances state in 
let allowance_key =  (sender0, (spender param)) in 
let previous_value = match Map.find_opt allowance_key allowances_ with 
Some (v) -> v
 | None  -> 0n in 
match throwIf (andb (ltbN 0n previous_value) (ltbN 0n (value_ param))) with 
Some (val0) -> (let allowances_0 = Map.update allowance_key (maybe (value_ param)) allowances_ in 
Some ((setter_from_getter_State_allowances (fun (a :  ((address * address), nat) map) -> allowances_0) state)))
 | None  -> (None: (dexter2FA12_State) option)

let target(m : dexter2FA12_mintOrBurn_param) : address = match m with 
Dext_build_mintOrBurn_param (quantity, target) -> target

let quantity(m : dexter2FA12_mintOrBurn_param) : int = match m with 
Dext_build_mintOrBurn_param (quantity, target) -> quantity

let set_State_total_supply(f : nat -> nat) (r : dexter2FA12_State) : dexter2FA12_State = Dext_build_state ((tokens r), (allowances r), (admin r), (f (total_supply r)))

let setter_from_getter_State_total_supply : (nat -> nat) -> dexter2FA12_State -> dexter2FA12_State = set_State_total_supply

let try_mint_or_burn(sender0 : address) (param : dexter2FA12_mintOrBurn_param) (state : dexter2FA12_State) :  (dexter2FA12_State) option = match throwIf (not (eq_addr sender0 (admin state))) with 
Some (val0) -> (let tokens_ = tokens state in 
let old_balance = match Map.find_opt (target param) tokens_ with 
Some (v) -> v
 | None  -> 0n in 
let new_balance = addInt (z_of_N old_balance) (quantity param) in 
match throwIf (ltInt new_balance 0) with 
Some (val1) -> (let tokens_0 = Map.update (target param) (maybe (abs new_balance)) tokens_ in 
let total_supply_ = abs (addInt (z_of_N (total_supply state)) (quantity param)) in 
Some ((setter_from_getter_State_total_supply (fun (a : nat) -> total_supply_) (setter_from_getter_State_tokens (fun (a :  (address, nat) map) -> tokens_0) state))))
 | None  -> (None: (dexter2FA12_State) option))
 | None  -> (None: (dexter2FA12_State) option)

let request(g : dexter2FA12_getAllowance_param) : (address * address) = match g with 
Dext_build_getAllowance_param (request, allowance_callback) -> request

let return_addr(c : dexter2FA12_callback) : address = match c with 
Dext_Build_callback (return_addr) -> return_addr

let callback_addr(c : dexter2FA12_callback) : address = return_addr c

let allowance_callback(g : dexter2FA12_getAllowance_param) : dexter2FA12_callback = match g with 
Dext_build_getAllowance_param (request, allowance_callback) -> allowance_callback

let receive_allowance_(n : nat) :  (unit) dexter2FA12_FA12ReceiverMsg = Dext_receive_allowance (n)

let try_get_allowance(param : dexter2FA12_getAllowance_param) (state : dexter2FA12_State) :  (operation) list = let value = match Map.find_opt (request param) (allowances state) with 
Some (v) -> v
 | None  -> 0n in 
(mk_callback (callback_addr (allowance_callback param)) (receive_allowance_ value)) :: ([]: (operation) list)

let owner_(g : dexter2FA12_getBalance_param) : address = match g with 
Dext_build_getBalance_param (owner_, balance_callback) -> owner_

let balance_callback(g : dexter2FA12_getBalance_param) : dexter2FA12_callback = match g with 
Dext_build_getBalance_param (owner_, balance_callback) -> balance_callback

let receive_balance_of_(n : nat) :  (unit) dexter2FA12_FA12ReceiverMsg = Dext_receive_balance_of (n)

let try_get_balance(param : dexter2FA12_getBalance_param) (state : dexter2FA12_State) :  (operation) list = let value = match Map.find_opt (owner_ param) (tokens state) with 
Some (v) -> v
 | None  -> 0n in 
(mk_callback (callback_addr (balance_callback param)) (receive_balance_of_ value)) :: ([]: (operation) list)

let supply_callback(g : dexter2FA12_getTotalSupply_param) : dexter2FA12_callback = match g with 
Dext_build_getTotalSupply_param (request_, supply_callback) -> supply_callback

let receive_total_supply_(n : nat) :  (unit) dexter2FA12_FA12ReceiverMsg = Dext_receive_total_supply (n)

let try_get_total_supply(param : dexter2FA12_getTotalSupply_param) (state : dexter2FA12_State) :  (operation) list = let value = total_supply state in 
(mk_callback (callback_addr (supply_callback param)) (receive_total_supply_ value)) :: ([]: (operation) list)

let receive_lqt(ctx : cctx) (state : dexter2FA12_State) (maybe_msg :  (dexter2FA12_Msg) option) :  ((dexter2FA12_State *  (operation) list)) option = let sender0 = ctx_from ctx in 
let without_actions = fun (o :  (dexter2FA12_State) option) -> match o with 
Some (a) -> (Some ( (a, ([]: (operation) list))))
 | None  -> (None: ((dexter2FA12_State *  (operation) list)) option) in 
let without_statechange = fun (acts :  (operation) list) -> Some ( (state, acts)) in 
match throwIf ((fun (x : tez) -> 0tez < x) (ctx_amount ctx)) with 
Some (val0) -> (match maybe_msg with 
Some (m) -> (match m with 
Dext_msg_transfer (param) -> (without_actions (try_transfer sender0 param state))
 | Dext_msg_approve (param) -> (without_actions (try_approve sender0 param state))
 | Dext_msg_mint_or_burn (param) -> (without_actions (try_mint_or_burn sender0 param state))
 | Dext_msg_get_allowance (param) -> (without_statechange (try_get_allowance param state))
 | Dext_msg_get_balance (param) -> (without_statechange (try_get_balance param state))
 | Dext_msg_get_total_supply (param) -> (without_statechange (try_get_total_supply param state)))
 | None  -> (None: ((dexter2FA12_State *  (operation) list)) option))
 | None  -> (None: ((dexter2FA12_State *  (operation) list)) option)

let receive_(chain : chain) (ctx : cctx) (state : dexter2FA12_State) (maybe_msg :  (dexter2FA12_Msg) option) :  (( (operation) list * dexter2FA12_State)) option = match receive_lqt ctx state maybe_msg with 
Some (x) -> (Some ( (x.1, x.0)))
 | None  -> (None: (( (operation) list * dexter2FA12_State)) option)

let init (setup : dexter2FA12_Setup) : dexter2FA12_State = let inner (setup : dexter2FA12_Setup) : (dexter2FA12_State) option = 
Some ((Dext_build_state ((Map.add (lqt_provider setup) (initial_pool setup) (Map.empty:  (address, nat) map)), (Map.empty:  ((address * address), nat) map), (admin_ setup), (initial_pool setup)))) in
match (inner setup) with
  Some v -> v
| None -> (failwith ("Init failed"): dexter2FA12_State)


type return = (operation) list * dexter2FA12_State

let main (p, st : dexter2FA12_Msg option * dexter2FA12_State) : return = 
   (match (receive_ dummy_chain cctx_instance  st p) with   
      Some v -> (v.0, v.1)
    | None -> (failwith ("Contract returned None") : return))
