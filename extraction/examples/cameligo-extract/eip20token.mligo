
[@inline] let addInt (i : int) (j : int) = i + j
[@inline] let subInt (i : int) (j : int) = i - j
[@inline] let multInt (i : int) (j : int) = i * j
[@inline] let divInt (i : int) (j : int) = i / j
[@inline] let leInt (i : int) (j : int) = i <= j
[@inline] let ltInt (i : int) (j : int) = i < j
[@inline] let eqInt (i : int) (j : int) = i = j

[@inline] let addTez (n : tez) (m : tez) = n + m
[@inline] let subTez (n : tez) (m : tez) = n - m
[@inline] let leTez (a : tez ) (b : tez ) = a <= b
[@inline] let ltTez (a : tez ) (b : tez ) =  a < b
[@inline] let gtbTez (a : tez ) (b : tez ) =  a > b
[@inline] let eqTez (a : tez ) (b : tez ) = a = b

[@inline] let modN (a : nat ) (b : nat ) = a mod b
[@inline] let divN (a : nat ) (b : nat ) = a / b
[@inline] let eqN (a : nat ) (b : nat ) = a = b
[@inline] let lebN (a : nat ) (b : nat ) = a <= b
[@inline] let ltbN (a : nat ) (b : nat ) = a < b

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

type tokenValue = nat

type msg = 
Transfer of (address * tokenValue)
| Transfer_from of (address * address * tokenValue)
| Approve of (address * tokenValue)


type setup = {
owner : address;
init_amount : tokenValue
}

type state = {
total_supply : tokenValue;
balances :  (address, tokenValue) map;
allowances :  (address,  (address, tokenValue) map) map
}

let partial_alter_addr_nat (f : nat option -> nat option)
                           (k : address)
                           (m : (address,nat) map) : (address,nat) map =
  match Map.find_opt k m with
    Some v -> Map.update k (f v) m
  | None -> Map.update k (f (None : nat option)) m

let option_map_state_acts (f : state -> (state * operation list)) (o : state option) =
  match o with
    Some a -> Some (f a)
    | None -> (None : (state * operation list))
let bind_option_state (a, b, c : unit) (m : state option) (f : state -> state option) : state option =
match m with
    Some a -> f a
  | None -> (None : state option)
let with_default_N (n : nat) (m : nat option) : n =
  match m with
    Some m -> m
  | None -> n

let test_try_transfer (from : address) (to : address) (amount : tokenValue) (state : state) = let from_balance = with_default_N 0n (Map.find_opt from state.balances) in 
if ltInt from_balance amount then (None: (state) option) else let new_balances = Map.add  from (subInt from_balance amount) state.balances in 
let new_balances0 = partial_alter_addr_nat (fun (balance :  (nat) option ->  (nat) option) -> Some ((addInt (with_default_N 0n balance) amount))) to new_balances in 
Some (({total_supply = state.total_supply; balances = new_balances0; allowances = state.allowances}: state))

let test_try_transfer_from (delegate : address) (from : address) (to : address) (amount : tokenValue) (state : state) = match Map.find_opt from state.allowances with 
Some (from_allowances_map) -> (match Map.find_opt delegate from_allowances_map with 
Some (delegate_allowance) -> (let from_balance = with_default_N 0n (Map.find_opt from state.balances) in 
if orb (ltInt delegate_allowance amount) (ltInt from_balance amount) then (None: (state) option) else let new_allowances = Map.add  delegate (subInt delegate_allowance amount) from_allowances_map in 
let new_balances = Map.add  from (subInt from_balance amount) state.balances in 
let new_balances0 = partial_alter_addr_nat (fun (balance :  (nat) option ->  (nat) option) -> Some ((addInt (with_default_N 0n balance) amount))) to new_balances in 
Some (({total_supply = state.total_supply; balances = new_balances0; allowances = (Map.add  from new_allowances state.allowances)}: state)))
 | None  -> (None: (state) option))
 | None  -> (None: (state) option)

let test_receive (chain : chain) (ctx : (adress * (address * int))) (state : state) (maybe_msg :  (msg) option) = let chain_ = chain in 
let sender = Tezos.sender in 
let without_actions = option_map_state_acts (fun (new_state : state -> ( (actionBody) list * state)) ->  (([]: (actionBody) list), new_state)) in 
match maybe_msg with 
Some (m) -> (match m with 
Transfer (to, amount) -> (without_actions (test_try_transfer sender to amount state))
 | Transfer_from (from, to, amount) -> (without_actions (test_try_transfer_from sender from to amount state))
 | Approve (a, t) -> (None: (( (actionBody) list * state)) option))
 | None  -> (None: (( (actionBody) list * state)) option)

let init (a : unit) : state = 

let inner (setup : setup) : (state) option = 
Some (({total_supply = setup.init_amount; balances = Map.empty; allowances = Map.empty}: state)) in
let ctx = (Tezos.now,
   (Tezos.sender,
   (Tezos.amount,
    Tezos.balance))) in
match (inner ctx) with
  Some v -> v
| None -> (failwith (""): state)
type init_args_ty = unit
let init_wrapper (args : init_args_ty) =
  init()


type return = (operation) list * (storage option)
type parameter_wrapper =
  Init of init_args_ty
| Call of msg option

let wrapper (param, st : parameter_wrapper * (state) option) : return =
  match param with  
    Init init_args -> (([]: operation list), Some (init init_args))
  | Call p -> (
    match st with
      Some st -> (match (eip20token dummy_chain (Tezos.sender,
   (Tezos.self_address,
    Tezos.amount))) st p) with   
                    Some v -> (v.0, Some v.1)
                  | None -> (failwith ("") : return))
    | None -> (failwith ("cannot call this endpoint before Init has been called"): return))
let main (action, st : parameter_wrapper * storage option) : return = wrapper (action, st)
