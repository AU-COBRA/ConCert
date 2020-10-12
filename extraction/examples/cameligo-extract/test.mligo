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

let my_account : address =
  ("tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx" : address)

type msg = 
Inc of (int)
| Dec of (int)


type simpleCallCtx = (timestamp * (address * (tez * tez)))

type storage = (int * address)

let inc_balance (st : storage) (new_balance : int) =  ((addInt st.0 new_balance), st.1)

let dec_balance (st : storage) (new_balance : int) =  ((subInt st.0 new_balance), st.1)

let counter (msg : msg) (st : storage) = match msg with
   Inc (i) -> (if leInt 0 i then Some ( (([]: operation list), (inc_balance st i))) else (None: (operation list * storage) option))
 | Dec (i) -> (if leInt 0 i then Some ( (([]: operation list), (dec_balance st i))) else (None: (operation list * storage) option))

let storage (setup : (int * address)) : storage = 
  let inner (ctx : simpleCallCtx) (setup : (int * address)) : (storage) option = 
    let ctx = ctx in 
    Some (setup) in
  let ctx = (Tezos.now,
    (Tezos.source,
    (Tezos.amount,
      Tezos.balance))) in
  match (inner ctx setup) with
    Some v -> v
  | None -> (failwith (""):  storage)

type parameter = msg
type storage = storage
type return = (operation) list * storage
type parameter_wrapper =
  Init of storage
| Call of parameter

let wrapper (param, st : parameter_wrapper * storage) : return =
  match param with  
    Init st_init -> (([]: operation list), st_init) 
  | Call p -> (match (counter p st) with  
      Some v -> v
    | None -> (failwith ("") : return)) 

let main (action, st : parameter_wrapper * storage) : return = wrapper (action, st)