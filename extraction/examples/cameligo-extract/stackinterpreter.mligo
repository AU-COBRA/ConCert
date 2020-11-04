
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

type op = 
Add
| Sub
| Mult
| Lt
| Le
| Equal


type instruction = 
IPushZ of (int)
| IPushB of (bool)
| IObs of ((string * int))
| IIf
| IElse
| IEndIf
| IOp of (op)


type value = 
BVal of (bool)
| ZVal of (int)


type params = ( (instruction) list * (string * int,value) map)

type simpleCallCtx = (timestamp * (address * (tez * tez)))

type storage =  (value) list



let continue_ (i : int) = eqInt i 0

let bool_to_cond (b : bool) = if b then 0 else 1

let flip (i : int) = if eqInt i 0 then 1 else if eqInt i 1 then 0 else i

let reset_decrement (i : int) = if leInt i 1 then 0 else subInt i 1

let interp  = let rec interp  ((ext : (string * int,value) map), (insts :  (instruction) list), (s :  (value) list), (cond : int)) :  ( (value) list) option = 
match insts with 
[] -> (Some (s))
 | hd :: inst_ -> (match hd with 
IPushZ (i) -> (if continue_ cond then interp (ext, inst_, ((ZVal (i)) :: s), cond) else interp (ext, inst_, s, cond))
 | IPushB (b) -> (if continue_ cond then interp (ext, inst_, ((BVal (b)) :: s), cond) else interp (ext, inst_, s, cond))
 | IObs (p) -> (if continue_ cond then match Map.find_opt p ext with 
Some (v) -> (interp (ext, inst_, (v :: s), cond))
 | None  -> (None: ( (value) list) option) else interp (ext, inst_, s, cond))
 | IIf  -> (if eqInt cond 0 then match s with 
[] -> (None: ( (value) list) option)
 | v :: s_ -> (match v with 
BVal (b) -> (interp (ext, inst_, s_, (bool_to_cond b)))
 | ZVal (z) -> (None: ( (value) list) option)) else interp (ext, inst_, s, (addInt 1 cond)))
 | IElse  -> (interp (ext, inst_, s, (flip cond)))
 | IEndIf  -> (interp (ext, inst_, s, (reset_decrement cond)))
 | IOp (op) -> (if continue_ cond then match op with 
Add  -> (match s with 
[] -> (None: ( (value) list) option)
 | v :: l -> (match v with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (i) -> (match l with 
[] -> (None: ( (value) list) option)
 | v0 :: s_ -> (match v0 with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (j) -> (interp (ext, inst_, ((ZVal ((addInt i j))) :: s_), cond))))))
 | Sub  -> (match s with 
[] -> (None: ( (value) list) option)
 | v :: l -> (match v with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (i) -> (match l with 
[] -> (None: ( (value) list) option)
 | v0 :: s_ -> (match v0 with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (j) -> (interp (ext, inst_, ((ZVal ((subInt i j))) :: s_), cond))))))
 | Mult  -> (match s with 
[] -> (None: ( (value) list) option)
 | v :: l -> (match v with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (i) -> (match l with 
[] -> (None: ( (value) list) option)
 | v0 :: s_ -> (match v0 with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (j) -> (interp (ext, inst_, ((ZVal ((multInt i j))) :: s_), cond))))))
 | Lt  -> (match s with 
[] -> (None: ( (value) list) option)
 | v :: l -> (match v with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (i) -> (match l with 
[] -> (None: ( (value) list) option)
 | v0 :: s_ -> (match v0 with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (j) -> (interp (ext, inst_, ((BVal ((ltInt i j))) :: s_), cond))))))
 | Le  -> (match s with 
[] -> (None: ( (value) list) option)
 | v :: l -> (match v with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (i) -> (match l with 
[] -> (None: ( (value) list) option)
 | v0 :: s_ -> (match v0 with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (j) -> (interp (ext, inst_, ((BVal ((leInt i j))) :: s_), cond))))))
 | Equal  -> (match s with 
[] -> (None: ( (value) list) option)
 | v :: l -> (match v with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (i) -> (match l with 
[] -> (None: ( (value) list) option)
 | v0 :: s_ -> (match v0 with 
BVal (b) -> (None: ( (value) list) option)
 | ZVal (j) -> (interp (ext, inst_, ((BVal ((eqInt i j))) :: s_), cond)))))) else interp (ext, inst_, s, cond)))
 in fun (ext : (string * int,value) map) (insts :  (instruction) list) (s :  (value) list) (cond : int) -> interp (ext, insts, s, cond)

let receive (p : params) (s :  (value) list) = let s_ = s in 
match interp p.1 p.0 ([]: (value) list) 0 with 
Some (v) -> (Some ( (([]: (operation) list), v)))
 | None  -> (None: (( (operation) list * storage)) option)

let receive_ (s : storage) (msg :  (params) option) = match msg with 
Some (msg0) -> (receive msg0 s)
 | None  -> (None: (( (operation) list * storage)) option)

let init (a : unit) : storage = 
let inner (ctx : simpleCallCtx) : (storage) option = 
let ctx_ = ctx in 
Some (([]: (value) list)) in
let ctx = (Tezos.now,
   (Tezos.source,
   (Tezos.amount,
    Tezos.balance))) in
match (inner ctx) with
  Some v -> v
| None -> (failwith (""): storage)
type init_args_ty = unit
let init_wrapper (args : init_args_ty) =
  init()


type return = (operation) list * (storage option)
type parameter_wrapper =
  Init of init_args_ty
| Call of params option
let wrapper (param, st : parameter_wrapper * (value list) option) : return =
  match param with  
    Init init_args -> (([]: operation list), Some (init init_args))
  | Call p -> (
    match st with
      Some st -> (match (receive_ st p) with   
                    Some v -> (v.0, Some v.1)
                  | None -> (failwith ("") : return))
    | None -> (failwith ("cannot call this endpoint before Init has been called"): return))
let main (action, st : parameter_wrapper * storage option) : return = wrapper (action, st)
