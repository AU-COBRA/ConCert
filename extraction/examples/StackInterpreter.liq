let[@inline] fst (p : 'a * 'b) : 'a = p.(0)
let[@inline] snd (p : 'a * 'b) : 'b = p.(1)
let[@inline] addInt (i : int) (j : int) = i + j
let[@inline] subInt (i : int) (j : int) = i - j
let[@inline] leInt (i : int) (j : int) = i <= j
let[@inline] ltInt (i : int) (j : int) = i < j
let[@inline] eqInt (i : int) (j : int) = i = j
let[@inline] andb (a : bool ) (b : bool ) = a & b

type op = 
Add
| And
| Equal


type instruction = 
IPushZ of int
| IPushB of bool
| IObs of string * int
| IOp of op


type value = 
BVal of bool
| ZVal of int


type params = ( (instruction) list * (string * int,value) map)

type storage =  (value) list

let obs0 (s : string) = IObs (s, 0)

let interp  = let rec interp  (ext, insts, s) = 
match insts with 
[] -> (Some (s))
 | hd :: inst' -> (match hd with 
IPushZ (i) -> (interp (ext, inst', ((ZVal (i)) :: s)))
 | IPushB (b) -> (interp (ext, inst', ((BVal (b)) :: s)))
 | IObs (l, i) -> (match Map.find  (l, i) ext with 
Some (v) -> (interp (ext, inst', (v :: s)))
 | None  -> None)
 | IOp (op) -> (match op with 
Add  -> (match s with 
[] -> None
 | v :: l -> (match v with 
BVal (b) -> None
 | ZVal (i) -> (match l with 
[] -> None
 | v0 :: s' -> (match v0 with 
BVal (b) -> None
 | ZVal (j) -> (interp (ext, inst', ((ZVal ((addInt i j))) :: s')))))))
 | And  -> (match s with 
[] -> None
 | v :: l -> (match v with 
BVal (i) -> (match l with 
[] -> None
 | v0 :: s' -> (match v0 with 
BVal (j) -> (interp (ext, inst', ((BVal ((andb i j))) :: s')))
 | ZVal (z) -> None))
 | ZVal (z) -> None))
 | Equal  -> (match s with 
[] -> None
 | v :: l -> (match v with 
BVal (b) -> None
 | ZVal (i) -> (match l with 
[] -> None
 | v0 :: s' -> (match v0 with 
BVal (b) -> None
 | ZVal (j) -> (interp (ext, inst', ((BVal ((eqInt i j))) :: s')))))))))
 in interp

(* Test input (should give [BVal true]):

([IPushZ 0; IObs ("blah",0); IOp Add; IPushZ 1; IOp Equal], (Map [(("blah", 0), (ZVal 1))])) *)

let receive (p : params) (s :  (value) list) = interp ((snd p), (fst p), s)

let%init storage = []

let%entry main (p : params) s =
match receive p [] with
| Some res -> ( [], res ) 
| _ -> Current.failwith s