let[@inline] fst (p : 'a * 'b) : 'a = p.(0)
let[@inline] snd (p : 'a * 'b) : 'b = p.(1)
let[@inline] addInt (i : int) (j : int) = i + j
let[@inline] subInt (i : int) (j : int) = i - j
let[@inline] leInt (i : int) (j : int) = i <= j
let[@inline] ltInt (i : int) (j : int) = i < j
let[@inline] eqInt (i : int) (j : int) = i = j
let exist a = a

type storage = int

type coq_sumbool =
Coq_left
| Coq_right


type coq_msg =
Coq_Inc of int
| Coq_Dec of int


let coq_inc_counter (st : storage) (inc : int) = exist ((addInt st ((fun x -> x) inc)))

let coq_dec_counter (st : storage) (dec : int) = exist ((subInt st ((fun x -> x) dec)))

let coq_my_bool_dec (b1 : bool) (b2 : bool) = (if b1 then fun x -> if x then Coq_left else Coq_right else fun x -> if x then Coq_right else Coq_left) b2

let coq_counter (msg : coq_msg) (st : storage) = match msg with
Coq_Inc (i) -> (match coq_my_bool_dec (ltInt 0 i) true with
Coq_left  -> (Some ( ([], ((fun x -> x) (coq_inc_counter st (exist (i)))))))
 | Coq_right  -> None)
 | Coq_Dec (i) -> (match coq_my_bool_dec (ltInt 0 i) true with
Coq_left  -> (Some ( ([], ((fun x -> x) (coq_dec_counter st (exist (i)))))))
 | Coq_right  -> None)

let wrapper param (st : storage) = match coq_counter param st with| Some v -> v| None -> failwith ()

let%entry main param st = wrapper param st