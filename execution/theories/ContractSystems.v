(* Systems of Contracts *)
From Coq Require Import List.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractMorphisms.

Definition pair_fun {S T S' T' : Type} 
    (f : S -> S') (g : T -> T') (x : S * T) : S' * T' :=
    let (s,t) := x in (f s, g t).
Definition pair_fun2 {S T S' T' S'' T'' : Type}
    (f : S -> S' -> S'') (g : T -> T' -> T'') (x : S * T) (y : S' * T') : S'' * T'' := 
    let (s,t) := x in let (s', t') := y in (f s s', g t t').

Section ContractTransformations.
Context { Base : ChainBase }.

(** We define the product of two contracts *)
Section ContractProducts.
Definition init_product 
        { Setup Setup' State State' Error Error' : Type}
    (init  : Chain -> ContractCallContext -> Setup  -> result State  Error)
    (init' : Chain -> ContractCallContext -> Setup' -> result State' Error') :
    (Chain -> ContractCallContext -> Setup * Setup' -> result (State * State') (Error + Error')) := 
    (fun (c : Chain) (ctx : ContractCallContext) (x : Setup * Setup') => 
        match (pair_fun (init c ctx) (init' c ctx) x) with 
        | (Err e, _) => Err (inl e) 
        | (_, Err e) => Err (inr e) 
        | (Ok s, Ok s') => Ok (s, s')
        end).

Definition recv_product 
        { State State' Msg Msg' Error Error' : Type}
    (recv  : Chain -> ContractCallContext -> State  -> option Msg  -> result (State  * list ActionBody) Error)
    (recv' : Chain -> ContractCallContext -> State' -> option Msg' -> result (State' * list ActionBody) Error') : 
    Chain -> ContractCallContext -> State * State' -> option (Msg * Msg') -> result ((State * State') * list ActionBody) (Error + Error') := 
    (fun (c : Chain) (ctx : ContractCallContext) (x1 : State * State') (x2 : option (Msg * Msg')) =>
        let x2' := 
            match x2 with 
            | None => (None, None)
            | Some (x,y) => (Some x, Some y)
            end in 
        match (pair_fun2 (recv c ctx) (recv' c ctx) x1 x2') with 
        | (Err e, _) => Err (inl e)
        | (_, Err e) => Err (inr e) 
        | (Ok r, Ok r') =>
            let (st, actns) := r in 
            let (st', actns') := r' in 
            Ok ((st, st'), actns ++ actns')
        end).

Definition product_contract 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C  : Contract Setup  Msg  State  Error) 
    (C' : Contract Setup' Msg' State' Error') : 
    Contract (Setup * Setup') (Msg * Msg') (State * State') (Error + Error') := 
    build_contract 
        (init_product C.(init) C'.(init))
        (recv_product C.(receive) C'.(receive)).

Lemma product_contract_associative
    { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    `{Serializable Msg''} `{Serializable Setup''} `{Serializable State''} `{Serializable Error''}
    { C : Contract Setup Msg State Error } 
    { C' : Contract Setup' Msg' State' Error' }
    { C'' : Contract Setup'' Msg'' State'' Error'' } : 
    contracts_isomorphic
        (product_contract C (product_contract C' C''))  
        (product_contract (product_contract C C') C'').
Proof. Admitted.

End ContractProducts.

(** We define the disjoint sum of two contracts *)
Section ContractSums.

Definition init_sum 
    { Setup Setup' State State' Error Error' : Type}
    (init  : Chain -> ContractCallContext -> Setup  -> result State Error)
    (init' : Chain -> ContractCallContext -> Setup' -> result State' Error') : 
    (Chain -> ContractCallContext -> Setup + Setup' -> result (State + State') (Error + Error' + unit)) := 
    (fun (c : Chain) (ctx : ContractCallContext) (x : Setup + Setup') => 
        match x with 
        | inl s => 
            match init c ctx s with 
            | Ok s' => Ok (inl s')
            | Err e => Err (inl (inl e)) 
            end
        | inr s =>
            match init' c ctx s with 
            | Ok s' => Ok (inr s')
            | Err e => Err (inl (inr e))
            end
        end).

Definition recv_sum 
    { Msg Msg' State State' Error Error' : Type }
    (recv  : Chain -> ContractCallContext -> State  -> option Msg  -> result (State  * list ActionBody) Error)
    (recv' : Chain -> ContractCallContext -> State' -> option Msg' -> result (State' * list ActionBody) Error') : 
    Chain -> ContractCallContext -> State + State' -> option (Msg + Msg') -> result ((State + State') * list ActionBody) (Error + Error' + unit) :=
    (fun (c : Chain) (ctx : ContractCallContext) (st : State + State') (op_msg : option (Msg + Msg')) => 
        match st with 
        | inl s => 
            match op_msg with 
            | Some msg => 
                match msg with 
                | inl m => 
                    match recv c ctx s (Some m) with 
                    | Ok (s', actns) => Ok (inl s', actns)
                    | Err e => Err (inl (inl e))
                    end 
                | inr m => Err (inr tt) (* fails if state/msg don't pertain to the same contract *)
                end 
            | None => 
                match recv c ctx s None with 
                | Ok (s', actns) => Ok (inl s', actns)
                | Err e => Err (inl (inl e))
                end 
        end 
        | inr s => 
            match op_msg with 
            | Some msg => 
                match msg with 
                | inr m => 
                    match recv' c ctx s (Some m) with 
                    | Ok (s', actns) => Ok (inr s', actns)
                    | Err e => Err (inl (inr e))
                    end
                | inl m => Err (inr tt) (* fails if state/msg don't pertain to the same contract *)
                end 
            | None => 
                match recv' c ctx s None with 
                | Ok (s', actns) => Ok (inr s', actns)
                | Err e => Err (inl (inr e))
                end
            end 
        end).

Definition sum_contract 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C : Contract Setup Msg State Error) 
    (C' : Contract Setup' Msg' State' Error') : 
    Contract (Setup + Setup') (Msg + Msg') (State + State') (Error + Error' + unit) := 
    build_contract 
        (init_sum C.(init) C'.(init))
        (recv_sum C.(receive) C'.(receive)).

Lemma sum_contract_associative
    { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    `{Serializable Msg''} `{Serializable Setup''} `{Serializable State''} `{Serializable Error''}
    { C : Contract Setup Msg State Error } 
    { C' : Contract Setup' Msg' State' Error' }
    { C'' : Contract Setup'' Msg'' State'' Error'' } :  
    contracts_isomorphic
        (sum_contract C (sum_contract C' C'')) 
        (sum_contract (sum_contract C C') C'').
Proof. Admitted.

Theorem sum_contract_projects_left
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C : Contract Setup Msg State Error}
    {C' : Contract Setup' Msg' State' Error'} : 
    exists (f : ContractMorphism (sum_contract C C') (sum_contract C null_contract)),
        is_surj_cm f.
Proof. Admitted.

Theorem sum_contract_projects_right
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C : Contract Setup Msg State Error}
    {C' : Contract Setup' Msg' State' Error'} : 
    exists (f : ContractMorphism (sum_contract C C') (sum_contract null_contract C')),
        is_surj_cm f.
Proof. Admitted.

Theorem sum_contract_embeds_left
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C : Contract Setup Msg State Error}
    {C' : Contract Setup' Msg' State' Error'} : 
    exists (f : ContractMorphism C (sum_contract C C')),
        is_inj_cm f.
Proof. Admitted.

Theorem sum_contract_embeds_right
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C : Contract Setup Msg State Error}
    {C' : Contract Setup' Msg' State' Error'} : 
    exists (f : ContractMorphism (sum_contract C C') C'),
        is_inj_cm f.
Proof. Admitted.

End ContractSums.


(** We define the joined sum of two contracts, which will be useful for reasoning about 
    systems of contracts *)
Section JoinedContractSum.

Definition init_joined_sum 
        { Setup Setup' State State' Error Error' : Type}
    (init  : Chain -> ContractCallContext -> Setup  -> result State Error)
    (init' : Chain -> ContractCallContext -> Setup' -> result State' Error') : 
    (Chain -> ContractCallContext -> Setup * Setup' -> result (State * State') (Error + Error')) := 
    (fun (c : Chain) (ctx : ContractCallContext) (x : Setup * Setup') => 
        let (s, s') := x in 
        match init c ctx s with
        | Ok st => 
            match init' c ctx s' with 
            | Ok st' => Ok (st, st')
            | Err e' => Err (inr e')
            end
        | Err e => Err (inl e)
        end).

Definition recv_joined_sum 
        { Msg Msg' State State' Error Error' : Type }
    (recv  : Chain -> ContractCallContext -> State  -> option Msg  -> result (State  * list ActionBody) Error)
    (recv' : Chain -> ContractCallContext -> State' -> option Msg' -> result (State' * list ActionBody) Error') : 
    Chain -> ContractCallContext -> State * State' -> option (Msg + Msg') -> result ((State * State') * list ActionBody) (Error + Error') :=
    (fun (c : Chain) (ctx : ContractCallContext) (st_pair : State * State') (op_msg : option (Msg + Msg')) => 
        let (st, st') := st_pair in 
        match op_msg with 
        | Some msg => 
            match msg with 
            | inl m => 
                match recv c ctx st (Some m) with 
                | Ok rslt => 
                    let (new_st, actns) := rslt in 
                    Ok ((new_st, st'), actns)
                | Err e => Err (inl e) 
                end 
            | inr m => 
                match recv' c ctx st' (Some m) with 
                | Ok rslt => 
                    let (new_st', actns) := rslt in 
                    Ok ((st, new_st'), actns)
                | Err e' => Err (inr e') 
                end 
            end 
        | None => (* is this what you want? *)
            match recv c ctx st None with 
            | Ok rslt => 
                match recv' c ctx st' None with 
                | Ok rslt' => 
                    let (new_st, actns) := rslt in 
                    let (new_st', actns') := rslt' in 
                    Ok ((new_st, new_st'), actns ++ actns')
                | Err e' => Err (inr e') 
                end 
            | Err e => Err (inl e) 
            end 
        end).

Definition joined_sum_contract 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C : Contract Setup Msg State Error) 
    (C' : Contract Setup' Msg' State' Error') : 
    Contract (Setup * Setup') (Msg + Msg') (State * State') (Error + Error') := 
    build_contract 
        (init_joined_sum C.(init) C'.(init))
        (recv_joined_sum C.(receive) C'.(receive)).

End JoinedContractSum.

End ContractTransformations.