(* Systems of Contracts *)
From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Sets.Ensembles.
From Coq Require Import ZArith.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractMorphisms.

Axiom todo : string -> forall {A}, A.

Definition pair_fun {S T S' T' : Type} 
    (f : S -> S') (g : T -> T') (x : S * T) : S' * T' :=
    let (s,t) := x in (f s, g t).
Definition pair_fun2 {S T S' T' S'' T'' : Type}
    (f : S -> S' -> S'') (g : T -> T' -> T'') (x : S * T) (y : S' * T') : S'' * T'' := 
    let (s,t) := x in let (s', t') := y in (f s s', g t t').


Section MultiChainWeakEquivalences.
Context { Base1 Base2 : ChainBase }.

Definition MultiChainState : Type := @ChainState Base1 * @ChainState Base2.
Definition MultiChainStep (prev_multi_bstate : MultiChainState) (next_multi_bstate : MultiChainState) : Type := 
        @ChainStep Base1 (fst prev_multi_bstate) (fst next_multi_bstate) +
        @ChainStep Base2 (snd prev_multi_bstate) (snd next_multi_bstate) +
       (@ChainStep Base1 (fst prev_multi_bstate) (fst next_multi_bstate) *
        @ChainStep Base2 (snd prev_multi_bstate) (snd next_multi_bstate)).
Definition MultiChainTrace := ChainedList MultiChainState MultiChainStep.

(* multi-chain contract : Defn 6.3.2 *)


(* multi-chain null contract *)

(* multi-chain morphism *)
Definition multichain_empty_state : MultiChainState := (empty_state, empty_state).

Definition multichain_reachable (mstate : MultiChainState) : Prop := 
    reachable (fst mstate) /\ reachable (snd mstate).

(* A multi-chain morphism is a morphism of linked lists *)
(* TODO restrict to reachability? *)
Record MultiChainMorphism := build_multi_chain_morphism {
    multichainstate_morph : MultiChainState -> MultiChainState ; 
    multi_empty_fixpoint : 
        multichainstate_morph multichain_empty_state = multichain_empty_state ; 
    multichainstep_morph : 
        forall mstate1 mstate2, 
        MultiChainStep mstate1 mstate2 -> 
        MultiChainStep (multichainstate_morph mstate1) (multichainstate_morph mstate2) ;
}.

(* Lemma : takes reachable states to reachable states *)
(* TODO AFTER you sorted out contract morphisms *)

(* composition of multi-chain morphisms *)
(* an auxiliary lemma *)
Lemma multichain_compose_fixpoint_result (mch1 mch2 : MultiChainMorphism) : 
    compose (multichainstate_morph mch2) (multichainstate_morph mch1) multichain_empty_state =
    multichain_empty_state.
Proof. Admitted.

(* composition of multi-chain morphisms *)
Definition composition_mch (mch1 mch2 : MultiChainMorphism) : MultiChainMorphism := {| 
    multichainstate_morph := 
        compose (multichainstate_morph mch1) (multichainstate_morph mch2) ; 
    multi_empty_fixpoint := multichain_compose_fixpoint_result mch2 mch1 ;
    multichainstep_morph := (fun b1 b2 => 
        compose 
            (multichainstep_morph mch2 
                (multichainstep_morph mch1 b1)
                (multichainstep_morph mch2 b2))
            (multichainstep_morph mch1 b1 b2)) ;
|}.

(* composition is associative *)
Lemma composition_assoc_mch : forall mch1 mch2 mch3, 
    composition_mch (composition_mch mch3 mch2) mch1 = 
    composition_mch mch3 (composition_mch mch2 mch1).
Proof. (* proof omitted *) Qed.

(*** identity morphism *)
(* an auxiliary lemma *)
Lemma multi_empty_fixpoint_id : 
    @id MultiChainState multichain_empty_state = multichain_empty_state.
Proof. auto. Qed.

(* the identity multi-chain morphism *)
Definition id_mch : MultiChainMorphism := {| 
    multichainstate_morph := @id MultiChainState ; 
    multi_empty_fixpoint := multi_empty_fixpoint_id ;
    multichainstep_morph := (fun b1 b2 => @id (MultiChainStep b1 b2)) ;
|}.

(* left and right composition results *)
Lemma composition_mch_left : forall mch, composition_mch id_mch mch = mch.
Proof. (* proof omitted *) Qed.

Lemma composition_mch_right : forall mch, composition_mch mch id_mch = mch.
Proof. (* proof omitted *) Qed.

End MultiChainWeakEquivalences.


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
Proof. 
    unfold contracts_isomorphic.
    unfold is_iso_cm.
Admitted.

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

(* TODO 
    - Transform actions so addresses are right 
    - Keep track of balances    
*)
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

(* you want the universal properties, right? *)




(* sum a system of contracts *)





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

(* NEXT : CONSTRUCT BISIMULATIONS OF CHAINS VIA THESE TRANSFORMATIONS
    YOU ONLY NEED TO DO TWO AT A TIME *)


Section WeakContractMorphisms.

(* a weak morphism between a system of contracts and a monolithic contract *)


(* THEN one corresponding to each of these constructions ^^ (with conditions on what's needed, e.g. account balances unchanged) *)

End WeakContractMorphisms.


Section ChainMorphisms.

Record ChainMorphism := build_chain_morphism {
    chainstate_morph : ChainState -> ChainState ; 
    chainstep_morph : 
        forall bstate1 bstate2, 
        ChainStep bstate1 bstate2 -> 
        ChainStep (chainstate_morph bstate1) (chainstate_morph bstate2) ;
}.

(* the identity chain morphism *)
Definition id_chm : ChainMorphism := {| 
    chainstate_morph := id_fun ChainState ; 
    chainstep_morph := (fun b1 b2 => id_fun (ChainStep b1 b2)) ; |}.

Definition composition_chm (chm2 chm1 : ChainMorphism) : ChainMorphism := {| 
    chainstate_morph := compose (chainstate_morph chm2) (chainstate_morph chm1) ;
    chainstep_morph  := (fun b1 b2 => 
        compose 
            (chainstep_morph chm2 
                (chainstate_morph chm1 b1) 
                (chainstate_morph chm1 b2)) 
            (chainstep_morph chm1 b1 b2)) ;
|}.

Lemma composition_chm_left : forall chm, composition_chm id_chm chm = chm.
Proof. 
    intro. unfold composition_chm. 
    destruct chm. f_equal; simpl.
Qed.

Lemma composition_chm_right : forall chm, composition_chm chm id_chm = chm.
Proof. 
    intro. unfold composition_chm. 
    destruct chm. f_equal; simpl.
Qed.

Lemma composition_assoc_chm : forall chm1 chm2 chm3, 
    composition_chm (composition_chm chm3 chm2) chm1 = 
    composition_chm chm3 (composition_chm chm2 chm1).
Proof.
    intros. unfold composition_chm. f_equal.
Qed.

(* chain isomoprhisms, which are bisimulations of blockchains *)
Definition is_iso_chm (f g : ChainMorphism) : Prop := 
    composition_chm g f = id_chm /\ 
    composition_chm f g = id_chm.

End ChainMorphisms.

(*  Some conditions under which a system of contracts can be 
    contracted via a chain (e.g. bisimulated) *)

Section SystemContraction.
Import ListNotations.

Definition cm_lift' 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} : 
    (f : ContractMorphism C C') -> ChainMorphism.


(* the chainstate (cst) morphism : system to monolithic *)
Definition cst_system_to_mono 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'}
    (caddr1 caddr2 : Address)
    (bstate : ChainState) : ChainState := 
    {| chain_state_env :=
       {| env_chain :=
            {| chain_height := 0;
               current_slot := 0;
               finalized_height := 0; |};
          env_account_balances a := 0%Z;
          env_contract_states a := None;
          env_contracts a := None; |};
     chain_state_queue := [] |}.

(* the chainstep (csp) morphism : system to monolithic *)
Definition csp_system_to_mono

(* the chain morphism (chm) : system to monolithic *)
Definition chm_system_to_mono 





Definition chm_mono_to_system


Theorem system_contraction 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} : 
    forall bstate caddr1 caddr2, 
    (* such that caddr1 is C and caddr2 is C' *)

    (* the chain morphism defined above *)


End SystemContraction.


(** A weak equivalence of Environments and ChainStates *)
Section ChainStateWeakEquivalence.
(* SETTING:
    - I have a system of contracts, which consists of: 
        - a POINTED set of addresses, which is the point of contraction (perhaps define this yourself)
    - I need to transform it into a disjoint sum of contracts living at one address
    - And then prove a bisimulation
*)

Definition ActionWeakTransform (* 
  - transforms actions into the contracts in the system into actions into the joined contract 
  - this changes:
    - from (modular => monolithic)
    - to (modular => monolithic)
    - msg (msg => inl msg or inr msg, etc) -- perhaps you define this when you define the contraction
  - TODO what to do about deployments?
*)

Definition EnvironmentWeakEquiv (e1 e2 : Environment) 
    (mon : (Address * WeakContract)) (* the monolithic contract *)
    (sys : list (Address * WeakContract)) (* the system of contracts*) := 
    build_env_weak_eq {
        chain_weak_eq : 
        (* we need to adjust chain height to account for deployments and, later, *) ;
        account_balances_weak_eq : 
            forall a,
                (* if a not in list *)
                (* then same *)
                (* otherwise, sum of the list balances = the monolithic balance *) ;
        contracts_weak_eq : 
            forall a,
                (* if a not in list *)
                (* then same *)
                (* otherwise, None in list, mon at mon_addr *) ;
        contract_states_weak_eq : 
            forall a,
            (* if a not in list *)
            (* then same *)
            (* otherwise, None in list, mon's state at mon_addr *) ;
    }.

(*
  - Chain : ?
  - Balances : sum of balance of system should always equal balance of 
  - (weak) Contracts : monolithic address has monolithic contract; each 
  - States : states are none at old addresses, are the combined state at the pointed address 
*)


Definition ChainStateWeakEquiv (* 
  - list Action : ?
*)


(*
  - this is a NOTION of equivalence, parameterized over a system of contracts.
  - you need to prove that this notion of equivalence is actually a BISIMULATION
  - then provide sufficient conditions to achieve this ...
     - the idea being that you take a system and combine it in any way listed above ^^.
       then you have a single contract you can reason about.
*)



Context 
    (* we can lift a morphism of contracts, parameterized by the morphpism f and the address of C1 *)
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'}
    {f : ContractMorphism C1 C2}.

Definition wc_dec_eq : forall w1 w2 : WeakContract, {w1 = w2} + {w1 <> w1} := todo "".
Declare Scope wc_scope.
Delimit Scope wc_scope with wc.
Bind Scope wc_scope with WeakContract.
Infix "=?" := wc_dec_eq (at level 70) : wc_scope.

(* Given f, we can transform actions *)
Definition action_transform { addrs : set Address } (native_env : Environment) (a : Action) : Action := {| 
    act_origin := act_origin a ;
    act_from := act_from a ;
    act_body := 
        match act_body a with 
        (* contract calls into C1 change to calls into C2 *)
        | act_call to amt msg => 
            match env_contracts native_env to with 
            | Some wc => 
                if (wc =? contract_to_weak_contract C1)%wc
                then act_call to amt msg
                else act_body a
            | None => act_body a
            end
        (* we deploy C2 instead of C1 *)
        | act_deploy amt c setup => 
            if (c =? contract_to_weak_contract C1)%wc
            then act_deploy amt (contract_to_weak_contract C2) setup
            else act_body a
        (* all amounts stay the same, so we do not change transfers *)
        | act_transfer _ _ => act_body a 
        end
|}.

(* A morphism of Environments, parameterized implicitly over f by swapping out C2 for C1 *)
Record EnvironmentMorphism (e1 e2 : Environment) := 
    build_env_morphism {
        chain_eq' : env_chain e1 = env_chain e2 ;
        account_balances_eq' :
            forall a, env_account_balances e1 a = env_account_balances e2 a ;
        contracts_morph :
            forall a, 
                env_contracts e2 a = 
                match env_contracts e1 a with 
                | Some wc => 
                    if (wc =? contract_to_weak_contract C1)%wc 
                    then Some (contract_to_weak_contract C2) 
                    else Some wc
                | None => None 
                end ;
        contract_states_morph : 
            forall a, 
                env_contract_states e2 a = 
                match env_contracts e1 a with 
                | Some wc => 
                    if (wc =? contract_to_weak_contract C1)%wc 
                    then (option_fun (serialize_function state_morph)) (env_contract_states e1 a)
                    else env_contract_states e1 a
                | None => env_contract_states e1 a
                end ;
}.

(* A morphism of ChainStates, parameterized implicitly over f *)
Record ChainStateMorphism (cstate1 cstate2 : ChainState) := 
    build_chainstate_morphism {
        env_morph   : EnvironmentMorphism cstate1 cstate2 ;
        queue_morph : chain_state_queue cstate2 = 
                      List.map (action_transform cstate1) (chain_state_queue cstate1) ;
    }.

End ChainStateWeakEquivalence.


Section WeakContractMorphismLift.



End WeakContractMorphismLift.


End ContractTransformations.