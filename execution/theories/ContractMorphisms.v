(* A Description of Morphisms of Contracts *)

From Coq Require Import Basics.
From Coq Require Import ProofIrrelevance.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Bool.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Permutation.
From Coq Require Import RelationClasses.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractSystems.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Execution Require Import InterContractCommunication.
From ConCert.Utils Require Import RecordUpdate.

Axiom todo : string -> forall {A}, A.

(* some auxiliary functions *)
Definition curry_fun3 {A B C D : Type} (f : A * B * C -> D) : A -> B -> C -> D := 
    fun (a : A) => fun (b : B) => fun (c : C) => f (a,b,c).
Definition uncurry_fun3 {A B C D : Type} (f : A -> B -> C -> D) : A * B * C -> D :=
    fun (x : A * B * C) => 
        let (x', c) := x in 
        let (a, b) := x' in f a b c.
Definition curry_fun4 {A B C D E : Type} (f : A * B * C * D -> E) : A -> B -> C -> D -> E :=
    fun (a : A) => fun (b : B) => fun (c : C) => fun (d : D) => f (a,b,c,d).
Definition uncurry_fun4 {A B C D E : Type} (f : A -> B -> C -> D -> E) : A * B * C * D -> E :=
    fun (x : A * B * C * D) => 
        let (x' , d) := x in 
        let (x'', c) := x' in 
        let (a, b) := x'' in f a b c d.
Definition serialize_function {A B} `{Serializable A} `{Serializable B} 
    (f : A -> B) (sv : SerializedValue) : SerializedValue := 
    match deserialize sv with 
    | None => sv (* should not be deserializable *)
    | Some a => serialize (f a)
    end.
Definition option_fun {A B} (f : A -> B) (op_a : option A) : option B := 
    match op_a with 
    | Some a => Some (f a)
    | None => None 
    end.

Section ContractMorphisms.
Context { Base : ChainBase }.


Section MorphismDefinition.
(* TODO amounts do not change with morphisms *)
(* TODO the actionbody outputs do not change with morphisms. JUST THE STATE. *)

(* init component *)
Definition init_morphs_commute  
    { Setup Setup' State State' Error Error' : Type}
    (init  : Chain -> ContractCallContext -> Setup  -> result State  Error)
    (init' : Chain -> ContractCallContext -> Setup' -> result State' Error')
    (init_inputs : Chain * ContractCallContext * Setup -> 
        Chain * ContractCallContext * Setup') 
    (init_outputs : result State Error -> result State' Error') :=
    forall x : Chain * ContractCallContext * Setup,
        uncurry_fun3 init' (init_inputs x) = 
        init_outputs (uncurry_fun3 init x).

Record InitCM
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C : Contract Setup Msg State Error) (C' : Contract Setup' Msg' State' Error') 
    (* takes input a state morphism *)
    := build_initcm {
        init_inputs : Chain * ContractCallContext * Setup -> 
            Chain * ContractCallContext * Setup' ;
        init_outputs : result State Error -> result State' Error' ;
        (* proof of diagram commutativity *)
        init_commutes : 
            init_morphs_commute C.(init) C'.(init) init_inputs init_outputs ;
    }.

(* recv component *)
Definition recv_morphs_commute 
    { Msg Msg' State State' Error Error' : Type }
    (recv  : Chain -> ContractCallContext -> State  -> option Msg  -> 
        result (State  * list ActionBody) Error)
    (recv' : Chain -> ContractCallContext -> State' -> option Msg' -> 
        result (State' * list ActionBody) Error')
    (recv_inputs : Chain * ContractCallContext * State * option Msg -> 
        Chain * ContractCallContext * State' * option Msg')
    (recv_outputs : result (State * list ActionBody) Error -> 
        result (State' * list ActionBody) Error') : Prop :=
        forall (x : Chain * ContractCallContext * State * option Msg), 
            uncurry_fun4 recv' (recv_inputs x) = 
            recv_outputs (uncurry_fun4 recv x).

Record RecvCM
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (* takes input a state morphism and an actionbody morphism *)
    (C : Contract Setup Msg State Error) (C' : Contract Setup' Msg' State' Error') := {
        recv_inputs : Chain * ContractCallContext * State * option Msg -> 
            Chain * ContractCallContext * State' * option Msg' ;
        recv_outputs : result (State * list ActionBody) Error -> 
            result (State' * list ActionBody) Error' ;
        (* proof of diagram commutativity *)
        recv_commutes : 
            recv_morphs_commute C.(receive) C'.(receive) recv_inputs recv_outputs ;
    }.

(* definition *)
Record ContractMorphism 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (* uses the same state morphism (and same actionbody morphism) *)
    (C  : Contract Setup  Msg  State  Error) 
    (C' : Contract Setup' Msg' State' Error') := {
        cm_init : InitCM C C' ;
        cm_recv : RecvCM C C' ;
    }.

End MorphismDefinition.


Section MorphismUtilities.

Definition init_cm 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} 
    (f : ContractMorphism C C') : InitCM C C' := 
    cm_init C C' f.
Definition recv_cm 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} 
    (f : ContractMorphism C C') : RecvCM C C' := 
    cm_recv C C' f.
Definition id_morph (A : Type) : A -> A := @id A.

End MorphismUtilities.


(* The Identity Contract Morphism *)
Section IdentityMorphism.

Lemma init_commutes_id 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) :
    init_morphs_commute 
        C.(init) C.(init) 
        (id_morph (Chain * ContractCallContext * Setup)) 
        (id_morph (result State Error)).
Proof. intro. auto. Qed.

Definition id_cm_init 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) :
    InitCM C C := {|
        init_inputs  := id_morph (Chain * ContractCallContext * Setup) ;
        init_outputs := id_morph (result State Error) ;
        (* proof of commutativity *)
        init_commutes := init_commutes_id C ;
    |}.

Lemma r_commutes_id 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) :
    recv_morphs_commute 
        C.(receive) C.(receive) 
        (id_morph (Chain * ContractCallContext * State * option Msg)) 
        (id_morph (result (State * list ActionBody) Error)).
Proof. intro. auto. Qed.

Definition id_cm_recv 
        { Setup Msg State Error : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) : RecvCM C C := {|
        recv_inputs := id_morph (Chain * ContractCallContext * State * option Msg) ;
        recv_outputs := id_morph (result (State * list ActionBody) Error) ;
        (* proof of commutativity *)
        recv_commutes := r_commutes_id C ;
    |}.

(* * the identity morphism *)
Definition id_cm 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) : ContractMorphism C C := {|
        cm_init := id_cm_init C ;
        cm_recv := id_cm_recv C ;
    |}.

End IdentityMorphism.

(* Deriving Equality of Contract Morphisms *)
Section EqualityOfMorphisms.

Lemma is_eq_cm 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} :
    forall (f g : ContractMorphism C C'), 
    init_cm f = init_cm g -> 
    recv_cm f = recv_cm g -> 
    f = g.
Proof.
    intros f g init_eq recv_eq.
    destruct f. destruct g. f_equal.
    - unfold init_cm in init_eq. unfold cm_init in init_eq.
      exact init_eq.
    - unfold recv_cm in recv_eq. unfold cm_recv in recv_eq.
      exact recv_eq.
Qed.

Lemma is_eq_cm_init  
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} :
    forall (f g : ContractMorphism C C'),
    (init_inputs C C' (init_cm f)) = (init_inputs C C' (init_cm g)) -> 
    (init_outputs C C' (init_cm f)) = (init_outputs C C' (init_cm g)) -> 
    init_cm f = init_cm g.
Proof.
    intros f g. destruct f. destruct g. simpl.
    destruct cm_init0. destruct cm_init1. simpl. 
    intros inputs_eq outputs_eq. subst. f_equal.
    apply proof_irrelevance.
Qed.

Lemma is_eq_cm_recv 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} :
    forall (f g : ContractMorphism C C'),
    (recv_inputs C C' (recv_cm f)) = (recv_inputs C C' (recv_cm g)) -> 
    (recv_outputs C C' (recv_cm f)) = (recv_outputs C C' (recv_cm g)) -> 
    recv_cm f = recv_cm g.
Proof.
    intros f g. destruct f. destruct g. simpl.
    destruct cm_recv0. destruct cm_recv1. simpl.
    intros inputs_eq outputs_eq. subst. f_equal.
    apply proof_irrelevance.
Qed.

End EqualityOfMorphisms.


Section MorphismComposition.

Lemma compose_commutes_init 
        { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
        `{Serializable Msg}    `{Serializable Setup}    `{Serializable State}    `{Serializable Error}
        `{Serializable Msg'}   `{Serializable Setup'}   `{Serializable State'}   `{Serializable Error'}
        `{Serializable Msg''}  `{Serializable Setup''}  `{Serializable State''}  `{Serializable Error''}
        { C : Contract Setup Msg State Error } 
        { C' : Contract Setup' Msg' State' Error' }
        { C'' : Contract Setup'' Msg'' State'' Error'' } 
    (g : ContractMorphism C' C'')
    (f : ContractMorphism C  C') :
    init_morphs_commute 
        C.(init) 
        C''.(init)
        (compose (init_inputs  C' C'' (init_cm g)) (init_inputs  C C' (init_cm f)))
        (compose (init_outputs C' C'' (init_cm g)) (init_outputs C C' (init_cm f))).
Proof.
    unfold init_morphs_commute. intro. simpl.
    rewrite (init_commutes C' C'' (init_cm g)).
    rewrite (init_commutes C C' (init_cm f)). 
    reflexivity.
Qed.

Lemma compose_commutes_recv
        { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
        `{Serializable Msg}    `{Serializable Setup}    `{Serializable State}    `{Serializable Error}
        `{Serializable Msg'}   `{Serializable Setup'}   `{Serializable State'}   `{Serializable Error'}
        `{Serializable Msg''}  `{Serializable Setup''}  `{Serializable State''}  `{Serializable Error''}
        { C : Contract Setup Msg State Error } 
        { C' : Contract Setup' Msg' State' Error' }
        { C'' : Contract Setup'' Msg'' State'' Error'' } 
    (g : ContractMorphism C' C'')
    (f : ContractMorphism C  C') :
    recv_morphs_commute 
        C.(receive)
        C''.(receive)
        (compose (recv_inputs  C' C'' (recv_cm g)) (recv_inputs  C C' (recv_cm f)))
        (compose (recv_outputs C' C'' (recv_cm g)) (recv_outputs C C' (recv_cm f))).
Proof.
    unfold recv_morphs_commute. intro. simpl.
    rewrite (recv_commutes C' C'' (recv_cm g)). 
    rewrite (recv_commutes C C' (recv_cm f)).
    reflexivity.
Qed.

Definition composition_cm 
        { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
        `{Serializable Msg}    `{Serializable Setup}    `{Serializable State}    `{Serializable Error}
        `{Serializable Msg'}   `{Serializable Setup'}   `{Serializable State'}   `{Serializable Error'}
        `{Serializable Msg''}  `{Serializable Setup''}  `{Serializable State''}  `{Serializable Error''}
        { C : Contract Setup Msg State Error } 
        { C' : Contract Setup' Msg' State' Error' }
        { C'' : Contract Setup'' Msg'' State'' Error'' } 
    (g : ContractMorphism C' C'')
    (f : ContractMorphism C  C') : ContractMorphism C C'' := 
    let compose_init := {|
        init_inputs  := compose (init_inputs  C' C'' (init_cm g)) (init_inputs  C C' (init_cm f)) ;
        init_outputs := compose (init_outputs C' C'' (init_cm g)) (init_outputs C C' (init_cm f)) ;
        (* proof of commutativity *)
        init_commutes := compose_commutes_init g f ;
    |} in 
    let compose_recv := {|
        recv_inputs  := compose (recv_inputs  C' C'' (recv_cm g)) (recv_inputs  C C' (recv_cm f)) ;
        recv_outputs := compose (recv_outputs C' C'' (recv_cm g)) (recv_outputs C C' (recv_cm f)) ;
        (* proof of commutativity *)
        recv_commutes := compose_commutes_recv g f ;
    |} in 
    {|
        cm_init := compose_init ;
        cm_recv := compose_recv ;
    |}.


(* Composition with the Identity morphism is trivial *)
Proposition composition_id_cm_left 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} :
    forall (f : ContractMorphism C C'), 
    (composition_cm (id_cm C') f) = f.
Proof.
    intros. unfold composition_cm. unfold id_cm. simpl.
    apply is_eq_cm; simpl.
    -   apply (is_eq_cm_init (composition_cm (id_cm C') f) f); auto.
    -   apply (is_eq_cm_recv (composition_cm (id_cm C') f) f); auto.
Qed.

Proposition composition_id_cm_right 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} :
    forall (f : ContractMorphism C C'), 
    (composition_cm f (id_cm C)) = f.
Proof.
    intros. unfold composition_cm. unfold id_cm. simpl.
    apply is_eq_cm; simpl. 
    + apply (is_eq_cm_init (composition_cm f (id_cm C)) f); auto.
    + apply (is_eq_cm_recv (composition_cm f (id_cm C)) f); auto.
Qed.

(* Composition is Associative *)
Proposition composition_assoc_cm 
        { Setup Setup' Setup'' Setup''' 
        Msg   Msg'   Msg''   Msg''' 
        State State' State'' State''' 
        Error Error' Error'' Error''' : Type }
        `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        `{Serializable Msg''} `{Serializable Setup''} `{Serializable State''} `{Serializable Error''}
        `{Serializable Msg'''} `{Serializable Setup'''} `{Serializable State'''} `{Serializable Error'''}
        { C : Contract Setup Msg State Error } 
        { C' : Contract Setup' Msg' State' Error' }
        { C'' : Contract Setup'' Msg'' State'' Error'' }
        { C''' : Contract Setup''' Msg''' State''' Error''' } :
    forall 
        (f : ContractMorphism C C') 
        (g : ContractMorphism C' C'') 
        (h : ContractMorphism C'' C'''), 
    composition_cm h (composition_cm g f) =
    composition_cm (composition_cm h g) f.
Proof.
    intros.
    unfold composition_cm. simpl. apply is_eq_cm.
    +   apply 
        (is_eq_cm_init 
            (composition_cm h (composition_cm g f))
            (composition_cm (composition_cm h g) f)); auto.
    +   apply 
        (is_eq_cm_recv 
            (composition_cm h (composition_cm g f))
            (composition_cm (composition_cm h g) f)); auto.
Qed.

End MorphismComposition.


Section SimpleContractMorphism.
(* contract morphisms can be constructed by *)

Definition simple_cm_construct 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'}
    (msg_morph   : Msg   -> Msg')
    (setup_morph : Setup -> Setup')
    (state_morph : State -> State')
    (* TODO plus some coherence conditions *)
    : ContractMorphism C1 C2 := todo "".

End SimpleContractMorphism.

Section ContractMorphismLift.
Context 
    (* we can lift a morphism of contracts, parameterized by the morphpism f and the address of C1 *)
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'}
    {f : ContractMorphism C1 C2}
    (* f must be decomposable as follows *)
    {msg_morph   : Msg   -> Msg'}
    {setup_morph : Setup -> Setup'}
    {state_morph : State -> State'}
    {f_decomposable : f = simple_cm_construct msg_morph setup_morph state_morph}.

(* TODO *)
Definition wc_dec_eq : forall w1 w2 : WeakContract, {w1 = w2} + {w1 <> w1} := todo "".
Declare Scope wc_scope.
Delimit Scope wc_scope with wc.
Bind Scope wc_scope with WeakContract.
Infix "=?" := wc_dec_eq (at level 70) : wc_scope.

(* calls into C1 are transformed into calls into C2
   deployment of C1 is transformed to deployment of C2 *)
Definition action_morphism (native_env : Environment) (a : Action) : Action := {| 
    act_origin := act_origin a ;
    act_from := act_from a ;
    act_body := 
        match act_body a with 
        (* contract calls into C1 change to calls into C2 *)
        | act_call to amt msg => 
            match env_contracts native_env to with 
            | Some wc => 
                if (wc =? contract_to_weak_contract C1)%wc
                then act_call to amt (serialize_function msg_morph msg)
                else act_body a
            | None => act_body a
            end
        (* we deploy C2 instead of C1 *)
        | act_deploy amt c setup => 
            if (c =? contract_to_weak_contract C1)%wc
            then act_deploy amt (contract_to_weak_contract C2) (serialize_function setup_morph setup)
            else act_body a
        (* all amounts stay the same, so we do not change transfers *)
        | act_transfer _ _ => act_body a 
        end
|}.

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

Record ChainStateMorphism (cstate1 cstate2 : ChainState) := 
    build_chainstate_morphism {
        env_morph   : EnvironmentMorphism cstate1 cstate2 ;
        queue_morph : chain_state_queue cstate2 = 
                      List.map (action_morphism cstate1) (chain_state_queue cstate1) ;
    }.

(* given a bstate, construct one over f that will (trivially) yield a ChainStateMorphism *)
Definition bstate_transform_step (bstate : ChainState) : ChainState := 
        let env := {| 
            (* the same as bstate *)
            env_chain := env_chain bstate ; 
            (* the same as bstate *)
            env_account_balances := env_account_balances bstate ; 
            (* the contracts are transformed via the contract morphism *)
            env_contracts := fun a =>
                match env_contracts bstate a with 
                | Some wc => 
                    if (wc =? contract_to_weak_contract C1)%wc 
                    then Some (contract_to_weak_contract C2)
                    else Some wc 
                | None => None
                end ;
            (* the contract states are transformed via the contract morphism *)
            env_contract_states := fun a => 
                match env_contracts bstate a with 
                | Some wc => 
                    if (wc =? contract_to_weak_contract C1)%wc 
                    then (option_fun (serialize_function state_morph)) (env_contract_states bstate a)
                    else env_contract_states bstate a
                | None => env_contract_states bstate a
                end ;
        |} in
        (* we just use the queue again from bstate1' *)
        let queue := List.map (action_morphism bstate) (chain_state_queue bstate) in 
        (* return the new cstate *)
        {| chain_state_env := env ; chain_state_queue := queue ; |}.

(* the chain_eq' component of an EnvironmentMorphism *)
Lemma env_morph_step_chain_eq (bstate1 : ChainState) : 
        let bstate2 := bstate_transform_step bstate1 in
        env_chain bstate1 = env_chain bstate2.
Proof. auto. Qed.

(* the account_balances_eq' component of an EnvironmentMorphism *)
Definition env_morph_step_balances (bstate1 : ChainState) : 
    let bstate2 := bstate_transform_step bstate1 in
    forall a, env_account_balances bstate1 a = env_account_balances bstate2 a.
Proof. auto. Qed.

(* the contract_morphisms component of an EnvironmentMorphism *)
Definition env_morph_step_contracts (bstate1 : ChainState) :  
    let bstate2 := bstate_transform_step bstate1 in
    forall a, 
        env_contracts bstate2 a = 
        match env_contracts bstate1 a with 
        | Some wc => 
            if (wc =? contract_to_weak_contract C1)%wc 
            then Some (contract_to_weak_contract C2) 
            else Some wc
        | None => None 
        end.
Proof. 
    intros. 
    unfold bstate2.
    unfold bstate_transform_step. 
    simpl. reflexivity.
Qed.

Definition env_morph_step_states (bstate1 : ChainState) : 
    let bstate2 := bstate_transform_step bstate1 in
    forall a,
        env_contract_states bstate2 a = 
        match env_contracts bstate1 a with 
        | Some wc => 
            if (wc =? contract_to_weak_contract C1)%wc 
            then (option_fun (serialize_function state_morph)) (env_contract_states bstate1 a)
            else env_contract_states bstate1 a
        | None => env_contract_states bstate1 a
        end.
Proof.
    intros.
    unfold bstate2.
    unfold bstate_transform_step.
    simpl. reflexivity.
Qed.

Definition env_morph_step (bstate1 : ChainState) : 
    let bstate2 := bstate_transform_step bstate1 in
    EnvironmentMorphism bstate1 bstate2 := {| 
        chain_eq' := env_morph_step_chain_eq bstate1 ; 
        account_balances_eq' := env_morph_step_balances bstate1 ; 
        contracts_morph := env_morph_step_contracts bstate1 ; 
        contract_states_morph := env_morph_step_states bstate1 ;
    |}.    

Lemma queue_morphism_step (bstate1 : ChainState) : 
    let bstate2 := bstate_transform_step bstate1 in  
    chain_state_queue bstate2
    = List.map (action_morphism bstate1) (chain_state_queue bstate1).
Proof. auto. Qed.

Definition chainstate_morphism_step (bstate1' : ChainState) : 
    let bstate2' := bstate_transform_step bstate1' in  
    (ChainStateMorphism bstate1' bstate2') := {|  
        env_morph   := env_morph_step bstate1' ; 
        queue_morph := queue_morphism_step bstate1' |}.





(* construct the step from bstate2 to bstate2' *)
Lemma chainstate_morphism_empty_queue 
    (cstate1 cstate2 : ChainState) 
    (m : ChainStateMorphism cstate1 cstate2) : 
    chain_state_queue cstate1 = nil -> chain_state_queue cstate2 = nil.
Proof. 
    intro. rewrite (queue_morph cstate1 cstate2 m). rewrite H7. simpl. reflexivity.
Qed.

Lemma chainstate_morphism_next_block_valid
    (cstate1 cstate2 : ChainState) 
    (m : ChainStateMorphism cstate1 cstate2)
    (header : BlockHeader) : 
    IsValidNextBlock header cstate1 -> IsValidNextBlock header cstate2.
Proof.
    intro. destruct H7.
    assert (env_chain cstate1 = env_chain cstate2); 
    try exact (chain_eq' cstate1 cstate2 (env_morph cstate1 cstate2 m)).
    rewrite H7 in valid_height.
    rewrite H7 in valid_slot.
    rewrite H7 in valid_finalized_height. 
    exact (build_is_valid_next_block header cstate2 valid_height valid_slot valid_finalized_height valid_creator valid_reward).
Qed.

Lemma chainstate_morphism_no_acts_from_accounts
    (bstate1' : ChainState) : 
    let bstate2' := bstate_transform_step bstate1' in  
    Forall act_is_from_account (chain_state_queue bstate1') -> 
    Forall act_is_from_account (chain_state_queue bstate2').
Proof.
    intros. 
    unfold bstate2'.
    simpl.
    induction (chain_state_queue bstate1').
    - auto.
    - simpl. apply Forall_cons_iff in H7. destruct H7. apply IHl in H8.
        apply Forall_cons.
        + exact H7.
        + exact H8.
Qed.

Lemma chainstate_morphism_origin_eq_from
    (bstate1' : ChainState) : 
    let bstate2' := bstate_transform_step bstate1' in  
    Forall act_origin_is_eq_from (chain_state_queue bstate1') -> 
    Forall act_origin_is_eq_from (chain_state_queue bstate2').
Proof.
    intros. 
    unfold bstate2'.
    simpl.
    induction (chain_state_queue bstate1').
    - auto.
    - simpl. apply Forall_cons_iff in H7. destruct H7. apply IHl in H8.
        apply Forall_cons.
        + exact H7.
        + exact H8.
Qed.

Lemma chainstate_morphism_step_env_chain_eq
    (bstate1 bstate2 : ChainState)
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    env_chain bstate1 = env_chain bstate2.
Proof.
    exact (chain_eq' bstate1 bstate2 (env_morph bstate1 bstate2 c_morph)).
Qed.

Lemma env_equiv_carries_over_env_morphism 
    (bstate1 bstate1' bstate2 bstate2' : Environment)
    (e_morph  : EnvironmentMorphism bstate1  bstate2)
    (e_morph' : EnvironmentMorphism bstate1' bstate2') :
    EnvironmentEquiv bstate1 bstate1' -> 
    EnvironmentEquiv bstate2 bstate2'.
Proof.
    intro EE1. destruct EE1. 
    (* prove chain_eq *)
    assert (env_chain bstate2 = env_chain bstate2').
    rewrite (chain_eq' bstate1  bstate2  e_morph)  in chain_eq.
    rewrite (chain_eq' bstate1' bstate2' e_morph') in chain_eq.
    exact chain_eq.
    (* prove account_balances_eq *)
    assert (forall a, env_account_balances bstate2 a = env_account_balances bstate2' a).
    intro.
    rewrite <- (account_balances_eq' bstate1  bstate2  e_morph  a).
    rewrite <- (account_balances_eq' bstate1' bstate2' e_morph' a).
    exact (account_balances_eq a).
    (* prove contracts_eq *)
    assert (forall a, env_contracts bstate2 a = env_contracts bstate2' a).
    intro.
    rewrite (contracts_morph bstate1  bstate2  e_morph  a).
    rewrite (contracts_morph bstate1' bstate2' e_morph' a).
    rewrite <- (contracts_eq a). reflexivity.
    (* prove contract_states_eq *)
    assert (forall a, env_contract_states bstate2 a = env_contract_states bstate2' a).
    intro.
    rewrite (contract_states_morph bstate1  bstate2  e_morph  a).
    rewrite (contract_states_morph bstate1' bstate2' e_morph' a).
    rewrite <- (contracts_eq a).
    rewrite <- (contract_states_eq a). reflexivity.
    (* construct the result *)
    exact {| chain_eq := H7 ; 
             account_balances_eq := H8 ;
             contracts_eq := H9 ;
             contract_states_eq := H10 ; |}.
Qed.

(* then prove that adding a block preserves the cstate morphism *)
Lemma env_morph_preserved_under_adding_block 
    (bstate1 bstate2 : ChainState)
    (e_morph : EnvironmentMorphism bstate1 bstate2)
    (header : BlockHeader) : 
    let bstate1' := (add_new_block_to_env header bstate1) in 
    let bstate2' := (add_new_block_to_env header bstate2) in 
    EnvironmentMorphism bstate1' bstate2'.
Proof.
    intros.
    (* prove chain_eq' *)
    assert (env_chain bstate1' = env_chain bstate2'). auto.
    (* prove account_balances_eq' *)
    assert (forall a, 
        env_account_balances bstate1' a = env_account_balances bstate2' a).
    unfold bstate1'. unfold bstate2'.
    unfold add_new_block_to_env. 
    intro. simpl.
    rewrite <- (account_balances_eq' bstate1 bstate2 e_morph a). reflexivity.
    (* prove contracts_morph *)
    assert (forall a, 
        env_contracts bstate2' a = 
        match env_contracts bstate1' a with 
        | Some wc => 
            if (wc =? contract_to_weak_contract C1)%wc 
            then Some (contract_to_weak_contract C2) 
            else Some wc
        | None => None 
        end). 
    unfold bstate1'. unfold bstate2'.
    unfold add_new_block_to_env. 
    intro. simpl. 
    exact (contracts_morph bstate1 bstate2 e_morph a).
    (* prove contract_states_morph *)
    assert (forall a, 
        env_contract_states bstate2' a = 
        match env_contracts bstate1' a with 
        | Some wc => 
            if (wc =? contract_to_weak_contract C1)%wc 
            then (option_fun (serialize_function state_morph)) (env_contract_states bstate1' a)
            else env_contract_states bstate1' a
        | None => env_contract_states bstate1' a
        end).
    unfold bstate1'. unfold bstate2'.
    unfold add_new_block_to_env. 
    intro. simpl. 
    exact (contract_states_morph bstate1 bstate2 e_morph a).
    (* construct the result *)
    exact {| chain_eq' := H7 ; 
             account_balances_eq' := H8 ;
             contracts_morph := H9 ;
             contract_states_morph := H10 ; |}.
Qed.

Lemma chainstate_morphism_new_env_equiv_add_block
    (bstate1 bstate2 bstate1' : ChainState)
    (e_morph : EnvironmentMorphism bstate1 bstate2) 
    (header : BlockHeader) : 
    let bstate2' := bstate_transform_step bstate1' in  
    EnvironmentEquiv bstate1' (add_new_block_to_env header bstate1) -> 
    EnvironmentEquiv bstate2' (add_new_block_to_env header bstate2).
Proof.
    intros bstate2' EE1.
    assert (EnvironmentMorphism (add_new_block_to_env header bstate1) (add_new_block_to_env header bstate2)); 
    try exact (env_morph_preserved_under_adding_block bstate1 bstate2 e_morph header).
    assert (EnvironmentMorphism bstate1' bstate2');
    try exact (env_morph_step bstate1').
    exact (symmetry (env_equiv_carries_over_env_morphism
        (add_new_block_to_env header bstate1) bstate1'
        (add_new_block_to_env header bstate2) bstate2'
        H7 H8  (symmetry EE1))).
Qed.

Lemma permutation_preserved_over_map {A B : Type} : 
    forall (g : A -> B) (l1 l2 : list A),
    Permutation l1 l2 -> 
    Permutation (List.map g l1) (List.map g l2).
Proof.
    intros.
    induction H7.
    - auto.
    - simpl. exact (perm_skip (g x) IHPermutation).
    - simpl. exact (perm_swap (g x) (g y) (map g l)).
    - exact (perm_trans IHPermutation1 IHPermutation2).
Qed.

Lemma chainstate_morphism_new_permuted 
    (bstate1 bstate2 bstate1' : ChainState)
    (env_equiv : EnvironmentEquiv bstate1 bstate1') 
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    let bstate2' := bstate_transform_step bstate1' in 
    Permutation (chain_state_queue bstate1) (chain_state_queue bstate1') -> 
    Permutation (chain_state_queue bstate2) (chain_state_queue bstate2').
Proof.
    intros.
    simpl. rewrite (queue_morph bstate1 bstate2 c_morph).
    assert (action_morphism bstate1 = action_morphism bstate1').
    - apply functional_extensionality. intro a.
        unfold action_morphism. f_equal.
        destruct (act_body a); auto.
        rewrite (contracts_eq bstate1 bstate1' env_equiv to). auto.
    - rewrite <- H8. 
        exact (permutation_preserved_over_map (action_morphism bstate1) (chain_state_queue bstate1) (chain_state_queue bstate1') H7).
Qed.

Lemma chainstate_morphism_new_env_equiv_permute 
    (bstate1 bstate2 bstate1' : ChainState)
    (e_morph : EnvironmentMorphism bstate1 bstate2) : 
    let bstate2' := bstate_transform_step bstate1' in 
    EnvironmentEquiv bstate1' bstate1 -> 
    EnvironmentEquiv bstate2' bstate2.
Proof.
    intros bstate2' EE1.
    exact 
    (symmetry
    (env_equiv_carries_over_env_morphism 
        bstate1 bstate1' bstate2 bstate2' 
        e_morph
        (env_morph_step bstate1')
        (symmetry EE1))).
Qed.

Lemma chainstate_morphism_new_queue_prev 
    (bstate1 bstate2 : ChainState)
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    forall (act : Action) (acts : list Action),
    chain_state_queue bstate1 = act :: acts -> 
    let new_act := action_morphism bstate1 act in 
    let new_acts := List.map (action_morphism bstate1) acts in
    chain_state_queue bstate2 = new_act :: new_acts.
Proof.
    intros.
    unfold new_act. unfold new_acts.
    rewrite (queue_morph bstate1 bstate2 c_morph). 
    rewrite H7.
    auto.
Qed.

Lemma chainstate_morphism_new_act_eval_true 
    (bstate1 bstate2 bstate1' : ChainState)
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    forall (act : Action) (new_acts : list Action),
    let act' := action_morphism bstate1 act in 
    let new_acts' := List.map (action_morphism bstate1) new_acts in 
    let bstate2' := bstate_transform_step bstate1' in  
    ActionEvaluation bstate1 act  bstate1' new_acts ->
    ActionEvaluation bstate2 act' bstate2' new_acts'.
Proof. Admitted.

(* TODO transform bstate back *)
Lemma act_eval_pullback 
    (bstate1 bstate2 : ChainState) 
    (c_morph : ChainStateMorphism bstate1 bstate2)
    (bstate : Environment) (act : Action) (new_acts : list Action) : 
    let act' := action_morphism bstate1 act in 
    ActionEvaluation bstate2 act' bstate new_acts ->
    ActionEvaluation bstate1 act  bstate new_acts.
Proof. Admitted.

Lemma chainstate_morphism_new_act_eval_false
    (bstate1 bstate2 : ChainState) 
    (c_morph : ChainStateMorphism bstate1 bstate2)
    (act : Action) : 
    let act' := action_morphism bstate1 act in 
    (forall bstate new_acts, ActionEvaluation bstate1 act  bstate new_acts -> False) ->
    (forall bstate new_acts, ActionEvaluation bstate2 act' bstate new_acts -> False).
Proof.
    intros.
    apply (H7 bstate new_acts).
    apply (act_eval_pullback bstate1 bstate2 c_morph bstate act new_acts).
    exact X.
Qed.

Lemma list_map_concat {A B : Type} {g : A -> B} : 
    forall (l1 l2 : list A), 
    List.map g (l1 ++ l2) = (List.map g l1) ++ (List.map g l2).
Proof.
    intros. 
    induction l1.
    - auto.
    - assert (((a :: l1) ++ l2) = a :: (l1 ++ l2)); auto. rewrite H7.
        assert (forall a' k, map g (a' :: k) = (g a') :: map g k); auto. 
        rewrite (H8 a (l1 ++ l2)).
        rewrite (H8 a l1).
        assert (forall (a':B) k1 k2, (a' :: k1) ++ k2 = a' :: (k1 ++ k2)); auto.
        rewrite (H9 (g a) (map g l1) (map g l2)).
        rewrite IHl1. reflexivity.
Qed.

Lemma chainstate_morphism_new_queue_next
    (bstate1 bstate2 bstate1' : ChainState)
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    forall (new_acts : list Action) (acts : list Action),
    chain_state_queue bstate1' = new_acts ++ acts -> 
    let bstate2'  := bstate_transform_step bstate1' in  
    let new_acts' := List.map (action_morphism bstate1) new_acts in 
    let acts'     := List.map (action_morphism bstate1) acts in
    chain_state_queue bstate2' = new_acts' ++ acts'.
Proof.
    intros.
    unfold bstate2'.
    unfold bstate_transform_step. simpl.
    unfold new_acts'. unfold acts'. rewrite H7.
    rewrite <- (list_map_concat new_acts acts).
    (assert (action_morphism bstate1' = action_morphism bstate1)).
    - apply functional_extensionality. intro x.
        destruct x.
        unfold action_morphism. simpl. f_equal.
        destruct act_body; auto.
        admit.
    - rewrite H8. reflexivity.
Admitted.

Lemma chainstate_morphism_queue_next_action_invalid
    (bstate1 bstate2 bstate1' : ChainState) 
    (acts : list Action): 
    let bstate2' := bstate_transform_step bstate1' in  
    let acts' := List.map (action_morphism bstate1) acts in 
    chain_state_queue bstate1' = acts ->
    chain_state_queue bstate2' = acts'.
Proof. Admitted.

Lemma chainstate_morphism_from_acct
    (bstate : ChainState) (act : Action) : 
    act_is_from_account act -> 
    act_is_from_account (action_morphism bstate act).
Proof.
    unfold act_is_from_account.
    intros.
    assert (act_from (action_morphism bstate act) = act_from act).
    - unfold action_morphism. auto.
    - rewrite H8. exact H7.
Qed.

Definition step_transform_step 
    (bstate1 bstate2 bstate1' : ChainState)
    (c_morph : ChainStateMorphism bstate1 bstate2) 
    (step : ChainStep bstate1 bstate1') : 
    let bstate2' := bstate_transform_step bstate1' in  
    (ChainStep bstate2 bstate2') :=
    let bstate2' := bstate_transform_step bstate1' in  
    let c_morph' := chainstate_morphism_step bstate1' in 
    match step with 
    | step_block _ _ header prev_queue_empty next_block_valid no_acts_from_accounts origin_eq_from 
        env_equiv  => 
        (* modified header *)
        let header' := header in 
        (* modified prev_queue_empty *)
        let prev_queue_empty' := 
            chainstate_morphism_empty_queue bstate1 bstate2 c_morph prev_queue_empty in 
        (* modified next_block_valid *)
        let next_block_valid' := 
            chainstate_morphism_next_block_valid bstate1 bstate2 c_morph header next_block_valid in 
        (* modified no_acts_from_accounts *)
        let no_acts_from_accounts' := 
            chainstate_morphism_no_acts_from_accounts bstate1' no_acts_from_accounts in
        (* modified origin_eq_from *)
        let origin_eq_from' :=
            chainstate_morphism_origin_eq_from bstate1' origin_eq_from in 
        (* modified env_equiv *)
        let env_equiv' :=
            chainstate_morphism_new_env_equiv_add_block bstate1 bstate2 bstate1' 
            (env_morph bstate1 bstate2 c_morph) header env_equiv in
        (* the new step_block *)
        step_block bstate2 bstate2'
            header' prev_queue_empty' next_block_valid' no_acts_from_accounts' 
            origin_eq_from' env_equiv'
    | step_action _ _ act acts new_acts queue_prev act_eval_true queue_next => 
        (* modified act *)
        let act' := action_morphism bstate1 act in 
        (* modified acts *)
        let acts' := 
            List.map (action_morphism bstate1) acts in 
        (* modified new_acts *)
        let new_acts' := 
            List.map (action_morphism bstate1) new_acts in 
        (* modified queue_prev *)
        let queue_prev' := 
            chainstate_morphism_new_queue_prev bstate1 bstate2 c_morph act acts queue_prev in 
        (* modified act_eval_true *)
        let act_eval_true' := 
            chainstate_morphism_new_act_eval_true bstate1 bstate2 bstate1' c_morph act new_acts act_eval_true in 
        (* modified queue_next *)
        let queue_next' := 
            chainstate_morphism_new_queue_next bstate1 bstate2 bstate1' c_morph new_acts acts queue_next in
        (* the new step_block *)
        step_action bstate2 bstate2' act' acts' new_acts' queue_prev' act_eval_true' queue_next'
    | step_action_invalid _ _ act acts env_equiv queue_prev queue_next from_acct actn_eval_false => 
        (* modified act *)
        let act' := action_morphism bstate1 act in 
        (* modified acts *)
        let acts' := 
            List.map (action_morphism bstate1) acts in 
        (* modified env_equiv *)
        let env_equiv' := 
            chainstate_morphism_new_env_equiv_permute bstate1 bstate2 bstate1' 
            (env_morph bstate1 bstate2 c_morph) env_equiv in 
        (* modified queue_prev *)
        let queue_prev' := 
            chainstate_morphism_new_queue_prev bstate1 bstate2 c_morph act acts queue_prev in 
        (* modified queue_next *)
        let queue_next' := 
            chainstate_morphism_queue_next_action_invalid bstate1 bstate2 bstate1' acts queue_next in 
        (* modified from_acct *)
        let from_acct' := 
            chainstate_morphism_from_acct bstate1 act from_acct in 
        (* modified actn_eval_false *)
        let actn_eval_false' := 
            chainstate_morphism_new_act_eval_false bstate1 bstate2 c_morph act actn_eval_false in 
        (* the new step_block *)
        step_action_invalid bstate2 bstate2' act' acts' env_equiv' queue_prev' queue_next' from_acct' actn_eval_false'
    | step_permute _ _ env_equiv permuted => 
        (* modified env_equiv *)
        let env_equiv' := 
            chainstate_morphism_new_env_equiv_permute bstate1 bstate2 bstate1' 
            (env_morph bstate1 bstate2 c_morph) env_equiv in 
        (* modified permutation *)
        let permuted' := 
            chainstate_morphism_new_permuted bstate1 bstate2 bstate1' (symmetry env_equiv) c_morph permuted in 
        (* the new step_block *)
        step_permute bstate2 bstate2' env_equiv' permuted' 
    end.

Lemma empty_chainstate_morphism : ChainStateMorphism empty_state empty_state. 
Proof.
    apply build_chainstate_morphism; auto.
    apply build_env_morphism; auto.
Qed.

Definition caddr_implication_step (bstate1' : ChainState) (caddr : Address) :
    let bstate2' := bstate_transform_step bstate1' in  
    env_contracts bstate1' caddr = Some (C1 : WeakContract) -> 
    env_contracts bstate2' caddr = Some (C2 : WeakContract).
Proof.
    intros. unfold bstate2'.
    unfold bstate_transform_step. simpl.
    rewrite H7. 
    destruct (C1 =? C1)%wc; auto.
    contradiction.
Qed.
    
(* Theorem: A contract morphism can be lifted into a morphism of ChainStates *)
Theorem cm_lift :
    forall  bstate1 caddr (trace : ChainTrace empty_state bstate1),
    exists  (* a new bstate related to the old *)
            (bstate2 : ChainState) 
            (bstate_morph : ChainStateMorphism bstate1 bstate2)
            (* a new trace related to the old *)
            (trace2 : ChainTrace empty_state bstate2),
            (* with C2 swapped out for C1 *)
            env_contracts bstate1 caddr = Some (C1 : WeakContract) -> 
            env_contracts bstate2 caddr = Some (C2 : WeakContract).
Proof.
    (* we induct over the trace *)
    intros.
    remember empty_state eqn:genesis_empty. induction trace.
    - rewrite genesis_empty. 
        exists empty_state. exists empty_chainstate_morphism. 
        exists ChainedList.clnil.
        intro. assert (env_contracts empty_state caddr = None); auto. 
        rewrite H8 in H7. congruence.
    - apply IHtrace in genesis_empty. clear IHtrace.
        (* destruct IHtrace1 as [bstate2 H']. auto. admit. *)
        destruct genesis_empty as [bstate2 genesis_empty]. 
        destruct genesis_empty as [bstate_morph genesis_empty]. 
        destruct genesis_empty as [trace2 addr_implication].
        (* construct the new bstate and trace *)
        set (bstate2' := bstate_transform_step to).
        set (l' := step_transform_step mid bstate2 to bstate_morph l).
        set (trace2' := ChainedList.snoc trace2 l').
        (* construct the relationships *)
        set (bstate_morph' := chainstate_morphism_step to).
        set (caddr_impl := caddr_implication_step to caddr).
        exists bstate2'. 
        exists bstate_morph'. 
        exists trace2'.
        exact caddr_impl.
Qed.

End ContractMorphismLift.

Section ContractMorphismLiftCompose.

(* Some results about the lifted morphism *)
(*
Lemma id_lifts_to_id 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : todo "".
Proof. exact (todo ""). Qed.

Lemma morphisms_lift_compose
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : todo "".

Lemma inj_lifts_to_inj
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : todo "".

Lemma surj_lifts_to_surj
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : todo "".
*)

End ContractMorphismLiftCompose.


Section Isomorphisms.

Definition is_iso {A B : Type} (f : A -> B) (g : B -> A) : Prop := 
    compose g f = @id A /\ compose f g = @id B.

Lemma is_iso_reflexive {A B : Type} (f : A -> B) (g : B -> A) : 
    is_iso f g -> is_iso g f.
Proof. unfold is_iso. intro. destruct H. auto. Qed.

Definition is_iso_cm 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} 
    (f : ContractMorphism C C')
    (g : ContractMorphism C' C) : Prop := 
    composition_cm g f = id_cm C /\ 
    composition_cm f g = id_cm C'.

Definition contracts_isomorphic 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        (C : Contract Setup Msg State Error) (C' : Contract Setup' Msg' State' Error') := 
    exists (f : ContractMorphism C C') (g : ContractMorphism C' C),
    is_iso_cm f g.

Lemma iso_cm_components 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} :
    forall 
        (f : ContractMorphism C C')
        (g : ContractMorphism C' C),
    is_iso (init_inputs  C C' (init_cm f)) (init_inputs  C' C (init_cm g)) /\
    is_iso (init_outputs C C' (init_cm f)) (init_outputs C' C (init_cm g)) /\
    is_iso (recv_inputs  C C' (recv_cm f)) (recv_inputs  C' C (recv_cm g)) /\
    is_iso (recv_outputs C C' (recv_cm f)) (recv_outputs C' C (recv_cm g)) 
    <->
    is_iso_cm f g.
Proof.
    intros f g. unfold is_iso. unfold iff. split.
    -   intro E. 
        destruct E as [iso_i_inputs E'].
        destruct iso_i_inputs as [iso_i_inputs1 iso_i_inputs2].
        destruct E' as [iso_i_outputs E''].
        destruct iso_i_outputs as [iso_i_outputs1 iso_i_outputs2].
        destruct E'' as [iso_r_inputs iso_r_outputs].
        destruct iso_r_inputs as [iso_r_inputs1 iso_r_inputs2].
        destruct iso_r_outputs as [iso_r_outputs1 iso_r_outputs2].
        unfold is_iso_cm. unfold composition_cm. unfold id_cm. 
        unfold id_cm_init. unfold id_cm_recv. unfold id_morph. 
        split.
        +   apply is_eq_cm.
            * apply is_eq_cm_init; simpl.
                ** exact iso_i_inputs1. 
                ** exact iso_i_outputs1.
            * apply is_eq_cm_recv; simpl.
                ** exact iso_r_inputs1.
                ** exact iso_r_outputs1.
        +   apply is_eq_cm.
            *  apply is_eq_cm_init; simpl. 
                ** exact iso_i_inputs2. 
                ** exact iso_i_outputs2.
            *  apply is_eq_cm_recv; simpl.
                ** exact iso_r_inputs2.
                ** exact iso_r_outputs2. 
    -   unfold is_iso_cm. unfold composition_cm.  unfold id_cm. 
        unfold id_cm_init. unfold id_cm_recv. unfold id_morph.
        intro is_iso_H. destruct is_iso_H as [is_iso_H1 is_iso_H2].
        inversion is_iso_H1. inversion is_iso_H2.
        auto.
Qed.

Lemma iso_cm_reflexive
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'}
    (f : ContractMorphism C C')
    (g : ContractMorphism C' C) : 
    is_iso_cm f g -> 
    is_iso_cm g f.
Proof.
    intro. apply iso_cm_components in H7. 
    apply iso_cm_components. destruct H7.
    apply is_iso_reflexive in H7. split; try exact H7. destruct H8.
    apply is_iso_reflexive in H8. split; try exact H8. destruct H9.
    apply is_iso_reflexive in H9. split; try exact H9.
    apply is_iso_reflexive in H10. exact H10.
Qed.

Lemma composition_iso_cm 
        { Setup Setup' Setup'' Setup''' 
        Msg   Msg'   Msg''   Msg''' 
        State State' State'' State''' 
        Error Error' Error'' Error''' : Type }
        `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        `{Serializable Msg''} `{Serializable Setup''} `{Serializable State''} `{Serializable Error''}
        `{Serializable Msg'''} `{Serializable Setup'''} `{Serializable State'''} `{Serializable Error'''}
        { C : Contract Setup Msg State Error } 
        { C' : Contract Setup' Msg' State' Error' }
        { C'' : Contract Setup'' Msg'' State'' Error'' }
        { C''' : Contract Setup''' Msg''' State''' Error''' }
    (f : ContractMorphism C C')
    (g : ContractMorphism C' C'')
    (f' : ContractMorphism C' C)
    (g' : ContractMorphism C'' C') :
    is_iso_cm f f' -> 
    is_iso_cm g g' -> 
    is_iso_cm (composition_cm g f) (composition_cm f' g').
Proof.
    unfold is_iso_cm.
    intros iso_f iso_g. 
    destruct iso_f as [iso_f1 iso_f2].
    destruct iso_g as [iso_g1 iso_g2].
    split.
    -   rewrite composition_assoc_cm. 
        rewrite <- (composition_assoc_cm g g' f').
        rewrite iso_g1. rewrite (composition_id_cm_right f'). exact iso_f1.
    -   rewrite composition_assoc_cm.
        rewrite <- (composition_assoc_cm f' f g).
        rewrite iso_f2. rewrite (composition_id_cm_right g). exact iso_g2.
Qed.


(*  Results about isomorphisms 

    The following results show that :

    (1) deploying isomorphic contracts produces isomorphic environments, or a bisimulation of 
        environments
    (2) an equivalence of environments is preserved under ActionEvaluation, where equivalent actions 
        are paired via the isomorphism of environments

    Together, these results show that deploying isomorphic contracts results two separate chains, along with a bisimulation of chains. Functionally, then, the chains behave in equivalent ways.
*)

Definition weak_contracts_isomorphic (W1 W2 : option WeakContract) : Prop := todo "".
Definition serialized_state_isomorphic (s1 s2 : option SerializedValue) : Prop := todo "".

(* we define a (functional) equivalence of environments via a function : this is a bisimulation *)
Record EnvironmentBisimulation (e1 e2 : Environment) : Prop := {
    chain_eq : env_chain e1 = env_chain e2 ; 
    account_balances_eq :
        forall a, env_account_balances e1 a = env_account_balances e2 a;
    contracts_eq :
        forall a, weak_contracts_isomorphic (env_contracts e1 a) (env_contracts e2 a);
    contract_states_eq :
        forall a, serialized_state_isomorphic (env_contract_states e1 a) (env_contract_states e2 a);
}.
    
(* should rely on environment bisimulation *)
Record ChainStateBisimulation (b1 b2 : ChainState) : Prop := {
    env_eq' : EnvironmentBisimulation b1 b2 ; 
    queue_eq' : chain_state_queue b1 = chain_state_queue b2 ;
}.

(* every environment is a bisimulation of itself *)
Lemma env_equiv_then_bisimulation:
    forall e1 e2,
    EnvironmentEquiv e1 e2 -> 
    EnvironmentBisimulation e1 e2.
Proof. Admitted.

(* deploying isomorphic contracts preserves a bisimulation *)
Definition isomorphic_contracts_to_bisimulation
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} : 
    contracts_isomorphic C C' ->
    (* start with equivalent, reachable environments *)
    forall env1 env2, 
    reachable env1 ->
    reachable env2 ->
    EnvironmentBisimulation env1 env2 -> 
    forall env1' env2' act_deploy_C act_deploy_C' new_acts s s' amt,
    (* the environment we get by deploying C  *)
    ActionEvaluation env1 act_deploy_C env1' new_acts -> 
        act_deploy_C.(act_body) = act_deploy amt C s ->
    (* the environment we get by deploying C'  *)
    ActionEvaluation env2 act_deploy_C' env2' new_acts -> 
        act_deploy_C'.(act_body) = act_deploy amt C' s' ->
    (* the setups are equivalent under the isomorphism *)
    s = s' -> (* TODO *)
    (* they are deployed to the same address *)
    forall caddr caddr',
        env_contracts env1'  caddr  = Some (C  : WeakContract) -> 
        env_contracts env2' caddr' = Some (C' : WeakContract) ->
        caddr = caddr' ->
    (* they are deployed BY the same address (and origin) *)
    act_deploy_C.(act_from) = act_deploy_C'.(act_from) ->
    act_deploy_C.(act_origin) = act_deploy_C'.(act_origin) ->
    (* the isomorphisms f and g lift to a bisimulation of env' and env'' *)
    EnvironmentBisimulation env1' env2'
    := todo "".

(* if C and C' are isomorphic, then deploying  *)
(* base case *)
Lemma iso_cm_then_iso_env_init 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'} : 
    forall (f : ContractMorphism C C') (g : ContractMorphism C' C),
    is_iso_cm f g -> 
    (* for all reachable states *)
    forall env, reachable env -> 
    forall env' env'' act_deploy_C act_deploy_C' new_acts s amt,
    (* the environment we get by deploying C  *)
    ActionEvaluation env act_deploy_C  env'  new_acts -> 
        act_deploy_C.(act_body)  = act_deploy amt C  s ->
    (* the environment we get by deploying C'  *)
    ActionEvaluation env act_deploy_C' env'' new_acts -> 
        act_deploy_C'.(act_body) = act_deploy amt C' s ->
    (* they are deployed to the same address *)
    forall caddr caddr',
        env_contracts env'  caddr  = Some (C  : WeakContract) -> 
        env_contracts env'' caddr' = Some (C' : WeakContract) ->
        caddr = caddr' ->
    (* they are deployed BY the same address (and origin) *)
    act_deploy_C.(act_from) = act_deploy_C'.(act_from) ->
    act_deploy_C.(act_origin) = act_deploy_C'.(act_origin) ->
    (* the two environments are equivalent *)
    EnvironmentBisimulation env' env''.
Proof. Admitted.
(* get a witness that env bisimulates itself, apply function above *)

(* inductive step *)
Lemma iso_cm_then_iso_env_recv : 
    forall bstate1  bstate2,  EnvironmentBisimulation bstate1 bstate2 -> 
    forall bstate1' bstate2' act1 act2 new_acts,
        ActionEvaluation bstate1 act1 bstate1' new_acts -> 
        ActionEvaluation bstate2 act2 bstate2' new_acts -> 
        (* the act should be equivalent, not identical *)
        act1 = act2 -> (* TODO *)
        EnvironmentBisimulation bstate1' bstate2'.
Proof. Admitted.

(* Main result for isomorphisms *)
Theorem iso_cm_then_iso_bstate
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : 
    forall (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1),
    is_iso_cm f g -> 
    (* for all reachable states *)
    forall bstate, reachable bstate -> 
    forall bstate1 bstate2 (* the new blockchain states *)
           acts new_acts s amt (* queued actions, actions emitted by C1 and C2, setup, and amt *)
           act_deploy_C1 act_deploy_C2 (* the actions of deploying C1 and C2 *)
           actneval1 actneval2 (* the inhabitants of ActionEvaluation *)
           state_queue1 state_queue1' (* proof that the state queues evolve correctly *)
           state_queue2 state_queue2'
           cstep1 cstep2, (* the chainstep *)
    (* the bstate we get by deploying C  *)
    cstep1 = step_action bstate bstate1 act_deploy_C1 acts new_acts state_queue1 actneval1 state_queue1' -> 
    act_deploy_C1.(act_body) = act_deploy amt C1  s ->
    (* the bstate we get by deploying C'  *)
    cstep2 = step_action bstate bstate2 act_deploy_C2 acts new_acts state_queue2 actneval2 state_queue2' -> 
    act_deploy_C2.(act_body) = act_deploy amt C2 s ->
    (* they are deployed to the same address *)
    forall caddr1 caddr2,
        env_contracts bstate1 caddr1 = Some (C1 : WeakContract) -> 
        env_contracts bstate2 caddr2 = Some (C2 : WeakContract) ->
        caddr1 = caddr2 ->
    (* they are deployed BY the same address (and origin) *)
    act_deploy_C1.(act_from)   = act_deploy_C2.(act_from) ->
    act_deploy_C1.(act_origin) = act_deploy_C2.(act_origin) ->
    (* for any state reachable through env1, we have a corresponding isomorphic state reachable through env2 *)
    forall bstate1', reachable_through bstate1 bstate1' -> 
    exists bstate2', 
        reachable_through bstate2 bstate2' /\
        ChainStateBisimulation bstate1' bstate2'.
Proof. Admitted.


(* for any reachable state with C1 deployed, we have an isomorphic reachable state with C2 deployed at the same address *)
Definition iso_trace bstate bstate1 bstate2 :
    ChainTrace bstate bstate1 -> ChainTrace bstate bstate2 := todo "".

Definition iso_bstate (bstate1 bstate2 : ChainState) : Prop := todo "".

Theorem iso_cm_then_iso_bstate2 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : 
    contracts_isomorphic C1 C2 -> 
    (* forall reachable states *)
    forall bstate1 caddr (trace1 : ChainTrace empty_state bstate1), 
    reachable bstate1 -> 
    env_contracts bstate1 caddr = Some (C1 : WeakContract) -> 
    (* we can produce an isomorphic trace *)
    exists (bstate2 : ChainState) (trace2 : ChainTrace empty_state bstate2),
    env_contracts bstate2 caddr = Some (C2 : WeakContract) /\ 
    iso_bstate bstate1 bstate2 /\ (* todo : perhaps produce the isomorphism *)
    trace2 = iso_trace empty_state bstate1 bstate2 trace1.
Proof. Admitted.

End Isomorphisms.


Section Monomorphisms.
Definition is_inj {A B : Type} (f : A -> B) : Prop := 
    forall (a a' : A), f a = f a' -> a = a'.

Definition is_inj_cm 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'}
    (f : ContractMorphism C C') : Prop := 
    (* init morphisms inject *)
    is_inj (init_inputs  C C' (init_cm f)) /\
    is_inj (init_outputs C C' (init_cm f)) /\
    (* recv morphisms inject *)
    is_inj (recv_inputs  C C' (recv_cm f)) /\
    is_inj (recv_outputs C C' (recv_cm f)).

Definition contract_embeds 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        (C1 : Contract Setup Msg State Error) (C2 : Contract Setup' Msg' State' Error') := 
    exists (f : ContractMorphism C1 C2), is_inj_cm f.

(* results about monomorphisms *)
(* an EMBEDDING of traces *)

Definition embed_trace bstate bstate1 bstate2 :
    ChainTrace bstate bstate1 -> ChainTrace bstate bstate2 := todo "".
Definition bstate_embeds (bstate1 bstate2 : ChainState) : Prop := todo "".

Theorem inj_cm_then_trace_embedding 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : 
    contract_embeds C1 C2 -> 
    (* for all reachable states where C1 is deployed *)
    forall bstate1 caddr (trace1 : ChainTrace empty_state bstate1),
    reachable bstate1 -> 
    env_contracts bstate1 caddr = Some (C1 : WeakContract) ->
    (* we can produce a trace in the case that C2 was deployed rather than C1 *)
    exists (bstate2 : ChainState) (trace2 : ChainTrace empty_state bstate2),
    env_contracts bstate2 caddr = Some (C2 : WeakContract) /\ 
    bstate_embeds bstate1 bstate2 /\ (* exists an embedding morphism *)
    trace2 = embed_trace empty_state bstate1 bstate2 trace1. (* we can construct a trace to reachable bstate2 *)
Proof. Admitted.    

End Monomorphisms.


Section Epimorphisms.

Definition is_surj {A B : Type} (f : A -> B) : Prop := 
    forall (b : B), exists (a : A), f a = b.

Definition is_surj_cm 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'}
    (f : ContractMorphism C C') : Prop := 
    (* init morphisms surject *)
    is_surj (init_inputs C C' (init_cm f)) /\ 
    is_surj (init_outputs C C' (init_cm f)) /\
    (* recv morphisms surject *)
    is_surj (recv_inputs C C' (recv_cm f)) /\
    is_surj (recv_outputs C C' (recv_cm f)).

(* TODO : Result about surjections : possibly about retracts, splitting C into C + C' via a retract *)
(*                                 : possibly about upgradeability too *)

Definition contract_surjects 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        (C1 : Contract Setup Msg State Error) (C2 : Contract Setup' Msg' State' Error') := 
    exists (f : ContractMorphism C1 C2), is_surj_cm f.

Definition bstate_surjects (bstate1 bstate2 : ChainState) : Prop := todo "".
Definition quotient_trace bstate bstate1 bstate2 :
    ChainTrace bstate bstate1 -> ChainTrace bstate bstate2 := todo "".

Theorem surj_cm_surj_bstate
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : 
    contract_surjects C1 C2 -> 
    (* for all reachable states where C1 is deployed *)
    forall bstate1 caddr (trace1 : ChainTrace empty_state bstate1),
    env_contracts bstate1 caddr = Some (C1 : WeakContract) ->
    (* we can produce a trace in the case that C2 was deployed rather than C1 *)
    exists (bstate2 : ChainState) (trace2 : ChainTrace empty_state bstate2),
    env_contracts bstate2 caddr = Some (C2 : WeakContract) /\ 
    bstate_surjects bstate1 bstate2 /\ (* exists a surjection morphism *)
    trace2 = quotient_trace empty_state bstate1 bstate2 trace1. (* we can compress trace1 into trace2 *)
Proof. Admitted.

End Epimorphisms.


Section TerminalContract.
    Import ListNotations.
    Set Nonrecursive Elimination Schemes.

(** State *)
Record Null_State := { null_state : unit }.

(** Msg *)
Inductive Null_Msg := 
| null_msg (n : unit).

(** Setup *)
Definition Null_Setup := option unit.

(* one canonical error message *)
Definition Null_Error := unit.

(** Init/Recv Functions *)
Definition null_init 
    (_ : Chain) 
    (_ : ContractCallContext) 
    (null_init : Null_Setup) : result Null_State Null_Error := 
        match null_init with 
        | Some _ => Ok {| null_state := tt |}
        | None => Err tt
        end.

Definition null_recv
    (_ : Chain) 
    (_ : ContractCallContext) 
    (_ : Null_State) 
    (op_msg : option Null_Msg) : 
    result (Null_State * list ActionBody) Null_Error := 
        match op_msg with 
        | Some _ => Ok ({| null_state := tt |}, [])
        | None => Err tt
        end.

(** Derive [Serializable] instances for state and messages *)
Global Instance Null_State_serializable : Serializable Null_State :=
Derive Serializable Null_State_rect<Build_Null_State>.

Global Instance Null_Msg_serializable : Serializable Null_Msg :=
Derive Serializable Null_Msg_rect<null_msg>.

(** the Terminal contract *)
Definition null_contract : Contract Null_Setup Null_Msg Null_State Null_Error := 
    build_contract null_init null_recv.

(* prove that every contract has a morphism into the terminal contract *)
Context 
    { Setup Msg State Error : Type } 
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    { C : Contract Setup Msg State Error }.

(* init morphisms *)
Definition morph_init_i (x : Chain * ContractCallContext * Setup) : Chain * ContractCallContext * Null_Setup :=
    let (x', s) := x in let (c, ctx) := x' in
    match (C.(init) c ctx s) with 
    | Ok  _ => (c, ctx, Some tt)
    | Err _ => (c, ctx, None)
    end.
Definition morph_init_o (x : result State Error) : result Null_State Null_Error := 
    match x with 
    | Ok  _ => Ok {| null_state := tt |}
    | Err _ => Err tt
    end.
Lemma null_init_commutes : init_morphs_commute C.(init) null_contract.(init) morph_init_i morph_init_o.
Proof.
    unfold init_morphs_commute. 
    intro. destruct x as [x' s]. destruct x' as [c ctx]. simpl.
    unfold uncurry_fun3. unfold null_init. unfold morph_init_o.
    now destruct (init C c ctx s).
Qed.

(* recv morphisms *)
Definition morph_recv_i (x : Chain * ContractCallContext * State * option Msg) : Chain * ContractCallContext * Null_State * option Null_Msg := 
    let (x', op_msg) := x in
    let (x'', st) := x' in 
    let (c, ctx) := x'' in 
    match (C.(receive) c ctx st op_msg) with 
    | Ok  _ => (c, ctx, {| null_state := tt |}, (Some (null_msg tt)))
    | Err _ => (c, ctx, {| null_state := tt |}, None)
    end.
Definition morph_recv_o (x : result (State * list ActionBody) Error) : result (Null_State * list ActionBody) Null_Error := 
    match x with 
    | Ok  _ => Ok ({| null_state := tt |}, [])
    | Err _ => Err tt 
    end.
Lemma null_recv_commutes : recv_morphs_commute C.(receive) null_contract.(receive) morph_recv_i morph_recv_o.
Proof.
    unfold recv_morphs_commute. intro.
    destruct x as [x' op_msg]. destruct x' as [x'' st]. destruct x'' as [c ctx]. simpl.
    unfold uncurry_fun4. unfold null_recv. unfold morph_recv_o.
    now destruct (receive C c ctx st op_msg).
Qed.

(* the terminal morphism *)
Definition null_morphism : ContractMorphism C null_contract := 
    let morph_init := {|
        init_inputs   := morph_init_i ; 
        init_outputs  := morph_init_o ;
        init_commutes := null_init_commutes ;
    |} in
    let morph_recv := {|
        recv_inputs   := morph_recv_i ;
        recv_outputs  := morph_recv_o ; 
        recv_commutes := null_recv_commutes ;
    |} in {| 
        cm_init := morph_init ; 
        cm_recv := morph_recv ;
    |}.

(* TODO: this is more nuanced 
Lemma null_morphism_unique : forall (f : ContractMorphism C null_contract), f = null_morphism.
Proof. 
    intro. apply is_eq_cm; try apply is_eq_cm_init; try apply is_eq_cm_recv; apply functional_extensionality; intro.
    -   destruct x as [x' s]. destruct x' as [c ctx].
        admit.
    -   destruct x. Admitted.*)

End TerminalContract.




End ContractMorphisms.