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
From ConCert.Execution Require Import BuildUtils.
From ConCert.Execution Require Import InterContractCommunication.
From ConCert.Utils Require Import RecordUpdate.

Axiom todo : string -> forall {A}, A.

(* some auxiliary functions *)
Definition curry_fun3 {A B C D : Type} (f : A * B * C -> D) : A -> B -> C -> D := 
    fun (a : A) => fun (b : B) => fun (c : C) => f (a,b,c).
Definition uncurry_fun3 {A B C D : Type} (f : A -> B -> C -> D) : A * B * C -> D :=
    fun (x : A * B * C) => 
        let '(a, b, c) := x in f a b c.
Definition curry_fun4 {A B C D E : Type} (f : A * B * C * D -> E) : A -> B -> C -> D -> E :=
    fun (a : A) => fun (b : B) => fun (c : C) => fun (d : D) => f (a,b,c,d).
Definition uncurry_fun4 {A B C D E : Type} (f : A -> B -> C -> D -> E) : A * B * C * D -> E :=
    fun (x : A * B * C * D) => 
        let '(a, b, c, d) := x in f a b c d.
Definition serialize_function {A B} `{Serializable A} `{Serializable B} 
    (f : A -> B) (sv : SerializedValue) : SerializedValue := 
    match deserialize sv with 
    | None => sv (* ideally would not be deserializable *)
    | Some a => serialize (f a)
    end.
Definition option_fun {A B} (f : A -> B) (op_a : option A) : option B := 
    match op_a with 
    | Some a => Some (f a)
    | None => None 
    end.


Section ContractMorphisms.
Context { Base : ChainBase }.

(** First, a definition of a Contract Morphism, which is a function between contracts *)
Section MorphismDefinition.

(** The init component *)
Record InitCM
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C : Contract Setup Msg State Error) (C' : Contract Setup' Msg' State' Error') 
    := build_init_cm {
        (* transform inputs/outputs of the init function *)
        init_inputs : Chain * ContractCallContext * Setup -> 
            Chain * ContractCallContext * Setup' ;
        init_outputs : result State Error -> result State' Error' ;
        (* proof of commutativity *)
        init_commutes : 
            forall x : Chain * ContractCallContext * Setup,
                uncurry_fun3 C'.(init) (init_inputs x) = 
                init_outputs (uncurry_fun3 C.(init) x) ;
    }.

(** The receive component *)
Record RecvCM
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C : Contract Setup Msg State Error) (C' : Contract Setup' Msg' State' Error') := 
    build_recv_cm {
        (* transform inputs/outputs of the receive function *)
        recv_inputs : Chain * ContractCallContext * State * option Msg -> 
            Chain * ContractCallContext * State' * option Msg' ;
        recv_outputs : result (State * list ActionBody) Error -> 
            result (State' * list ActionBody) Error' ;
        (* proof of commutativity *)
        recv_commutes : 
            forall (x : Chain * ContractCallContext * State * option Msg), 
                uncurry_fun4 C'.(receive) (recv_inputs x) = 
                recv_outputs (uncurry_fun4 C.(receive) x) ;
    }.

(** The definition *)
Record ContractMorphism 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C  : Contract Setup  Msg  State  Error) 
    (C' : Contract Setup' Msg' State' Error') := 
    build_cm {
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
Definition id_fun (A : Type) : A -> A := @id A.

(* the coherence conditions for constructing non-opaque morphisms *)
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

End MorphismUtilities.


(** The Identity Contract Morphism *)
Section IdentityMorphism.

(* an opaque construction *)
Definition id_cm_opaque 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) : ContractMorphism C C.
Proof.
    constructor.
    -   set (init_inputs  := id_fun (Chain * ContractCallContext * Setup)).
        set (init_outputs := id_fun (result State Error)).
        apply (build_init_cm Setup Setup Msg Msg State State Error Error H H0 H1 H2 H H0 H1 H2 C C init_inputs init_outputs).
        intro. destruct x. destruct p.
        unfold uncurry_fun3. 
        unfold init_inputs. unfold init_outputs. 
        unfold id_fun. simpl.
        reflexivity.
    -   set (recv_inputs  := id_fun (Chain * ContractCallContext * State * option Msg)).
        set (recv_outputs := id_fun (result (State * list ActionBody) Error)).
        apply (build_recv_cm Setup Setup Msg Msg State State Error Error H H0 H1 H2 H H0 H1 H2 C C recv_inputs recv_outputs).
        intro. destruct x. repeat destruct p.
        unfold uncurry_fun4. 
        unfold recv_inputs. unfold recv_outputs. 
        unfold id_fun. simpl.
        reflexivity.
Qed.

(* an explicity construction *)
Lemma init_commutes_id 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) :
    init_morphs_commute 
        C.(init) C.(init) 
        (id_fun (Chain * ContractCallContext * Setup)) 
        (id_fun (result State Error)).
Proof. intro. auto. Qed.

Definition id_cm_init 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) :
    InitCM C C := {|
        init_inputs  := id_fun (Chain * ContractCallContext * Setup) ;
        init_outputs := id_fun (result State Error) ;
        (* proof of commutativity *)
        init_commutes := init_commutes_id C ;
    |}.

Lemma recv_commutes_id 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) :
    recv_morphs_commute 
        C.(receive) C.(receive) 
        (id_fun (Chain * ContractCallContext * State * option Msg)) 
        (id_fun (result (State * list ActionBody) Error)).
Proof. intro. auto. Qed.

Definition id_cm_recv 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) : RecvCM C C := {|
        recv_inputs := id_fun (Chain * ContractCallContext * State * option Msg) ;
        recv_outputs := id_fun (result (State * list ActionBody) Error) ;
        (* proof of commutativity *)
        recv_commutes := recv_commutes_id C ;
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

(** Deriving equality of Contract Morphisms *)
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


(** An explicit construction of the composition of two morphisms *)
Section MorphismComposition.

(** The Init component *)
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

(** The Recv component *)
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

(** Composition *)
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

(** Composition with the Identity morphism is trivial *)
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

(** Composition is associative *)
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


(** We will treat various type of contract morphisms, starting with isomorphisms. *)
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
        unfold id_cm_init. unfold id_cm_recv. unfold id_fun. 
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
        unfold id_cm_init. unfold id_cm_recv. unfold id_fun.
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

End Isomorphisms.


(** Now, onto injections *)
Section Injections.

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

End Injections.


(** Finally, we treat surjections, or quotients *)
Section Surjections.

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

Definition contract_surjects 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        (C1 : Contract Setup Msg State Error) (C2 : Contract Setup' Msg' State' Error') := 
    exists (f : ContractMorphism C1 C2), is_surj_cm f.

End Surjections.


(** We have some interesting categorical properties, including the existence of a terminal
    contract. (Note that we have not yet proved uniqueness of the terminal morphism.) *)
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

(* TODO: Prove uniqueness *)

End TerminalContract.


(** The definition of contract morphisms is fairly general, and 
    somewhat difficult to work with. As we proceed, we will use 
    simple contract morphisms, which can be decomposed as functions 
    between state, msg, setup, and error types along with the corresponding
    coherence result.
    
    This simpler structure will allow us to lift contract morphisms into
    a transformation of chainstate and trace.
    
    Note that these simpler morphisms do not modify balances or emitted 
    actions. Future work could include generalizing the lifting result
    to allow for more contract morphisms.
*)
Section SimpleContractMorphism.

(** Some auxiliary functions for transforming component functions into morphism form *)
Definition init_result_transform 
        { State State' Error Error' : Type }
    (state_morph : State -> State')
    (error_morph : Error -> Error')
    (x : result State Error) : result State' Error' :=
    match x with 
    | Ok t => Ok (state_morph t)
    | Err e => Err (error_morph e)
    end.

Definition recv_result_transform 
        { State State' Error Error' : Type }
    (state_morph : State -> State')
    (error_morph : Error -> Error')
    (x : result (State  * list ActionBody) Error) : result (State' * list ActionBody) Error' := 
        match x with 
        | Ok t => let '(st, l) := t in Ok (state_morph st, l)
        | Err e => Err (error_morph e)
        end.

(** We explicitly construct the components *)
(* the init component *)
Lemma init_commutes_simple 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} 
    {C2 : Contract Setup' Msg' State' Error'}
    (* the components of f *)
    (setup_morph : Setup -> Setup')
    (state_morph : State -> State')
    (error_morph : Error -> Error')
    (* coherence conditions *)
    (init_coherence : forall c ctx s, 
        (init_result_transform state_morph error_morph) ((init C1) c ctx s) = (init C2) c ctx (setup_morph s)) : 
    init_morphs_commute 
        C1.(init) C2.(init)
        (fun (x : Chain * ContractCallContext * Setup) => 
            let '(c, ctx, s) := x in (c, ctx, setup_morph s))
        (init_result_transform state_morph error_morph).
Proof.
    unfold init_morphs_commute. 
    intro. destruct x. destruct p.
    unfold uncurry_fun3. simpl.
    rewrite <- (init_coherence c c0 s).
    unfold init_outputs. 
    reflexivity.
Qed.

Definition simple_cm_init 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} 
    {C2 : Contract Setup' Msg' State' Error'}
    (* the components of f *)
    (setup_morph : Setup -> Setup')
    (state_morph : State -> State')
    (error_morph : Error -> Error')
    (* coherence conditions *)
    (init_coherence : forall c ctx s, 
        (init_result_transform state_morph error_morph) ((init C1) c ctx s) = (init C2) c ctx (setup_morph s)) : 
    InitCM C1 C2 := {| 
        init_inputs := (fun (x : Chain * ContractCallContext * Setup) => 
        let '(c, ctx, s) := x in (c, ctx, setup_morph s)) ; 
        init_outputs := (init_result_transform state_morph error_morph) ; 
        init_commutes := init_commutes_simple setup_morph state_morph error_morph init_coherence ;
    |}.

(* the recv component *)
Lemma recv_commutes_simple 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} 
    {C2 : Contract Setup' Msg' State' Error'}
    (* the components of f *)
    (msg_morph   : Msg   -> Msg')
    (state_morph : State -> State')
    (error_morph : Error -> Error')
    (* coherence conditions *)
    (recv_coherence : forall c ctx st op_msg, 
        (recv_result_transform state_morph error_morph) ((receive C1) c ctx st op_msg) = 
        (receive C2) c ctx (state_morph st) (option_fun msg_morph op_msg)) : 
    recv_morphs_commute
        C1.(receive) C2.(receive)
        (fun (x : Chain * ContractCallContext * State * option Msg) => 
            let '(c, ctx, st, op_msg) := x in (c, ctx, state_morph st, option_fun msg_morph op_msg))
        (recv_result_transform state_morph error_morph).
Proof.
    unfold recv_morphs_commute. 
    intro. destruct x. repeat destruct p.
    unfold uncurry_fun4. simpl.
    rewrite <- (recv_coherence c c0 s o).
    unfold recv_outputs.
    reflexivity.
Qed.

Definition simple_cm_recv 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} 
    {C2 : Contract Setup' Msg' State' Error'}
    (* the components of f *)
    (msg_morph   : Msg   -> Msg')
    (state_morph : State -> State')
    (error_morph : Error -> Error')
    (* coherence conditions *)
    (recv_coherence : forall c ctx st op_msg, 
        (recv_result_transform state_morph error_morph) ((receive C1) c ctx st op_msg) = 
        (receive C2) c ctx (state_morph st) (option_fun msg_morph op_msg)) : 
    RecvCM C1 C2 := {| 
        recv_inputs := 
            (fun (x : Chain * ContractCallContext * State * option Msg) => 
                let '(c, ctx, st, op_msg) := x in (c, ctx, state_morph st, option_fun msg_morph op_msg)) ; 
        recv_outputs := 
            (recv_result_transform state_morph error_morph) ; 
        recv_commutes := recv_commutes_simple msg_morph state_morph error_morph recv_coherence ;
    |}.

(* the simple contract morphism *)
Definition simple_cm 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} 
    {C2 : Contract Setup' Msg' State' Error'}
    (* the components of f *)
    (msg_morph   : Msg   -> Msg')
    (setup_morph : Setup -> Setup')
    (state_morph : State -> State')
    (error_morph : Error -> Error')
    (* coherence conditions *)
    (init_coherence : forall c ctx s, 
        (init_result_transform state_morph error_morph) ((init C1) c ctx s) = (init C2) c ctx (setup_morph s))
    (recv_coherence : forall c ctx st op_msg, 
        (recv_result_transform state_morph error_morph) ((receive C1) c ctx st op_msg) = 
        (receive C2) c ctx (state_morph st) (option_fun msg_morph op_msg)) : 
    ContractMorphism C1 C2 := {| 
        cm_init := simple_cm_init setup_morph state_morph error_morph init_coherence ;
        cm_recv := simple_cm_recv msg_morph   state_morph error_morph recv_coherence ;
    |}.

End SimpleContractMorphism.


(** In this Section, we lift a contract morphism f to a transformation of bstate and trace.
    The main result, cm_lift, is proved by induction over the trace.
        The section is organized as follows:
        1. Section ChainStateMorphism: 
            - We define a morphism of environments and chainstates, parameterized by f
            - We define the trivial morphism on trivial chainstates
        1. Section BStateTransform:
            - We define a transformation of bstate over f, bstate_transform_step, along with
              a chainstate morphism from a state bstate to (bstate_transform_step bstate).
            - This is done in chainstate_morphism_step.
        2. Section CMLiftInductiveStep:
            - We prove various lemmas for the inductive step of our proof. Each of these
              has the prefix chainstep_transform_
            - The inductive step is proved in the results chainstep_transform_step and 
              caddr_implication_step
        5. Finally, we prove the main result cm_lift
*)
Section ContractMorphismLift.
Context 
    (* we can lift a morphism of contracts, parameterized by the morphpism f and the address of C1 *)
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'}
    {f : ContractMorphism C1 C2}.

Variable 
    (* f must be decomposable as follows *)
    (msg_morph   : Msg   -> Msg')
    (setup_morph : Setup -> Setup')
    (state_morph : State -> State')
    (error_morph : Error -> Error')
    (* with coherence conditions satisfied *)
    (init_coherence : forall c ctx s, 
        (init_result_transform state_morph error_morph) ((init C1) c ctx s) = (init C2) c ctx (setup_morph s))
    (recv_coherence : forall c ctx st op_msg, 
        (recv_result_transform state_morph error_morph) ((receive C1) c ctx st op_msg) = 
        (receive C2) c ctx (state_morph st) (option_fun msg_morph op_msg))
    (* f is decomposable *)
    (f_decomposable : 
        f = simple_cm msg_morph setup_morph state_morph error_morph init_coherence recv_coherence).

(* TODO *)
Definition wc_dec_eq : forall w1 w2 : WeakContract, {w1 = w2} + {w1 <> w1} := todo "".
Declare Scope wc_scope.
Delimit Scope wc_scope with wc.
Bind Scope wc_scope with WeakContract.
Infix "=?" := wc_dec_eq (at level 70) : wc_scope.

Section ChainStateMorphism.
(* Given f, we can transform actions *)
Definition action_transform (native_env : Environment) (a : Action) : Action := {| 
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

Lemma empty_chainstate_morphism : ChainStateMorphism empty_state empty_state. 
Proof.
    apply build_chainstate_morphism; auto.
    apply build_env_morphism; auto.
Qed.

End ChainStateMorphism.


Section BStateTransform.
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
        let queue := List.map (action_transform bstate) (chain_state_queue bstate) in 
        (* return the new cstate *)
        {| chain_state_env := env ; chain_state_queue := queue ; |}.

(* Some lemmas to construct something in ChainStateMorphism bstate (bstate_transform_step bstate) *)
Lemma env_morph_step_chain_eq (bstate1 : ChainState) : 
        let bstate2 := bstate_transform_step bstate1 in
        env_chain bstate1 = env_chain bstate2.
Proof. auto. Qed.

Definition env_morph_step_balances (bstate1 : ChainState) : 
    let bstate2 := bstate_transform_step bstate1 in
    forall a, env_account_balances bstate1 a = env_account_balances bstate2 a.
Proof. auto. Qed.

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
    = List.map (action_transform bstate1) (chain_state_queue bstate1).
Proof. auto. Qed.

(* We have ChainStateMorphism bstate (bstate_transform_step bstate) *)
Definition chainstate_morphism_step (bstate1' : ChainState) : 
    let bstate2' := bstate_transform_step bstate1' in  
    (ChainStateMorphism bstate1' bstate2') := {|  
        env_morph   := env_morph_step bstate1' ; 
        queue_morph := queue_morphism_step bstate1' |}.

End BStateTransform.


Section CMLiftInductiveStep.
(* the main result of this section is chainstep_transform_step, for which we need 
   several lemmas, each of which are prefixed with chainstep_transform_ *)

(* construct the step from bstate2 to bstate2' *)
Lemma chainstep_transform_empty_queue 
    (cstate1 cstate2 : ChainState) 
    (m : ChainStateMorphism cstate1 cstate2) : 
    chain_state_queue cstate1 = nil -> chain_state_queue cstate2 = nil.
Proof. 
    intro. rewrite (queue_morph cstate1 cstate2 m). rewrite H7. simpl. reflexivity.
Qed.

Lemma chainstep_transform_next_block_valid
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

Lemma chainstep_transform_no_acts_from_accounts
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

Lemma chainstep_transform_origin_eq_from
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

Lemma chainstep_transform_step_env_chain_eq
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

Lemma chainstep_transform_new_env_equiv_add_block
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

Lemma chainstep_transform_new_permuted 
    (bstate1 bstate2 bstate1' : ChainState)
    (env_equiv : EnvironmentEquiv bstate1 bstate1') 
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    let bstate2' := bstate_transform_step bstate1' in 
    Permutation (chain_state_queue bstate1) (chain_state_queue bstate1') -> 
    Permutation (chain_state_queue bstate2) (chain_state_queue bstate2').
Proof.
    intros.
    simpl. rewrite (queue_morph bstate1 bstate2 c_morph).
    assert (action_transform bstate1 = action_transform bstate1').
    - apply functional_extensionality. intro a.
        unfold action_transform. f_equal.
        destruct (act_body a); auto.
        rewrite (contracts_eq bstate1 bstate1' env_equiv to). auto.
    - rewrite <- H8. 
        exact (permutation_preserved_over_map (action_transform bstate1) (chain_state_queue bstate1) (chain_state_queue bstate1') H7).
Qed.

Lemma chainstep_transform_new_env_equiv_permute 
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

Lemma chainstep_transform_new_queue_prev 
    (bstate1 bstate2 : ChainState)
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    forall (act : Action) (acts : list Action),
    chain_state_queue bstate1 = act :: acts -> 
    let new_act := action_transform bstate1 act in 
    let new_acts := List.map (action_transform bstate1) acts in
    chain_state_queue bstate2 = new_act :: new_acts.
Proof.
    intros.
    unfold new_act. unfold new_acts.
    rewrite (queue_morph bstate1 bstate2 c_morph). 
    rewrite H7.
    auto.
Qed.

Lemma chainstep_transform_new_act_eval_true 
    (bstate1 bstate2 bstate1' : ChainState)
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    forall (act : Action) (new_acts : list Action),
    let act' := action_transform bstate1 act in
    let new_acts' := List.map (action_transform bstate1') new_acts in
    let bstate2' := bstate_transform_step bstate1' in
    ActionEvaluation bstate1 act  bstate1' new_acts ->
    ActionEvaluation bstate2 act' bstate2' new_acts'.
Proof. Admitted.

(* TODO transform bstate back *)
Lemma act_eval_pullback 
    (bstate1 bstate2 : ChainState) 
    (c_morph : ChainStateMorphism bstate1 bstate2)
    (bstate : Environment) (act : Action) (new_acts : list Action) : 
    let act' := action_transform bstate1 act in 
    ActionEvaluation bstate2 act' bstate new_acts ->
    ActionEvaluation bstate1 act  bstate new_acts.
Proof. Admitted.

Lemma chainstep_transform_new_act_eval_false
    (bstate1 bstate2 : ChainState) 
    (c_morph : ChainStateMorphism bstate1 bstate2)
    (act : Action) : 
    let act' := action_transform bstate1 act in 
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

Lemma chainstep_transform_new_queue_next
    (bstate1 bstate2 bstate1' : ChainState)
    (c_morph : ChainStateMorphism bstate1 bstate2) : 
    forall (new_acts : list Action) (acts : list Action),
    chain_state_queue bstate1' = new_acts ++ acts -> 
    let bstate2'  := bstate_transform_step bstate1' in  
    let new_acts' := List.map (action_transform bstate1') new_acts in 
    let acts'     := List.map (action_transform bstate1) acts in
    chain_state_queue bstate2' = new_acts' ++ acts'.
Proof.
    intros.
    unfold bstate2'.
    unfold bstate_transform_step. simpl.
    unfold new_acts'. unfold acts'. rewrite H7.
    rewrite (list_map_concat new_acts acts). 
    f_equal.
    admit.
Admitted.

Lemma chainstep_transform_queue_next_action_invalid
    (bstate1 bstate2 bstate1' : ChainState) 
    (acts : list Action): 
    let bstate2' := bstate_transform_step bstate1' in  
    let acts' := List.map (action_transform bstate1) acts in 
    chain_state_queue bstate1' = acts ->
    chain_state_queue bstate2' = acts'.
Proof.
    intros.
    unfold bstate2'. 
    unfold bstate_transform_step. simpl.
    unfold acts'. rewrite H7.
    admit.
Admitted.

Lemma chainstep_transform_from_acct
    (bstate : ChainState) (act : Action) : 
    act_is_from_account act -> 
    act_is_from_account (action_transform bstate act).
Proof.
    unfold act_is_from_account.
    intros.
    assert (act_from (action_transform bstate act) = act_from act).
    - unfold action_transform. auto.
    - rewrite H8. exact H7.
Qed.

Definition chainstep_transform_step 
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
            chainstep_transform_empty_queue bstate1 bstate2 c_morph prev_queue_empty in 
        (* modified next_block_valid *)
        let next_block_valid' := 
            chainstep_transform_next_block_valid bstate1 bstate2 c_morph header next_block_valid in 
        (* modified no_acts_from_accounts *)
        let no_acts_from_accounts' := 
            chainstep_transform_no_acts_from_accounts bstate1' no_acts_from_accounts in
        (* modified origin_eq_from *)
        let origin_eq_from' :=
            chainstep_transform_origin_eq_from bstate1' origin_eq_from in 
        (* modified env_equiv *)
        let env_equiv' :=
            chainstep_transform_new_env_equiv_add_block bstate1 bstate2 bstate1' 
            (env_morph bstate1 bstate2 c_morph) header env_equiv in
        (* the new step_block *)
        step_block bstate2 bstate2'
            header' prev_queue_empty' next_block_valid' no_acts_from_accounts' 
            origin_eq_from' env_equiv'
    | step_action _ _ act acts new_acts queue_prev act_eval_true queue_next => 
        (* modified act *)
        let act' := action_transform bstate1 act in 
        (* modified acts *)
        let acts' := 
            List.map (action_transform bstate1) acts in 
        (* modified new_acts *)
        let new_acts' := 
            List.map (action_transform bstate1') new_acts in 
        (* modified queue_prev *)
        let queue_prev' := 
            chainstep_transform_new_queue_prev bstate1 bstate2 c_morph act acts queue_prev in 
        (* modified act_eval_true *)
        let act_eval_true' := 
            chainstep_transform_new_act_eval_true bstate1 bstate2 bstate1' c_morph act new_acts act_eval_true in 
        (* modified queue_next *)
        let queue_next' := 
            chainstep_transform_new_queue_next bstate1 bstate2 bstate1' c_morph new_acts acts queue_next in
        (* the new step_block *)
        step_action bstate2 bstate2' act' acts' new_acts' queue_prev' act_eval_true' queue_next'
    | step_action_invalid _ _ act acts env_equiv queue_prev queue_next from_acct actn_eval_false => 
        (* modified act *)
        let act' := action_transform bstate1 act in 
        (* modified acts *)
        let acts' := 
            List.map (action_transform bstate1) acts in 
        (* modified env_equiv *)
        let env_equiv' := 
            chainstep_transform_new_env_equiv_permute bstate1 bstate2 bstate1' 
            (env_morph bstate1 bstate2 c_morph) env_equiv in 
        (* modified queue_prev *)
        let queue_prev' := 
            chainstep_transform_new_queue_prev bstate1 bstate2 c_morph act acts queue_prev in 
        (* modified queue_next *)
        let queue_next' := 
            chainstep_transform_queue_next_action_invalid bstate1 bstate2 bstate1' acts queue_next in 
        (* modified from_acct *)
        let from_acct' := 
            chainstep_transform_from_acct bstate1 act from_acct in 
        (* modified actn_eval_false *)
        let actn_eval_false' := 
            chainstep_transform_new_act_eval_false bstate1 bstate2 c_morph act actn_eval_false in 
        (* the new step_block *)
        step_action_invalid bstate2 bstate2' act' acts' env_equiv' queue_prev' queue_next' from_acct' actn_eval_false'
    | step_permute _ _ env_equiv permuted => 
        (* modified env_equiv *)
        let env_equiv' := 
            chainstep_transform_new_env_equiv_permute bstate1 bstate2 bstate1' 
            (env_morph bstate1 bstate2 c_morph) env_equiv in 
        (* modified permutation *)
        let permuted' := 
            chainstep_transform_new_permuted bstate1 bstate2 bstate1' (symmetry env_equiv) c_morph permuted in 
        (* the new step_block *)
        step_permute bstate2 bstate2' env_equiv' permuted' 
    end.

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

End CMLiftInductiveStep.

(* Theorem: A contract morphism can be lifted into a morphism of ChainStates *)
Theorem cm_lift :
    forall  bstate1 caddr (trace : ChainTrace empty_state bstate1),
    exists  (* a new bstate related to the old *)
            (bstate2 : ChainState) 
            (bstate_morph : ChainStateMorphism bstate1 bstate2)
            (* a new trace constructed from the old *)
            (trace2 : ChainTrace empty_state bstate2),
            (* with C2 swapped out for C1 *)
            env_contracts bstate1 caddr = Some (C1 : WeakContract) -> 
            env_contracts bstate2 caddr = Some (C2 : WeakContract).
Proof.
    (* we induct over the trace *)
    intros.
    remember empty_state eqn:genesis_empty. 
    induction trace.
    - rewrite genesis_empty. 
        exists empty_state. 
        exists empty_chainstate_morphism. 
        exists ChainedList.clnil.
        intro. assert (env_contracts empty_state caddr = None); auto. 
        rewrite H8 in H7. congruence.
    - apply IHtrace in genesis_empty. clear IHtrace.
        destruct genesis_empty as [bstate2 genesis_empty]. 
        destruct genesis_empty as [bstate_morph genesis_empty]. 
        destruct genesis_empty as [trace2 addr_implication].
        (* construct the new bstate and trace *)
        set (bstate2' := bstate_transform_step to).
        set (l' := chainstep_transform_step mid bstate2 to bstate_morph l).
        set (trace2' := ChainedList.snoc trace2 l').
        (* construct the relationships *)
        set (bstate_morph' := chainstate_morphism_step to).
        set (caddr_impl := caddr_implication_step to caddr).
        exists bstate2'. 
        exists bstate_morph'. 
        exists trace2'.
        exact caddr_impl.
Qed.

(* TODO a non-opaque construction? *)

End ContractMorphismLift.


(** We now examin how lifted morphisms behave with regard to morphism composition *)
Section ContractMorphismLiftCompose.

(*
Lemma id_lifts_to_id 

Lemma morphisms_lift_compose

Lemma iso_lifts_to_iso

Lemma inj_lifts_to_inj

Lemma surj_lifts_to_surj
*)

End ContractMorphismLiftCompose.

End ContractMorphisms.