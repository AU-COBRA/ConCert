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
Definition curry_3 {A B C D : Type} (f : A * B * C -> D) : A -> B -> C -> D := 
    (compose curry curry) f.
Definition curry_4 {A B C D E : Type} (f : A * B * C * D -> E) : A -> B -> C -> D -> E :=
    curry (curry (curry f)).
Definition uncurry_3 {A B C D : Type} (f : A -> B -> C -> D) : A * B * C -> D :=
    (compose uncurry uncurry) f.
Definition uncurry_4 {A B C D E : Type} (f : A -> B -> C -> D -> E) : A * B * C * D -> E :=
    uncurry (uncurry (uncurry f)).

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
                uncurry_3 C'.(init) (init_inputs x) = 
                init_outputs (uncurry_3 C.(init) x) ;
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
                uncurry_4 C'.(receive) (recv_inputs x) = 
                recv_outputs (uncurry_4 C.(receive) x) ;
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
        uncurry_3 init' (init_inputs x) = 
        init_outputs (uncurry_3 init x).

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
            uncurry_4 recv' (recv_inputs x) = 
            recv_outputs (uncurry_4 recv x).

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
        unfold uncurry_3. 
        unfold init_inputs. unfold init_outputs. 
        unfold id_fun. simpl.
        reflexivity.
    -   set (recv_inputs  := id_fun (Chain * ContractCallContext * State * option Msg)).
        set (recv_outputs := id_fun (result (State * list ActionBody) Error)).
        apply (build_recv_cm Setup Setup Msg Msg State State Error Error H H0 H1 H2 H H0 H1 H2 C C recv_inputs recv_outputs).
        intro. destruct x. repeat destruct p.
        unfold uncurry_4. 
        unfold recv_inputs. unfold recv_outputs. 
        unfold id_fun. simpl.
        reflexivity.
Qed.

(* an explicit construction *)
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
    unfold uncurry_3. unfold null_init. unfold morph_init_o.
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
    unfold uncurry_4. unfold null_recv. unfold morph_recv_o.
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
    unfold uncurry_3. simpl.
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
        (receive C2) c ctx (state_morph st) (option_map msg_morph op_msg)) : 
    recv_morphs_commute
        C1.(receive) C2.(receive)
        (fun (x : Chain * ContractCallContext * State * option Msg) => 
            let '(c, ctx, st, op_msg) := x in (c, ctx, state_morph st, option_map msg_morph op_msg))
        (recv_result_transform state_morph error_morph).
Proof.
    unfold recv_morphs_commute. 
    intro. destruct x. repeat destruct p.
    unfold uncurry_4. simpl.
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
        (receive C2) c ctx (state_morph st) (option_map msg_morph op_msg)) : 
    RecvCM C1 C2 := {| 
        recv_inputs := 
            (fun (x : Chain * ContractCallContext * State * option Msg) => 
                let '(c, ctx, st, op_msg) := x in (c, ctx, state_morph st, option_map msg_morph op_msg)) ; 
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
        (receive C2) c ctx (state_morph st) (option_map msg_morph op_msg)) : 
    ContractMorphism C1 C2 := {| 
        cm_init := simple_cm_init setup_morph state_morph error_morph init_coherence ;
        cm_recv := simple_cm_recv msg_morph   state_morph error_morph recv_coherence ;
    |}.

(* a predicate to indicate that a contract morphism is simple *)
Definition is_simple_cm
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} 
    {C2 : Contract Setup' Msg' State' Error'} 
    (f : ContractMorphism C1 C2) : Prop := 
    exists 
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
        (receive C2) c ctx (state_morph st) (option_map msg_morph op_msg)),
    f = simple_cm msg_morph setup_morph state_morph error_morph init_coherence recv_coherence.

(* TODO *)
(* a tactic for proving a morphism is simple 
Ltac show_is_simple_cm := 
    match goal with 
    | |- is_simple_cm _ => 
    end.
*)

(* a trivial lemma for convenience *)
Lemma simple_cm_is_simple
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C1 : Contract Setup Msg State Error} 
    {C2 : Contract Setup' Msg' State' Error'}
    (* the components of f *)
    {msg_morph   : Msg   -> Msg'}
    {setup_morph : Setup -> Setup'}
    {state_morph : State -> State'}
    {error_morph : Error -> Error'}
    (* coherence conditions *)
    {init_coherence : forall c ctx s, 
        (init_result_transform state_morph error_morph) ((init C1) c ctx s) = (init C2) c ctx (setup_morph s)}
    {recv_coherence : forall c ctx st op_msg, 
        (recv_result_transform state_morph error_morph) ((receive C1) c ctx st op_msg) = 
        (receive C2) c ctx (state_morph st) (option_map msg_morph op_msg)} : 
    is_simple_cm (simple_cm msg_morph setup_morph state_morph error_morph init_coherence recv_coherence).
Proof. 
    unfold is_simple_cm.
    exists msg_morph. exists setup_morph. exists state_morph. 
    exists error_morph. exists init_coherence. exists recv_coherence.
    auto.
Qed.

(* simple morphisms compose to simple morphisms *)
Lemma composition_simple_cm
    { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
    `{Serializable Msg}    `{Serializable Setup}    `{Serializable State}    `{Serializable Error}
    `{Serializable Msg'}   `{Serializable Setup'}   `{Serializable State'}   `{Serializable Error'}
    `{Serializable Msg''}  `{Serializable Setup''}  `{Serializable State''}  `{Serializable Error''}
    { C : Contract Setup Msg State Error } 
    { C' : Contract Setup' Msg' State' Error' }
    { C'' : Contract Setup'' Msg'' State'' Error'' } 
    (g : ContractMorphism C' C'')
    (f : ContractMorphism C  C') :
    is_simple_cm g -> 
    is_simple_cm f -> 
    is_simple_cm (composition_cm g f).
Proof. 
    unfold is_simple_cm.
    intros g_simple f_simple.
    (* extract functions from g *)
    destruct g_simple as [g_msg g_simple].
    destruct g_simple as [g_setup g_simple].
    destruct g_simple as [g_state g_simple].
    destruct g_simple as [g_error g_simple].
    destruct g_simple as [g_init g_simple].
    destruct g_simple as [g_recv g_simple].
    (* extract functions from f *)
    destruct f_simple as [f_msg f_simple].
    destruct f_simple as [f_setup f_simple].
    destruct f_simple as [f_state f_simple].
    destruct f_simple as [f_error f_simple].
    destruct f_simple as [f_init f_simple].
    destruct f_simple as [f_recv f_simple].
    (* construct g \circ f *)
    exists (compose g_msg f_msg).
    exists (compose g_setup f_setup).
    exists (compose g_state f_state).
    exists (compose g_error f_error).
    (* proof of init coherence *)
    assert (forall (c : Chain) (ctx : ContractCallContext) (s : Setup),
        init_result_transform 
            (compose g_state f_state)
            (compose g_error f_error) (init C c ctx s) =
        init C'' c ctx (compose g_setup f_setup s)).
    intros. simpl.
    rewrite <- g_init.
    rewrite <- f_init.
    unfold init_result_transform. destruct (init C c ctx s); auto.
    rename H11 into gf_init. 
    exists gf_init. 
    (* proof of recv coherence *)
    assert (forall (c : Chain) (ctx : ContractCallContext) (st : State) (op_msg : option Msg),
        recv_result_transform 
            (compose g_state f_state)
            (compose g_error f_error) (receive C c ctx st op_msg) =
        receive C'' c ctx (compose g_state f_state st) (option_map (compose g_msg f_msg) op_msg)).
    intros. simpl.
    replace (option_map (compose g_msg f_msg) op_msg) with (option_map g_msg (option_map f_msg op_msg)).
    rewrite <- g_recv.
    rewrite <- f_recv.
    unfold recv_result_transform. destruct (receive C c ctx st op_msg); simpl; auto. destruct t; auto.
    destruct op_msg; auto.
    rename H11 into gf_recv.
    exists gf_recv.
    (* rewrite the LHS *)
    rewrite g_simple. rewrite f_simple.
    unfold composition_cm. unfold simple_cm.
    apply is_eq_cm.
    - apply is_eq_cm_init. 
        + simpl. apply functional_extensionality. 
          intro. destruct x. destruct p. auto.
        + simpl. apply functional_extensionality.
          intro. destruct x; auto.
    - apply is_eq_cm_recv.
        + simpl. apply functional_extensionality.
          intro. destruct x. repeat destruct p. simpl. destruct o; auto.
        + simpl. apply functional_extensionality.
          intro. destruct x. destruct t. all: auto.
Qed.

(* the identity is a simple morphism *)
Lemma identity_simple 
    { Setup Msg State Error : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State} `{Serializable Error}
    (C : Contract Setup Msg State Error) : 
    is_simple_cm (id_cm C).
Proof. 
    unfold is_simple_cm.
    exists (id_fun Msg).
    exists (id_fun Setup).
    exists (id_fun State).
    exists (id_fun Error).
    assert (forall (c : Chain) (ctx : ContractCallContext) (s : Setup),
            init_result_transform (id_fun State) (id_fun Error) (init C c ctx s) =
            init C c ctx (id_fun Setup s)).
    intros. unfold init_result_transform. unfold id_fun; simpl. destruct (init C c ctx s); auto.
    rename H3 into id_init.
    exists id_init.
    assert (forall (c : Chain) (ctx : ContractCallContext) (st : State) (op_msg : option Msg),
            recv_result_transform (id_fun State) (id_fun Error) (receive C c ctx st op_msg) =
            receive C c ctx (id_fun State st) (option_map (id_fun Msg) op_msg)).
    intros. unfold recv_result_transform. unfold option_map. unfold id_fun; simpl.
    destruct op_msg.
    destruct (receive C c ctx st (Some m)); auto. destruct t; auto.
    destruct (receive C c ctx st None); auto. destruct t; auto.
    rename H3 into id_recv.
    exists id_recv.
    (* prove that id_cm C is simple wrt the above definitions *)
    unfold id_cm. unfold simple_cm.
    apply is_eq_cm.
    - apply is_eq_cm_init.
        + simpl. unfold id_fun. apply functional_extensionality. 
          intro. destruct x. destruct p. auto.
        + simpl. unfold id_fun. apply functional_extensionality. 
          intro. destruct x; auto.
    - apply is_eq_cm_recv.
        + simpl. unfold id_fun. apply functional_extensionality. 
          intro. destruct x. repeat destruct p. destruct o; auto.
        + simpl. unfold id_fun. apply functional_extensionality. 
          intro. destruct x; auto. destruct t. auto.
Qed.

End SimpleContractMorphism.


Section ChainMorphism.

(* We introduce the notion of a morphism of chains, which is a morphism on linked lists. *)
Record ChainMorphism := build_chain_morphism {
    chainstate_morph : ChainState -> ChainState ; 
    empty_fixpoint : chainstate_morph empty_state = empty_state ; 
    chainstep_morph : 
        forall bstate1 bstate2, 
        ChainStep bstate1 bstate2 -> 
        ChainStep (chainstate_morph bstate1) (chainstate_morph bstate2) ;
}.

(** Composition of chain morphisms *)
(* an auxiliary lemma *)
Lemma compose_fixpoint_result (chm1 chm2 : ChainMorphism) : 
    compose (chainstate_morph chm2) (chainstate_morph chm1) empty_state = 
    empty_state.
Proof.
    unfold compose.
    rewrite (empty_fixpoint chm1).
    rewrite (empty_fixpoint chm2).
    reflexivity.
Qed.

(* definition of composition *)
Definition composition_chm (chm2 chm1 : ChainMorphism) : ChainMorphism := {| 
    chainstate_morph := compose (chainstate_morph chm2) (chainstate_morph chm1) ;
    empty_fixpoint   := compose_fixpoint_result (chm1) (chm2) ;
    chainstep_morph  := (fun b1 b2 => 
        compose 
            (chainstep_morph chm2 
                (chainstate_morph chm1 b1) 
                (chainstate_morph chm1 b2)) 
            (chainstep_morph chm1 b1 b2)) ;
|}.

(* composition is associative *)
Lemma composition_assoc_chm : forall chm1 chm2 chm3, 
    composition_chm (composition_chm chm3 chm2) chm1 = 
    composition_chm chm3 (composition_chm chm2 chm1).
Proof.
    intros. unfold composition_chm. 
    f_equal. apply proof_irrelevance.
Qed.

(* the identity chain morphism *)
Lemma empty_fixpoint_id : 
    @id ChainState empty_state = empty_state.
Proof. auto. Qed.

Definition id_chm : ChainMorphism := {| 
    chainstate_morph := @id ChainState ; 
    empty_fixpoint := empty_fixpoint_id ;
    chainstep_morph := (fun b1 b2 => id_fun (ChainStep b1 b2)) ; |}.

Lemma composition_chm_left : forall chm, composition_chm id_chm chm = chm.
Proof.
    intro. unfold composition_chm. 
    destruct chm. f_equal. apply proof_irrelevance. 
Qed.

Lemma composition_chm_right : forall chm, composition_chm chm id_chm = chm.
Proof. 
    intro. unfold composition_chm. 
    destruct chm. f_equal. apply proof_irrelevance.
Qed.

(* chain isomoprhisms, which are bisimulations of blockchains *)
Definition is_iso_chm (f g : ChainMorphism) : Prop := 
    composition_chm g f = id_chm /\ 
    composition_chm f g = id_chm.

(* injections *)
Definition is_inj_chm (i : ChainMorphism) : Prop :=
    is_inj (chainstate_morph i).

(* surjections *)
Definition is_surj_chm (p : ChainMorphism) : Prop :=
    is_surj (chainstate_morph p).

(* chain monos *)
Definition is_monic_chm (i : ChainMorphism) : Prop := 
    forall f f', 
    composition_chm i f = composition_chm i f' -> f = f'.

(* chain epis *)
Definition is_epic_chm (p : ChainMorphism) : Prop := 
    forall f f',
    composition_chm f p = composition_chm f' p -> f = f'.

(* chain morphisms take reachable states to reachable states *)
Lemma chm_trace_to_trace : forall bstate1 bstate2 
    (trace : ChainTrace bstate1 bstate2) (chm : ChainMorphism),
    ChainTrace (chainstate_morph chm bstate1) (chainstate_morph chm bstate2).
Proof.
    intros. destruct chm as [cstate_morph empty_fixpoint cstep_morph]. cbn.
    induction trace.
    -   constructor.
    -   pose proof (cstep_morph mid to l).
        repeat (econstructor; eauto).
Qed.

Theorem reachable_to_reachable : forall bstate (chm : ChainMorphism), 
    reachable bstate -> reachable (chainstate_morph chm bstate).
Proof.
    intros.
    unfold reachable in H. destruct H. unfold reachable.
    pose proof (chm_trace_to_trace empty_state bstate X chm) as X'.
    rewrite (empty_fixpoint chm) in X'.
    constructor.
    exact X'.
Qed.

Lemma chm_reachable_through : forall bstate1 bstate2 
    (trace : reachable_through bstate1 bstate2) (chm : ChainMorphism),
    reachable_through (chainstate_morph chm bstate1) (chainstate_morph chm bstate2).
Proof.
    intros. 
    destruct trace. unfold reachable_through. destruct H0 as [trace]. split.
    - exact (reachable_to_reachable bstate1 chm H).
    - constructor. exact (chm_trace_to_trace bstate1 bstate2 trace chm).
Qed.

End ChainMorphism.



Section ReachableChainMorphism.

(* Define the subtype of ChainState which are reachable states *)
Definition ReachableChainState := {bstate : ChainState | reachable bstate}.
Definition empty_reachable : ReachableChainState := 
    exist reachable empty_state reachable_empty_state.

(* We introduce the notion of a morphism of chains, which is a morphism on linked lists. *)
Record ReachableChainMorphism := build_reachable_chain_morphism {
    r_chainstate_morph : ReachableChainState -> ReachableChainState ; 
    r_empty_fixpoint  : r_chainstate_morph empty_reachable = empty_reachable ; 
    r_chainstep_morph :
        forall rstate1 rstate2, 
        ChainStep (proj1_sig rstate1) (proj1_sig rstate2) -> 
        ChainStep 
            (proj1_sig (r_chainstate_morph rstate1)) 
            (proj1_sig (r_chainstate_morph rstate2)) ;
}.

(* composition *)

(* composition is associative *)

(* the identity chain morphism *)

(* chain isomoprhisms, which are bisimulations of blockchains *)

(* a proof tactic for reachable states *)
Definition rstate_induction : 
    forall P : ReachableChainState -> Type,
    P empty_reachable -> 
    (forall (rstate : ReachableChainState) (m : P rstate) 
        (bstate : ChainState) (step : ChainStep (proj1_sig rstate) bstate),
    P (exist _ bstate (reachable_step (proj1_sig rstate) bstate (proj2_sig rstate) step)))
    -> forall rstate : ReachableChainState, P rstate.
Proof. Admitted.

End ReachableChainMorphism.

(** Contract Morphisms lift to Reachable Chain Morphisms *)
Section ReachableMorphismLift.
Context 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'}.

(* *)
Definition cm_to_r_chainstate_morph (f : ContractMorphism C C') :
    ReachableChainState -> ReachableChainState.
Proof.
    apply rstate_induction.
    -   exact empty_reachable.
    -   intros.
        (* first construct the new bstate *) 

        (* then construct the new step *) 
Admitted.    

    
(* the lifting result *)
Definition cm_lift_to_rchm (f : ContractMorphism C C') : ReachableChainMorphism.
Proof.
    assert (r_chainstate_morph : ReachableChainState -> ReachableChainState).
    - admit.
    -  apply (build_reachable_chain_morphism r_chainstate_morph).
Admitted.

End ReachableMorphismLift.

(** Simple Contract Morphisms lift to Chain Morphisms *)
Section ContractMorphismLift.
Context 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    {C : Contract Setup Msg State Error} {C' : Contract Setup' Msg' State' Error'}.


(* the lifting function *)
Definition lift_chainstate_morph (f : ContractMorphism C C') : ChainState -> ChainState := todo "".
    (*  *)
    
Definition lift_empty_fixpoint (f : ContractMorphism C C') : 
    lift_chainstate_morph f empty_state = empty_state := todo "".

Definition lift_chainstep_morph (f : ContractMorphism C C') : 
    forall bstate1 bstate2, 
    ChainStep bstate1 bstate2 -> 
    ChainStep 
        (lift_chainstate_morph f bstate1) (lift_chainstate_morph f bstate2) := todo "".

Definition simple_cm_lift_to_chm (f : ContractMorphism C C') : ChainMorphism :=
    build_chain_morphism
        (lift_chainstate_morph f)
        (lift_empty_fixpoint f)
        (lift_chainstep_morph f).

Lemma c_c'_swap : 
    forall (bstate : ChainState) caddr (f : ContractMorphism C C'),
    env_contracts bstate caddr = Some (C : WeakContract) -> 
    env_contracts (chainstate_morph (simple_cm_lift_to_chm f) bstate) caddr = Some (C' : WeakContract).
Proof.
    intros.
Admitted.

End ContractMorphismLift.


(** We now examine how lifted morphisms behave with regard to morphism composition *)
Section ContractMorphismLiftCompose.

(* id_cm lifts to id_chm *)
Lemma id_cm_to_id_chm 
    { Setup Msg State Error : Type }
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    { C : Contract Setup Msg State Error } : 
    simple_cm_lift_to_chm (id_cm C) = id_chm.
Proof. Admitted.

(* compositions lift to compositions *)
Lemma cm_lift_compose 
    { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
    `{Serializable Msg}    `{Serializable Setup}    `{Serializable State}    `{Serializable Error}
    `{Serializable Msg'}   `{Serializable Setup'}   `{Serializable State'}   `{Serializable Error'}
    `{Serializable Msg''}  `{Serializable Setup''}  `{Serializable State''}  `{Serializable Error''}
    { C : Contract Setup Msg State Error } 
    { C' : Contract Setup' Msg' State' Error' }
    { C'' : Contract Setup'' Msg'' State'' Error'' } : 
    forall (f : ContractMorphism C C') (g : ContractMorphism C' C''),
    composition_chm (simple_cm_lift_to_chm g) (simple_cm_lift_to_chm f) = 
    simple_cm_lift_to_chm (composition_cm g f).
Proof. Admitted.

(* isomorphisms lift to isomorphisms *)
Lemma iso_cm_to_iso_chm 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    { C : Contract Setup Msg State Error } 
    { C' : Contract Setup' Msg' State' Error' } : 
    forall (f : ContractMorphism C C') (g : ContractMorphism C' C), 
    is_iso_cm f g -> 
    is_iso_chm (simple_cm_lift_to_chm f) (simple_cm_lift_to_chm g).
Proof.
    intros * is_iso.
    unfold is_iso_chm. unfold is_iso_cm in is_iso. 
    destruct is_iso as [iso_to iso_from].
    split.
    -   rewrite (cm_lift_compose f g). rewrite iso_to. 
        rewrite id_cm_to_id_chm. reflexivity.
    -   rewrite (cm_lift_compose g f). rewrite iso_from.   
        rewrite id_cm_to_id_chm. reflexivity.
Qed.

(* TODO 
Lemma inj_lifts_to_inj
Lemma surj_lifts_to_surj
*)

End ContractMorphismLiftCompose.


Section Equivalences.

(* equivalence of contracts *)
Definition are_equiv 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C  : Contract Setup  State  Msg  Error)
    (C' : Contract Setup' State' Msg' Error') : Prop := 
    exists (f : ContractMorphism C C') (g : ContractMorphism C' C),
    is_iso_cm f g.

(* weak equivalence of contracts *)
Definition are_weakly_equiv 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C  : Contract Setup  State  Msg  Error)
    (C' : Contract Setup' State' Msg' Error') : Prop := 
    exists (f g : ChainMorphism), 
    is_iso_chm f g /\
    forall (bstate : ChainState) caddr, 
    (env_contracts bstate caddr = Some (C : WeakContract)  
        -> env_contracts (chainstate_morph f bstate) caddr = Some (C' : WeakContract)) /\
    (env_contracts bstate caddr = Some (C' : WeakContract) 
        -> env_contracts (chainstate_morph g bstate) caddr = Some (C : WeakContract)).

End Equivalences.



End ContractMorphisms.