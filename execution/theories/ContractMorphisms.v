(* A Description of Morphisms of Contracts *)

From Coq Require Import Basics.
From Coq Require Import ProofIrrelevance.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import FunctionalExtensionality.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractSystems.
From ConCert.Execution Require Import BuildUtils.

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

Section ContractMorphisms.
Context { Base : ChainBase }.

Section MorphismDefinition.

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

(* we define a (functional) equivalence of environments via a function : this is a bisimulation *)
Definition EnvironmentBisimulation (e1 e2 : Environment) : Prop := 
    todo "".

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
    forall (f : ContractMorphism C C') (g : ContractMorphism C' C),
    is_iso_cm f g -> 
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
    EnvironmentBisimulation env1' env2' := todo "".

(* if C and C' are isomorphic, then deploying  *)
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

Lemma act_preserves_equiv : 
    forall bstate1  bstate2,  EnvironmentBisimulation bstate1 bstate2 -> 
    forall bstate1' bstate2' act1 act2 new_acts,
        ActionEvaluation bstate1 act1 bstate1' new_acts -> 
        ActionEvaluation bstate2 act2 bstate2' new_acts -> 
        (* the act should be equivalent, not identical *)
        act1 = act2 -> (* TODO *)
        EnvironmentBisimulation bstate1' bstate2'.
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

(* results about monomorphisms *)
(* an EMBEDDING of traces *)

Definition embed_trace bstate bstate1 bstate2 :
    ChainTrace bstate bstate1 -> ChainTrace bstate bstate2 := todo "".

Definition trace_embedding 
        { Setup Setup' Msg Msg' State State' Error Error' : Type }
        `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
        `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
        {C1 : Contract Setup Msg State Error} {C2 : Contract Setup' Msg' State' Error'} : 
    forall (f : ContractMorphism C1 C2), 
    is_inj_cm f -> 
    (* start with a reachable state *)
    forall bstate, reachable bstate -> 
    (* compare deploying C vs C' *)
    forall (bstate1 bstate2 : ChainState) act_deploy_C1 act_deploy_C2 new_acts s1 s2 amt1 amt2,
    (* the environment we get by deploying C  *)
    ActionEvaluation bstate act_deploy_C1 bstate1 new_acts -> 
        act_deploy_C1.(act_body) = act_deploy amt1 C1  s1 ->
    (* the environment we get by deploying C'  *)
    ActionEvaluation bstate act_deploy_C2 bstate2 new_acts -> 
        act_deploy_C2.(act_body) = act_deploy amt2 C2 s2 ->
    (* they are deployed to the same address *)
    forall caddr1 caddr2,
        env_contracts bstate1 caddr1 = Some (C1 : WeakContract) -> 
        env_contracts bstate2 caddr2 = Some (C2 : WeakContract) ->
        caddr1 = caddr2 ->
    (* they are deployed BY the same address (and origin) *)
    act_deploy_C1.(act_from)   = act_deploy_C2.(act_from)   ->
    act_deploy_C1.(act_origin) = act_deploy_C2.(act_origin) ->
    (* any state reachable through bstate1 has a corresponding state reachable through bstate2 *)
    forall bstate1', reachable_through bstate1 bstate1' ->
    forall (trace1 : ChainTrace bstate bstate1'),
    exists bstate2' (trace2 : ChainTrace bstate bstate2'),
        reachable_through bstate2 bstate2' /\ 
        trace2 = embed_trace bstate bstate1' bstate2' trace1.
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

(* TODO : Result about surjections : possibly about rectacts, splitting C into C + C' via a retract *)
(*                                 : possibly about upgradeability too *)

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

(* TODO: this is more nuanced *)
Lemma null_morphism_unique : forall (f : ContractMorphism C null_contract), f = null_morphism.
Proof. 
    intro. apply is_eq_cm; try apply is_eq_cm_init; try apply is_eq_cm_recv; apply functional_extensionality; intro.
    -   destruct x as [x' s]. destruct x' as [c ctx].
        admit.
    -   destruct x. Admitted.

End TerminalContract.

End ContractMorphisms.