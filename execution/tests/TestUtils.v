Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable. Import SerializedType.
From ConCert Require Import BoundedN ChainedList.



From Coq Require Import List. Import ListNotations.
From Coq Require Import Program.Basics.
Require Import Containers.

Global Definition AddrSize := (2^8)%N.
Instance LocalChainBase : ChainBase := LocalChainBase AddrSize.
Instance LocalChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.

Notation "f 'o' g" := (compose f g) (at level 50).


(* Misc utility functions *)
Open Scope list_scope.
Open Scope string_scope.

Fixpoint mkMapFromLists {A B : Type}
                       (a_eqb : A -> A -> bool)
                       (default : B)
                       (l : list A) 
                       (lb : list B)
                       : A -> B :=
  match (l,lb) with
  | ([],[]) => fun x => default
  | (a::l', b::lb') => 
    fun (x : A) => if a_eqb x a then b else (mkMapFromLists a_eqb default l' lb') x 
  | (_,_) => fun x => default
  end.

Definition string_of_FMap {A B : Type}
                         `{countable.Countable A}
                         `{base.EqDecision A}
                          (showA : A -> string) 
                          (showB : B -> string) 
                          (m : FMap A B) : string :=
  show (map (fun p => showA (fst p) ++ "-->" ++ showB (snd p)) (FMap.elements m)).


(* Utils for Show instances *)

Definition empty_str : string := "".
Definition sep : string := ", ".
Derive Show for unit.

Definition deserialize_to_string (s : SerializedValue) : string := 
  match deserialize s with
  | Some v => show v
  | None => "?"
  end.

Instance showFMap {A B : Type}
                 `{countable.Countable A}
                 `{base.EqDecision A}
                 `{Show A} 
                 `{Show B}
                  : Show (FMap A B) :=
{|
  show := string_of_FMap show show
|}.

Close Scope string_scope.


(* Utils for Generators *)


Record ChainContext (BaseTypes : ChainBase) := 
  mkBaseGens {
    gAddress              : G (@Address BaseTypes);
    accounts              : list (@Address BaseTypes);
    contracts             : list (@Address BaseTypes);
    gContractAddr         : G (@Address BaseTypes);
    gAccountAddr          : G (@Address BaseTypes);    
  }.
  
(* Helpers for ChainContext. TODO: look into parameterising ChainBase *)
Definition ctx_gAccountAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gAccountAddr LocalChainBase ctx.
Definition ctx_gContractAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gContractAddr LocalChainBase ctx.
Definition ctx_gAnyAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gAddress LocalChainBase ctx.
Definition ctx_accounts (ctx : ChainContext LocalChainBase) : list Address := 
  @accounts LocalChainBase ctx.
Definition ctx_contracts (ctx : ChainContext LocalChainBase) : list Address := 
  @contracts LocalChainBase ctx.

Definition gZPositive := liftM Z.of_nat arbitrary.
Definition gZPositiveSized n := liftM Z.of_nat (arbitrarySized n).

(* Helper generator and show instance for arbitrary FMaps *)

Fixpoint gFMapSized {A B : Type} 
                    {gA : G A} 
                    {gB : G B}
                    `{countable.Countable A}
                    `{base.EqDecision A}
                     (n : nat) : G (FMap A B) :=
  match n with
  | 0 => returnGen FMap.empty
  | S n' =>
    a <- gA ;;
    b <- gB ;;
    m <- @gFMapSized _ _ gA gB _ _ _ n' ;;
    returnGen (FMap.add a b m)  
  end.

Fixpoint gFMapFromInput {A B : Type}
                       `{countable.Countable A}
                       `{base.EqDecision A}     
                        (l1 : list A)
                        (l2 : list B)
                        : G (FMap A B) :=
  match (l1, l2) with
  | (a::l1', b::l2') => liftM (FMap.add a b) (gFMapFromInput l1' l2')
  | (_, _) => returnGen FMap.empty
  end.

Instance genFMapSized {A B : Type} 
                     `{Gen A} 
                     `{Gen B}
                     `{countable.Countable A}
                     `{base.EqDecision A}
                      : GenSized (FMap A B) :=
{|
  arbitrarySized := @gFMapSized A B arbitrary arbitrary _ _ _
|}.

Sample (@gFMapSized nat nat arbitrary arbitrary _ _ _ 1).


Fixpoint vectorOfCount {A : Type}
                      `{countable.Countable A} 
                       (default : A)
                       (n : nat) : G (list A) := 
  match n with
  | 0    => returnGen []
  | S n' => 
    match (countable.decode o Pos.of_nat) n with
    | Some a => liftM (cons a) (vectorOfCount default n')
    | None => liftM (cons default) (vectorOfCount default n')
    end
  end.


(* Utils for QuickChick *)

Close Scope list_scope.