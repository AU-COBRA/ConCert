Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick.
From ExtLib.Structures Require Import Functor Applicative.


From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.

Print Amount.

Print Z.of_nat.

(* Declare Instance genAmountSized : GenSized Amount.
Declare Instance showAmount : Show Amount.
Declare Instance shrinkAmount : Shrink Amount. *)


Instance showAmount : Show Amount :=
  {|
    show := @show Z showZ
  |}.

Instance genAmountSized : GenSized Amount :=
  {|
    arbitrarySized := @arbitrarySized Z genZSized 
  |}.

Instance shrinkAmount : Shrink Amount := 
  {|
    shrink := @shrink Z shrinkZ
  |}.

(* making show and generator instances for the Chain type *)

(* dummy implementation for now *)
Definition empty_str : string := "".

Instance showChain (BaseTypes : ChainBase) : Show (@Chain BaseTypes) :=
  {|
    show c := show (chain_height c)
  |}.

Print Chain.

Instance genChainSized (BaseTypes : ChainBase) : GenSized (@Chain BaseTypes) :=
  {|
    arbitrarySized n := returnGen (build_chain n n n (fun (a : Address) => Z.of_nat n))
  |}.

Print shrink.


(* For now, shrinking does nothing *)
Instance shrinkChain (BaseTypes : ChainBase) : Shrink (@Chain BaseTypes) :=
  {|
    shrink c := cons c nil
  |}.

Print LocalChainBase.
Sample (@arbitrarySized Chain (genChainSized LocalChainBase) 2).

Print genAmountSized.

Definition a : Amount := 2.

Sample (@arbitrarySized Amount genAmountSized 2).



Print genZSized.
Definition n_is_zero_nat (n : nat) := n =? 0.
QuickChick n_is_zero_nat.
Print arbitrarySized.
(* Example of how to sample a specific type? *)
Sample (@arbitrarySized Z genZSized 2).
Print genAmountSized.
Sample (@arbitrarySized Amount genZSized 2).


Open Scope Z_scope.
Definition n_is_zero (n : Z) := n =? 0.

QuickChick n_is_zero.

Print sized.
Sample (@sized Z (@arbitrarySized Z genZSized)).

(* 
Instance sizedGenZ : GenSized Z :=
  {|
    arbitrarySized n := returnGen (Z.of_nat n)
  |}.

Print GenOfGenSized.


Definition genZ := @GenOfGenSized Z sizedGenZ.

(* Instance genZ : Gen Z :=
  {|
    arbitrary := returnGen Z0
  |}. *) *)

Check Amount.
Derive  Arbitrary for Amount.