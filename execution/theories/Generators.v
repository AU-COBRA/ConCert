Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
(* For monad notations *)
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

From Coq Require Import List.
From Coq Require Import Strings.BinaryString.
Import ListNotations.

(* Module DoNotation.
Import ssrfun.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.
Import DoNotation. *)

(* Declare Instance genAmountSized : GenSized Amount.
Declare Instance showAmount : Show Amount.
Declare Instance shrinkAmount : Shrink Amount. *)


Instance showAmount : Show Amount :=
  {|
    show := @show Z showZ
  |}.

Instance genAmountSized : GenSized Amount :=
  {|
    arbitrarySized := @arbitrarySized Z _ 
  |}.

Instance shrinkAmount : Shrink Amount := 
  {|
    shrink := @shrink Z _
  |}.

  
(* dummy implementation for now *)
Definition empty_str : string := "".
Definition sep : string := ", ".



Record BaseGens {Setup Msg State : Type} := 
  mkBaseGens {
    (* Address          : Type; *)
    genAddress       : G Blockchain.Address;
    genSetup         : G Setup;
    genMsg           : G Msg;
    genState         : G State;
    genSerializedVal : G SerializedValue;
  }.


Open Scope string_scope.
Instance showChain (BaseTypes : ChainBase) : Show (@Chain BaseTypes) :=
  {|
    show c := 
      let height := show (chain_height c) in
      let slot := show (current_slot c) in
      let fin_height := show (finalized_height c) in
        "{" ++ height ++ sep ++ slot ++ sep ++ fin_height ++ "}"
  |}.

Close Scope string_scope.



Fixpoint mkMapFromList {B : Type}
                       (address_eqb : Address -> Address -> bool)
                       (genB : G B)
                       (l : list Address) 
                       : G (Address -> B) :=
  match l with
  | [] => b <- genB ;; returnGen (fun x => b)
  | a::l' =>
    b <- genB ;;
    liftM 
      (fun (mp : Address -> B) (x : Address) 
        => if address_eqb x a then b else mp x) 
      (mkMapFromList address_eqb genB l')
  end.

Definition mkMapFromListGen {B : Type}
                          (address_eqb : Address -> Address -> bool)
                          (genB : G B)
                          (genListA : G (list Address)) 
                          : G (Address -> B) :=
  listA <- genListA ;; mkMapFromList address_eqb genB listA.

(* Makes a generator for BlockChains, given generators for the necessary types: Address, Setup, Msg, State, SerializedValue. 
   Ensures that all address usages are consistent with the generated address mapping. *)
Definition mkChainGen {Setup Msg State : Type}
                        (baseGens : @BaseGens Setup Msg State) (BaseTypes : ChainBase)
                        : nat -> G (@Chain BaseTypes)  := 
  fun n =>
  (* First construct context of Contract Addresses. *)
  let g_address := genAddress baseGens in
  let addr_eqb : Address -> Address -> bool := address_eqb in
  let addr_list_gen : G (list Blockchain.Address) := vectorOf n g_address in
    ch_height  <- arbitrarySized n ;;
    cur_slot   <- arbitrarySized ch_height ;; (* We make sure current slot is <= chain height *)
    mp         <- mkMapFromListGen addr_eqb (sized arbitrarySized) addr_list_gen ;; 
    returnGen (build_chain ch_height cur_slot n (fun (a : Blockchain.Address) => Z.of_nat n)).

  (* For now, shrinking does nothing *)
Instance shrinkChain (BaseTypes : ChainBase) : Shrink (@Chain BaseTypes) :=
  {|
    shrink c := cons c nil
  |}.



Module LocalBlockchainGens.

Import BoundedN.Stdpp.
Global Opaque Address. 

Print LocalChainBase.

Definition b10 : Address := BoundedN.of_Z_const AddrSize 10.
Definition b9 : option (BoundedN.BoundedN AddrSize) := @BoundedN.of_nat AddrSize 9.


(* Show instances *)
Open Scope string_scope.
(* For a more memory efficient method, use BinaryString.of_N instead (but this prints numbers in binary notation, ie. eg. 0b0010) *)
Instance showN : Show N :=
  {|
    show n := show (N.to_nat n)   
  |}.


(* We dont show the bound because it may be a very large number which, when converted to nat and then to string, gives a memory overflow. *)
Instance showBoundedN {bound : N} `{Show N} : Show (BoundedN.BoundedN bound) :=
  {|
    show bn := match bn with | BoundedN.bounded n _ => show n ++ "%" ++ show bound end  
  |}.
 

Instance showBoundedNAddrSize : Show (BoundedN.BoundedN AddrSize) :=
  {|
    show := @show (BoundedN.BoundedN AddrSize) showBoundedN
  |}.

Instance showAddress : Show Address :=
  {|
    show := @show (BoundedN.BoundedN AddrSize) showBoundedN
  |}.



Close Scope string_scope.

(* Generators *)
Definition genZ : G Z := arbitrary.	


Derive Show for positive.
Derive Arbitrary for positive.
Derive GenSized for positive.

(* Although the type is G (option ...) it will never generate None values *)
Definition genBoundedNOpt (bound : N): G (option (BoundedN.BoundedN bound)) :=
  n <- arbitrarySized (N.to_nat bound) ;; (* we exploit that arbitrarySized n on nats automatically bounds the value by <= n *)
  returnGen (@decode_bounded bound (Pos.of_nat n)).


Definition genBoundedN : G (BoundedN.BoundedN AddrSize) :=
  bn <- genBoundedNOpt AddrSize ;;
  returnGen match bn with
    | Some b => b
    (** The None case should never happen since 'arbitrarySized' on AddrSize already ensures that
        n <= AddrSized. **)
    | None => BoundedN.of_Z_const AddrSize 0
  end. 

Definition genAddress : G Address := genBoundedN.



End LocalBlockchainGens.


Import LocalBlockchainGens.

Sample genAddress.


Sample (@arbitrarySized Chain (genChainSized LocalChainBase) 2).


Sample (@arbitrarySized Amount _ 2).

Open Scope nat_scope.
Definition n_is_zero_nat (n : nat) := n =? 0.
(* QuickChick n_is_zero_nat. *)


(* Example of how to sample a specific type? *)
Sample (@arbitrarySized Z genZSized 2).
Sample (@arbitrarySized Amount genZSized 2).
(* How to go from arbitrarySized to arbitrary *)
Print sized.
Sample (@sized Z (@arbitrarySized Z genZSized)).


Open Scope Z_scope.
Definition n_is_zero (n : Z) := n =? 0.
(* QuickChick n_is_zero. *)




