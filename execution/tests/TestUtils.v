Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

From ConCert Require Import Serializable. Import SerializedType.
From ConCert Require Import Blockchain.
From ConCert Require Import Congress.
From ConCert Require Import ResultMonad.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import BoundedN. Import BoundedN.Stdpp.

From Coq Require Import List. Import ListNotations.
From Coq Require Import Program.Basics.
Require Import Containers.

Global Definition AddrSize := (2^8)%N.
Global Instance LocalChainBase : ChainBase := LocalChainBase AddrSize.
Global Instance ChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.
Notation "f 'o' g" := (compose f g) (at level 50).

Definition creator : Address :=
  BoundedN.of_Z_const AddrSize 10.
Definition person_1 : Address :=
  BoundedN.of_Z_const AddrSize 11.
Definition person_2 : Address :=
  BoundedN.of_Z_const AddrSize 12.
Definition person_3 : Address :=
  BoundedN.of_Z_const AddrSize 13.
Definition person_4 : Address :=
  BoundedN.of_Z_const AddrSize 14.
Definition person_5 : Address :=
  BoundedN.of_Z_const AddrSize 15.

Definition test_chain_addrs := [person_1; person_2; person_3; person_4; person_5].

(* Misc utility functions *)
Open Scope list_scope.
Open Scope string_scope.

Definition zero_address : Address := BoundedN.of_Z_const AddrSize 0.

Definition isNone {A : Type} (a : option A) := match a with | Some _ => false | None => true end.
Definition isSome {A : Type} (a : option A) := negb (isNone a).

Definition string_of_FMap {A B : Type}
                         `{countable.Countable A}
                         `{base.EqDecision A}
                          (showA : A -> string)
                          (showB : B -> string)
                          (m : FMap A B) : string :=
  "[" ++
    String.concat "; " (map (fun '(a, b) => showA a ++ "-->" ++ showB b) (FMap.elements m))
  ++ "]".

Definition filter_FMap {A B : Type}
                      `{countable.Countable A}
                      `{base.EqDecision A}
                       (f : (A * B) -> bool)
                       (m : FMap A B)
                       : FMap A B :=
  let l := FMap.elements m in
  let filtered_l := List.filter (fun p => f p) l in
  FMap.of_list filtered_l.

Definition map_values_FMap {A B C: Type}
                      `{countable.Countable A}
                      `{base.EqDecision A}
                       (f : B -> C)
                       (m : FMap A B)
                       : FMap A C :=
  let l := FMap.elements m in
  let mapped_l := List.map (fun p => (fst p, f (snd p))) l in
  FMap.of_list mapped_l.

Definition FMap_find_ {A B : Type}
                    `{countable.Countable A}
                    `{base.EqDecision A}
                     (k : A)
                     (m : FMap A B)
                     (default : B)  :=
  match FMap.find k m with
  | Some v => v
  | None => default
  end.

Close Scope string_scope.
Fixpoint split_at_first_satisfying_fix {A : Type} (p : A -> bool) (l : list A) (acc : list A) : option (list A * list A) :=
  match l with
  | [] => None
  | x::xs => if p x
            then Some (acc ++ [x], xs)
            else (split_at_first_satisfying_fix p xs (acc ++ [x]))
  end.

Definition split_at_first_satisfying {A : Type} (p : A -> bool) (l : list A) : option (list A * list A) :=
  split_at_first_satisfying_fix p l [].

(* Helper function for backtrack_result. It picks and removes an element from a list of result generators. *)
Fixpoint pickDrop {T E}
                  (default : E)
                  (xs : list (nat * G (result T E))) 
                  (n : nat) 
                  : nat * G (result T E) * list (nat * G (result T E)) :=
  match xs with
    | nil => (0, returnGen (Err default), nil)
    | (k, x) :: xs =>
      if (n <? k) then  (k, x, xs)
      else let '(k', x', xs') := pickDrop default xs (n - k)
          in (k', x', (k,x)::xs')
  end. 

(* Backtracking generator for results instead of Option. Works the same way as backtrack. *)
Fixpoint backtrack_result_fix {T E} (default : E) (fuel : nat) (gs : list (nat * G (result T E))) : G (result T E) :=
  match fuel with
  | 0 => returnGen (Err default)
  | S fuel' => idx <- choose (0, fuel') ;;
        let '(k, g, gs') := pickDrop default gs idx in
        ma <- g ;;
        match ma with
        | Err e => backtrack_result_fix default fuel' gs'
        | Ok r => returnGen (Ok r)
        end
  end.

Definition backtrack_result {T E} (default : E) (gs : list (nat * G (result T E))) : G (result T E) :=
  backtrack_result_fix default (length gs) gs.


(* Utils for Show instances *)
Open Scope string_scope.

Definition sep : string := ", ".
Derive Show for unit.

Definition deserialize_to_string {ty : Type}
                                `{Serializable ty}
                                `{Show ty}
                                 (s : SerializedValue) : string :=
  match @deserialize ty _ s with
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
Open Scope bool_scope.

Definition get_contract_state (state : Type) `{Serializable state} env addr : option state :=
  let cstates := env.(env_contract_states) in
  match cstates addr with
  | Some ser_state =>
    match @deserialize state _ ser_state with
    | Some state => Some state
    | None => None
    end 
  | None => None
  end. 

(* Utils for Generators *)

Definition elems_opt {A : Type} (l : list A) : GOpt A :=
  match l with
  | x::xs => liftM Some (elems_ x xs)
  | _ => returnGen None end.

Definition returnGenSome {A : Type} (a : A) := returnGen (Some a).


Definition sampleFMapOpt {A B : Type}
                        `{countable.Countable A}
                        `{base.EqDecision A}
                         (m : FMap A B)
                         : G (option (A * B)) :=
  let els := FMap.elements m in
  match els with
  | e :: _ => liftM Some (elems_ e els)
  | [] => returnGen None
  end.

Definition sampleFMapOpt_filter {A B : Type}
                        `{countable.Countable A}
                        `{base.EqDecision A}
                         (m : FMap A B)
                         (f : (A * B) -> bool)
                         : GOpt (A * B) :=
  let els := FMap.elements m in
  match els with
  | e :: _ => liftM Some (elems_ e (List.filter f els))
  | [] => returnGen None
  end.

Definition sample2UniqueFMapOpt
                         {A B : Type}
                        `{countable.Countable A}
                        `{base.EqDecision A}
                         (m : FMap A B)
                         : GOpt ((A * B) * (A * B)) :=
  bindGenOpt (sampleFMapOpt m) (fun p1 =>
    let key1 := fst p1 in
    let val1 := snd p1 in
    bindGenOpt (sampleFMapOpt (FMap.remove key1 m)) (fun p2 =>
      returnGenSome (p1, p2)
    )
  ).

(* Although the type is GOpt ...) it will never generate None values.
   Perhaps this is where we should use generators with property proof relevance? Future work... *)
Definition gBoundedNOpt (bound : N) : G (option (BoundedN.BoundedN bound)) :=
  n <- arbitrarySized (N.to_nat bound) ;; (* we exploit that arbitrarySized n on nats automatically bounds the value by <= n *)
  returnGen (@decode_bounded bound (Pos.of_nat n)).

Definition gBoundedN : G (BoundedN.BoundedN AddrSize) :=
  bn <- gBoundedNOpt AddrSize ;;
  returnGen match bn with
    | Some b => b
    (** The None case should never happen since 'arbitrarySized' on AddrSize already ensures that
        n <= AddrSized. **)
    | None => BoundedN.of_Z_const AddrSize 0
  end.

Instance genBoundedN : Gen (BoundedN.BoundedN AddrSize) :=
  {|
    arbitrary := gBoundedN
  |}.

Instance genAddress : Gen (@Address LocalChainBase) :=
  {|
    (* I could have just written 'arbitrary' here, but this is more explicit; and i like explicit code *)
    arbitrary := @arbitrary (BoundedN.BoundedN AddrSize) genBoundedN
  |}.

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

Instance genFMapSized {A B : Type}
                     `{Gen A}
                     `{Gen B}
                     `{countable.Countable A}
                     `{base.EqDecision A}
                      : GenSized (FMap A B) :=
{|
  arbitrarySized := @gFMapSized A B arbitrary arbitrary _ _ _
|}.

(* Sample (@gFMapSized nat nat arbitrary arbitrary _ _ _ 1). *)


Definition optToVector {A : Type} (n : nat): GOpt A -> G (list A) :=
  fun g =>
  l <- vectorOf n g ;;
  let l' := fold_left (fun acc aopt => match aopt with
                          | Some a => a :: acc
                          | None => acc
                          end) l []
  in returnGen l'.

(* Utils for QuickChick *)

(* Little helper to avoid having to write out matches with "false ==> true" in None case all the time *)
Definition isSomeCheck {A B : Type} `{Checkable B} (a : option A) (f : A -> B) : Checker :=
match a with
  | Some v => checker (f v)
  | None => false ==> true
end.

(* A shallow way of embedding 'exists' in QC. Currently not very general, since we cant properly nest existPs
   because the predicate function returns a bool, and not a Checker. Need to review if this is even possible. *)
Local Open Scope string_scope.
Definition existsP {A prop : Type}
                  `{Checkable prop}
                  `{Show A}
                   (g : G A)
                   (p : A -> bool) :=
  expectFailure (forAll g
  (fun a => whenFail ("Success - found witness satisfying the predicate!" )
    (negb (p a)))).

Definition existsPShrink
                   {A prop : Type}
                  `{Checkable prop}
                  `{Show A}
                  `{Shrink A}
                   (g : G A)
                   (p : A -> bool) :=
  expectFailure (forAllShrink g shrink
  (fun a => whenFail ("Success - found witness satisfying the predicate!" )
    (negb (p a)))).

(* QuickChick (
  existsP arbitrary (fun a => a <=? a)
). *)

(* the shrinking variant may be more useful in some cases: *)
(* QuickChick (
  existsP arbitrary (fun (l : list nat) => 5 <? fold_left plus l 0 )
). *)
(* coqtop-stdout:[1; 2; 5; 0; 3]
Success - found witness satisfying the predicate!
+++ Failed (as expected) after 6 tests and 0 shrinks. (0 discards)
   *)
(* QuickChick (
  existsPShrink arbitrary (fun (l : list nat) => 5 <? fold_left plus l 0 )
). *)
(*
coqtop-stdout:[4; 2]
Success - found witness satisfying the predicate!
+++ Failed (as expected) after 5 tests and 3 shrinks. (0 discards)
 *)

Definition conjoin_map {A prop : Type}
                      `{Checkable prop}
                       (f : A -> prop)
                       (l : list A) := conjoin (map (checker o f) l).

Definition discard_empty {A prop : Type} 
                        `{Checkable prop} 
                         (l : list A) 
                         (f : list A -> prop) : Checker :=
  match l with
  | [] => false ==> true
  | _ => checker (f l)
  end.


Definition forEachMapEntry {A B prop : Type}
                          `{countable.Countable A}
                          `{base.EqDecision A}
                          `{Checkable prop}
                           (m : FMap A B)
                           (pf : A -> B -> prop)
                           : Checker :=
  let pf_ p := pf (fst p) (snd p) in
  conjoin_map pf_ (FMap.elements m).

(* Repeats a generator for each element in the given list *)
Fixpoint repeatWith {A prop : Type}
                   `{Checkable prop}
                    (l : list A)
                    (c : A -> prop)
                    := conjoin (map (checker o c) l).

(* Repeats a generator n times *)
Definition repeatn (n : nat) (c : Checker) := repeatWith (seq 0 n) (fun _ => c).

(* Converts a discarded test into a succesful test *)
Definition discardToSuccess {prop} `{Checkable prop} (p : prop): Checker :=
  mapTotalResult (fun res => match res.(ok) with
                             | None => updOk res (Some true)
                             | _ => res
                             end) p.
  
(* QuickChick (discardToSuccess (false ==> true)). *)
(* +++ Passed 10000 tests (0 discards) *)
(* QuickChick (discardToSuccess (conjoin [false==>true; checker true])). *)
(* +++ Passed 10000 tests (0 discards) *)
(* QuickChick (conjoin [discardToSuccess (false==>true); checker true]). *)
(* +++ Passed 10000 tests (0 discards) *)
(* QuickChick (discardToSuccess true). *)
(* +++ Passed 10000 tests (0 discards) *)
(* QuickChick (discardToSuccess false). *)
(* *** Failed after 1 tests and 0 shrinks. (0 discards) *)

(* discard-friendly variant of conjoin where discarded tests will NOT cause the conjoin
   combinator to also result in a discard. Specifically, conjoin_no_discard [false==>true] tests succesfully,
   whereas conjoin [false==>true] results in a discarded test. *)
Definition conjoin_no_discard {prop} `{Checkable prop} (l : list prop) : Checker := 
  conjoin_map discardToSuccess l.

(* QuickChick (conjoin_no_discard [false==>true; checker true]). *)
(* +++ Passed 10000 tests (0 discards) *)
