Require Import ZArith.
Require Import Ascii.
Require Import String.
Require Import List.

(* Open Scope Z. *)
Open Scope char_scope.

(* Check 1 : Z. *)

Check true : bool.

Check false : bool.

Check "c"  : ascii.

(* Open Scope string_scope. *)
(* Check "hello" : string. *)

Check (1,"c") :  nat * ascii.

Check Some 123 : option nat.

Check (None : option _).
Check (@None : forall A : Type, option A).

Check (inl 123 : sum nat _).

Open Scope string_scope.

Check (inr "Problem") : sum _ string.

Import ListNotations.
Check [1;2;3] : list nat.


(* No arrays *)

Require Import MSets MSetList.
Module NatSet := MSetList.Make PeanoNat.Nat.
Module NatSetProp := MSetProperties.WPropertiesOn PeanoNat.Nat NatSet.

Definition nat_set := NatSetProp.of_list [1;2;3].


Require Import FMaps FMapList.
Module NatMap := FMapList.Make Nat_as_OT.
Module NatMapProp := FMapFacts.WProperties_fun Nat_as_OT NatMap.

Definition nat_map := NatMapProp.of_list [(1,true);(2,false)].

(* Unit type *)
Check (tt : unit).


Inductive status := Todo | Doing | Done.

Check Todo : status.

Check Doing : status.

Check Done : status.

Print option.

Definition addOne (x: nat) : nat :=  x + 1.

Definition add (x y : nat) : nat := x + y.

Definition add' : nat -> nat -> nat := plus.

Definition poly {A : Type} (x : A) : nat := 14.

Definition square :=
  fun n => n^2.

Definition squares :=
  List.map (fun n => n^2) (List.seq 1 100).

SearchPattern (string -> string -> _).

Require Import Sorting.

Module NameOrder <: TotalLeBool.
  (* Ordering strings according to their length.
     Unfortunatelly, lexicographic ordering for strings
      is not defined in the StdLib of Coq *)
  Definition t := string.
  Definition leb x y :=
    NatOrder.leb (String.length x) (String.length y).
  Theorem leb_total :
    forall a1 a2, is_true (leb a1 a2) \/ is_true (leb a2 a1).
  Proof. intros. apply NatOrder.leb_total. Qed.
End NameOrder.

Module NameSort := Sort NameOrder.

Definition viewNames names :=
  String.concat ", " (NameSort.sort names).

Definition viewNames' :=
  compose (String.concat ", ") NameSort.sort.

Open Scope program_scope.
Definition viewNames'' := (String.concat ", ") ∘ NameSort.sort.

Require Import PeanoNat.

Open Scope nat.
Definition cond1 power := if 9000 <? power then "Wow!" else "Meh".

Definition cond2 key n:=
  if key =? 40 then n + 1
  else if key =? 38 then
         n - 1
       else
         n.

Definition case1 {A} (maybe : option (list A)) : list A :=
  match maybe with
    Some xs => xs
  | None    => []
  end.

Definition case2 {A} (xs : list A) :=
  match xs with
    hd::tl => Some (hd,tl)
  | []     => None
  end.

Definition fix1 :=
  fix fib n :=
    match n with
      0 => 1
    | 1 => 1
    | S n => fib n + fib (n-1)
    end.

Definition let1 :=

(* using natural numbers for simplicity *)
let
  ( three, four ) :=
     ( 3, 4 )
in
let hypotenuse a b :=
       Nat.sqrt (a^2 + b^2)
in
hypotenuse three four.

(* Modules in Coq are somewhat similar to OCaml.
   They represent powerful abstraction
   mechanism through parameterized modules -
   functors *)

(* Require module without opening it *)
Require List.

(* Qualified access to the definitions *)
(* List.map *)

(* Open a module *)
Import List.

Module L := List.

Module Type ListSig.
  Parameter my_map : forall {A B : Type}, (A -> B) -> list A -> list B.
  Parameter my_fold_left : forall {A B : Type}, (A -> B -> A) -> list B -> A -> A.
End ListSig.

Module MyList : ListSig.
  Definition my_map := List.map.
  Definition my_fold_left := List.fold_left.
End MyList.

Definition answer : nat :=
  42.

Definition factorial (n : nat) : nat :=
  List.fold_left mult (List.seq 1 n) 1.

(* Coq has no anonymous records *)
Record point :=
  { x:nat; y:nat }.

(* Or with explicit constructor *)
Record point1 :=
  Point { x1:nat; y1:nat }.

Definition pnt := {|x:=3; y:=4|}.

Definition zzz := pnt.(x). (* field access *)

(* No special record update syntax by default,
   but available through libraries
   e.g https://github.com/tchajed/coq-record-update *)

Definition set_x (p : point) (x : nat) : point :=
  {| x:=x; y:=p.(y) |}.


(* Pattern-matching on records *)
Definition distance (x : point) :=
  match x with
    {| x:=x; y:=y|} => Nat.sqrt (x^2 + y^2)
  end.

Definition distance' (x : point1) :=
  match x with
    Point x y => Nat.sqrt (x^2 + y^2)
  end.

Definition distance (p : point) : nat :=
  Nat.sqrt (p.(x)^2 + p.(y)^2).

(* The same [Definition] keyword can be used to define aliases *)
Definition name := string.
Definition age := nat.

(* Alternatively, [Notation] can be used *)
Notation "'name'" := string.
Notation "'age'" := nat.

Definition info : name * age := ("Steve", 28).

(* since there are no anonymous records,
  this is not an alias *)
(* Record point := *)
(*   { x:nat; y:nat }. *)

Definition origin : point := {| x:=0; y:=0 |}.

