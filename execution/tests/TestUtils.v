Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

From ConCert Require Import Serializable. Import SerializedType.
From ConCert Require Import Blockchain.
From ConCert Require Import Congress.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import BoundedN ChainedList. Import BoundedN.Stdpp.

From Coq Require Import List. Import ListNotations.
From Coq Require Import Program.Basics.
Require Import Containers.
Require Import ResultMonad.

Global Definition AddrSize := (2^8)%N.

Global Instance LocalChainBase : ChainBase := LocalChainBase AddrSize.
Global Instance ChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.

Definition creator : Address :=
  BoundedN.of_Z_const AddrSize 10.
Definition person_1 : Address :=
  BoundedN.of_Z_const AddrSize 11.
Definition person_2 : Address :=
  BoundedN.of_Z_const AddrSize 12.
Definition person_3 : Address :=
  BoundedN.of_Z_const AddrSize 13.

Definition unpack_result {T E} (r : result T E) :=
  match r return match r with
                  | Ok _ => T
                  | Err _ => E
                  end with
  | Ok t => t
  | Err e => e
  end.


Notation "f 'o' g" := (compose f g) (at level 50).

(* Misc utility functions *)
Open Scope list_scope.
Open Scope string_scope.

Definition zero_address : Address := BoundedN.of_Z_const AddrSize 0.

Definition isNone {A : Type} (a : option A) := match a with | Some _ => false | None => true end.
Definition isSome {A : Type} (a : option A) := negb (isNone a).

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

Definition map_filter_FMap {A B C: Type}
                      `{countable.Countable A}
                      `{base.EqDecision A}
                       (f : (A * B) -> option C)
                       (m : FMap A B)
                       : FMap A C :=
  let l := FMap.elements m in
  let mapped_l := List.fold_left (fun acc p => match f p with
                                               | Some c => ((fst p), c) :: acc
                                               | None => acc
                                               end  ) l [] in
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

(* Utils for Show instances *)

Definition empty_str : string := "".
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

Definition lc_contract_addrs lc := map fst (FMap.elements (@lc_contracts AddrSize lc)).
Definition lc_accounts lc := map fst (FMap.elements (@lc_account_balances AddrSize lc)).
Definition lc_account_balance lc addr : option Amount := (FMap.find addr (@lc_account_balances AddrSize lc)).

Definition lc_contract_state_deserialized (state : Type) `{Serializable state} lc : FMap Address state :=
  let els_list : list (Address * SerializedValue) := FMap.elements (lc_contract_state lc) in
  FMap.of_list (List.fold_left
                (fun acc p =>
                  match @deserialize state _ (snd p) with
                  | Some state => (fst p, state) :: acc
                  | None => acc
                  end)
                els_list []).

Definition lc_contract_owners : LocalChain -> FMap Address Address :=
  (map_values_FMap owner) o (lc_contract_state_deserialized Congress.State).

Open Scope bool_scope.

Definition lc_proposals (lc : LocalChain) : FMap Address (FMap ProposalId Proposal) :=
  map_values_FMap proposals (lc_contract_state_deserialized Congress.State lc).


Definition lc_contract_members_and_proposals_new_voters (lc : LocalChain) : FMap Address (FMap Address (list ProposalId)) :=
  map_filter_FMap (fun p =>
    let contract_addr := fst p in
    let state := snd p in
    let candidate_members := (map fst o FMap.elements) (members state) in
    let proposals_pairs := FMap.elements (proposals state) in
    if (0 <? length candidate_members) && (0 <? length proposals_pairs)
    then
      let voters_to_proposals : FMap Address (list ProposalId) :=
        List.fold_left (fun acc m =>
        let unvoted_proposals : list (ProposalId * Proposal) := List.filter (fun p => match FMap.find m (votes (snd p)) with
                                                  | Some _ => false
                                                  | None => true
                                                  end) proposals_pairs in
        match List.map fst unvoted_proposals with
        | [] => acc
        | _ as ps => FMap.add m ps acc
        end
      ) candidate_members FMap.empty in
      Some voters_to_proposals
    else None
  ) (lc_contract_state_deserialized Congress.State lc)
.

Definition lc_contract_members_and_proposals_with_votes (lc : LocalChain)
                                                        : FMap Address (FMap Address (list ProposalId)) :=
  map_filter_FMap (fun p =>
    let contract_addr := fst p in
    let state := snd p in
    let members : list Address := (map fst o FMap.elements) (members state) in
    let proposals_map : FMap nat Proposal := filter_FMap (fun p => 0 =? (FMap.size (votes (snd p))))  (proposals state) in
    if (0 <? length members) && (0 =? (FMap.size proposals_map))
    then Some (
      let propIds : list ProposalId := (map fst o FMap.elements) proposals_map in
      fold_left (fun acc m => FMap.add m propIds acc) members FMap.empty
    )
    else None
  ) (lc_contract_state_deserialized Congress.State lc)
.

(* Utils for Generators *)

Definition elems_opt {A : Type} (l : list A) : G (option A) :=
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
                         : G (option (A * B)) :=
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
                         : G (option ((A * B) * (A * B))) :=
  bindGenOpt (sampleFMapOpt m) (fun p1 =>
    let key1 := fst p1 in
    let val1 := snd p1 in
    bindGenOpt (sampleFMapOpt (FMap.remove key1 m)) (fun p2 =>
      returnGen (Some (p1, p2))
    )
  ).

Definition gContractFromLocalChain lc : G (option (Address * WeakContract)) :=
  sampleFMapOpt (@lc_contracts AddrSize lc).

Definition gAccountAddrFromLocalChain lc : G (option Address) :=
  p <- sampleFMapOpt_filter (@lc_account_balances AddrSize lc) (fun p => negb (address_is_contract (fst p))) ;;
  returnGen match p with
  | Some (addr, _) => Some addr
  | None => None
  end.

Fixpoint remove_multipe_FMap {A B : Type}
                            `{countable.Countable A}
                            `{base.EqDecision A}
                             (m : FMap A B)
                             (ids_to_remove : list A)
                             : FMap A B :=
  match ids_to_remove with
  | id::ids => remove_multipe_FMap (FMap.remove id m) ids
  | [] => m
  end.

Definition gAddrFromLCWithoutAddrs lc addrs : G (option Address) :=
  let acc_bals_sub := remove_multipe_FMap (@lc_account_balances AddrSize lc) addrs in
  p <- sampleFMapOpt acc_bals_sub ;;
  returnGen match p with
  | Some (addr, _) => Some addr
  | None => None
  end.

Definition gAccountAddrFromLCWithoutAddrs lc addrs : G (option Address) :=
  let acc_bals_sub := remove_multipe_FMap (@lc_account_balances AddrSize lc) addrs in
  p <- sampleFMapOpt_filter acc_bals_sub (fun p => negb (address_is_contract (fst p)));;
  returnGen match p with
  | Some (addr, _) => Some addr
  | None => None
  end.

Definition gContractAddrFromLocalChain lc : G (option Address) :=
  p <- sampleFMapOpt (@lc_contracts AddrSize lc) ;;
  returnGen match p with
  | Some (addr, _) => Some addr
  | None => None
  end.

Definition gContractAddrFromLCWithoutAddrs lc addrs : G (option Address) :=
  let contracts_sub := remove_multipe_FMap (@lc_contracts AddrSize lc) addrs in
  p <- sampleFMapOpt contracts_sub ;;
  returnGen match p with
  | Some (addr, _) => Some addr
  | None => None
  end.

Definition gAccountBalanceFromLocalChain lc : G (option (Address * Amount)) :=
  sampleFMapOpt (@lc_account_balances AddrSize lc).

Definition gAccountBalanceFromLCWithoutAddrs lc addrs : G (option (Address * Amount)) :=
  let bals_sub := remove_multipe_FMap (@lc_account_balances AddrSize lc) addrs in
  sampleFMapOpt bals_sub.

Definition gContractSateFromLocalChain lc : G (option (Address * SerializedValue)) :=
  sampleFMapOpt (@lc_contract_state AddrSize lc).

Definition gContractSateFromLCWithoutAddrs lc addrs : G (option (Address * SerializedValue)) :=
  let states_sub := remove_multipe_FMap (@lc_contract_state AddrSize lc) addrs in
  sampleFMapOpt states_sub.


Definition gZPositive := liftM Z.of_nat arbitrary.
Definition gZPositiveSized n := liftM Z.of_nat (arbitrarySized n).

(* Although the type is G (option ...) it will never generate None values.
   Perhaps this is where we should use generators with property proof relevance? Future work... *)
   Definition gBoundedNOpt (bound : N): G (option (BoundedN.BoundedN bound)) :=
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

Definition gDeploymentAction {Setup Msg State : Type}
                            `{Serializable Setup}
                            `{Serializable Msg}
                            `{Serializable State}
                             {BaseTypes : ChainBase}
                             (contract : @Contract BaseTypes Setup Msg State _ _ _)
                             (setup : Setup) : G ActionBody :=
  amount <- arbitrary ;;
  returnGen (act_deploy amount contract (@serialize Setup _ setup)).


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

(* Sample (@gFMapSized nat nat arbitrary arbitrary _ _ _ 1). *)

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

Definition optToVector {A : Type} (n : nat): (G (option A)) -> G (list A) :=
  fun g =>
  l <- vectorOf n g ;;
  let l' := fold_left (fun acc aopt => match aopt with
                          | Some a => a :: acc
                          | None => acc
                          end) l []
  in returnGen l'.

Fixpoint shrinkListTo {A : Type} maxSize (l : list A) : list A:=
  match l with
  | [] => []
  | x::xs => match maxSize with
            | 0 => []
            | S maxSize' => x :: (shrinkListTo maxSize' xs)
            end
  end.

Fixpoint gInterp_type (t : SerializedType) : G (interp_type t) :=
  match t with
  | ser_unit => returnGen tt
  | ser_int => @arbitrary Z _
  | ser_bool => arbitrary
  | ser_pair a b => liftM2 pair (gInterp_type a) (gInterp_type b)
  | ser_list a => listOf (gInterp_type a)
  end.

Derive Arbitrary for SerializedType.

Definition gSerializedValueSized (n : nat): G SerializedValue :=
  t <- arbitrarySized n ;;
  liftM (build_ser_value t) (gInterp_type t).

Instance genSerializedValueSized : GenSized SerializedValue :=
{|
  arbitrarySized := gSerializedValueSized
|}.

(* Utils for QuickChick *)

(* Helper functions when we want to state a property forAll x y z ... (someProp x y z ...) in QuickChick *)
(* Where the generator for y depends on x, the generator for z depends on y, etc. *)
Definition forAll2 {A B prop : Type}
                  `{Checkable prop}
                  `{Show A}
                  `{Show B}
                   (genA : G A)
                   (fgenB : A -> G B)
                   (pf : A -> B -> prop) :=
  forAll genA (fun a => forAll (fgenB a) (fun b => pf a b)).

Definition forAll3 {A B C prop : Type}
                  `{Checkable prop}
                  `{Show A}
                  `{Show B}
                  `{Show C}
                   (genA : G A)
                   (fgenB : A -> G B)
                   (fgenC : A -> B -> G C)
                   (pf : A -> B -> C -> prop) :=
  forAll
    genA
    (fun a =>
  forAll
    (fgenB a)
  (fun b =>
  forAll
    (fgenC a b)
  (fun c => pf a b c))).


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
