Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
(* For monad notations *)
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

From Coq Require Import List.
From Coq Require Import Strings.BinaryString.
Import ListNotations.

(* Declare Instance genAmountSized : GenSized Amount.
Declare Instance showAmount : Show Amount.
Declare Instance shrinkAmount : Shrink Amount. *)


Record BaseGens (BaseTypes : ChainBase) := 
  mkBaseGens {
    (* Address          : Type; *)
    gAddress              : G (@Address BaseTypes);
    init_account_balances : @Address BaseTypes -> Amount;
    gValidContractAddr    : G (@Address BaseTypes);
    (* genSetup         : G Setup;
    genMsg           : G Msg;
    genState         : G State;
    genSerializedVal : G SerializedValue; *)
  }.
  
Open Scope string_scope.
Instance showBaseGens {BaseTypes : ChainBase} : Show (BaseGens BaseTypes)  :=
  {|
    show bg := "BaseGens{...}"
  |}.

(* Instance showAmount : Show Amount :=
  {|
    show := @show Z showZ
  |}. *)


(* Instance genAmountSized : GenSized Amount :=
  {|
    arbitrarySized := @arbitrarySized Z _ 
  |}.

Instance genAmount : Gen Amount :=
  {|
    arbitrary := @arbitrary Z _ 
  |}. *)


Instance shrinkAmount : Shrink Amount := 
  {|
    shrink := @shrink Z _
  |}.

  
(* dummy implementations for now *)
Definition empty_str : string := "".
Definition sep : string := ", ".


Instance showChain (BaseTypes : ChainBase) : Show (@Chain BaseTypes) :=
  {|
    show c := 
      let height := show (chain_height c) in
      let slot := show (current_slot c) in
      let fin_height := show (finalized_height c) in
        "Chain{" ++ "height: " ++ height ++ sep 
                 ++ "current slot: " ++ slot ++ sep 
                 ++ "final height: " ++ fin_height 
                 ++ "}"
  |}.


Instance showEnvironment (BaseTypes : ChainBase) `{Show Chain}: Show Environment :=
  {|
    show env := "Environment{" 
                ++ "chain: " ++ show (env_chain env) ++ sep 
                ++ "contract states: ..."
                ++ "}"
  |}.

Close Scope string_scope.

Open Scope list_scope.

Fixpoint mkMapFromList {A B : Type}
                       (a_eqb : A -> A -> bool)
                       (default : B)
                       (l : list A) 
                       (lb : list B)
                       : A -> B :=
  match (l,lb) with
  | ([],[]) => fun x => default
  | (a::l', b::lb') => 
    fun (x : A) => if a_eqb x a then b else (mkMapFromList a_eqb default l' lb') x 
  | (_,_) => fun x => default
  end.


(* Makes a generator for BlockChains, given generators for the necessary types: Address, Setup, Msg, State, SerializedValue. 
   Ensures that all address usages are consistent with the generated address mapping. *)
Definition mkChainGen (BaseTypes : ChainBase) (baseGens : BaseGens BaseTypes) (n : nat)
                      : G Chain  := 
  (* First construct context of Contract Addresses. *)
    ch_height  <- arbitrarySized n ;;
    cur_slot   <- arbitrarySized ch_height ;; (* We make sure current slot is <= chain height *)
    (* gmp         <- liftM (mkMapFromList addr_eqb (arbitrarySized n)) addr_list_gen ;; 
    mp <- gmp ;; *)
    let acc_bal := init_account_balances BaseTypes baseGens in
    returnGen (build_chain ch_height cur_slot n acc_bal).
    
Close Scope list_scope.

  (* For now, shrinking does nothing *)
Instance shrinkChain (BaseTypes : ChainBase) : Shrink (@Chain BaseTypes) :=
  {|
    shrink c := cons c nil
  |}.

Derive Arbitrary for SerializedType.
Derive Show for SerializedType.
Import SerializedType.
Open Scope list_scope.
Open Scope string_scope.

Fixpoint string_of_interp_type (st : SerializedType) :  (interp_type st) -> string :=
match st as st0 return interp_type st0 -> string with
  | ser_unit => fun _ => "()"
  | ser_int => fun t => show t
  | ser_bool => fun t => show t
  | ser_list a => 
    fun t : list (interp_type a) => 
      let t_str_list := map (string_of_interp_type a) t in 
      "[" ++ String.concat ";" t_str_list ++ "]"  
  | ser_pair a b => 
    fun t : (interp_type a * interp_type b) => 
      "(" 
      ++ string_of_interp_type a (fst t) 
      ++ ","
      ++ string_of_interp_type b (snd t) ++ ")"
  end.  

Definition ex_serialized_type := ser_pair (ser_list (ser_list ser_bool)) ser_int.
Compute (interp_type ex_serialized_type).
Definition ex_val := ([[true;false];[true;true];[false];[]], 2%Z).
Compute (string_of_interp_type ex_serialized_type ex_val).

Close Scope list_scope.
Instance showSerializedValue : Show SerializedValue := 
  {|
    show v := "SerializedValue{" 
              ++ show (ser_value_type v) ++ sep
              ++ string_of_interp_type (ser_value_type v) (ser_value v) ++ "}" 
  |}.
Close Scope string_scope.

Fixpoint gInterp_type (t : SerializedType) : G (interp_type t) := 
  match t with
  | ser_unit => returnGen tt
  | ser_int => @arbitrary Z _
  | ser_bool => arbitrary
  | ser_pair a b => liftM2 pair (gInterp_type a) (gInterp_type b) 
  | ser_list a => listOf (gInterp_type a)
  end.

Definition gSerializedValueSized (n : nat): G SerializedValue :=
  t <- arbitrarySized n ;;
  liftM (build_ser_value t) (gInterp_type t).

Instance genSerializedValueSized : GenSized SerializedValue :=
  {|
    arbitrarySized := gSerializedValueSized 
  |}.

(* Sample (@arbitrarySized SerializedType _ 3). *)
(* Sample (@arbitrarySized SerializedValue _ 3). *)

Import BoundedN.Stdpp.
Import LocalBlockchain.
Definition zero_address : Address := BoundedN.of_Z_const AddrSize 10.
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

Instance showAddress : Show (@Address LocalChainBase) :=
  {|
    show := @show (BoundedN.BoundedN AddrSize) showBoundedN
  |}.

Instance showLocalChain : Show LocalChain := 
  {|
    show lc := "LocalChain{" 
                ++ show (lc_height lc) ++ sep 
                ++ show (lc_slot lc)   ++ sep 
                ++ show (lc_fin_height lc) 
                ++ sep ++ "... }"
  |}.


Close Scope string_scope.

(* Generators *)
Definition genZ : G Z := arbitrary.	


Derive Show for positive.
Derive Arbitrary for positive.
Derive GenSized for positive.

(* Although the type is G (option ...) it will never generate None values *)
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

(* Definition genDummyChainedList : G (ChainTrace empty_state (build_chain_state lcb_lc [])) :=
  returnGen clnil. *)

Definition gDummyLocalChain : G LocalChain :=
  returnGen lc_initial.

(* always generates the initial local chain builder, which contains the initial local chain, and initial, empty trace *)
Definition gDummyLocalChainBuilder : G LocalChainBuilder :=
  returnGen lcb_initial.

Definition gEnvFromLocalChain (lc : LocalChain) : G Environment := returnGen (lc_to_env lc) .

(* Instance genEnvFromLocalChain (lc : LocalChain) : Gen Environment :=
  {| 
    arbitrary := gEnvFromLocalChain lc
  |}. *)

Definition gValidContractAddr' : G (@Address LocalChainBase) :=
  n <- arbitrarySized (N.to_nat ContractAddrBase) ;; (* generates a value between 0 and ContractAddrBase (= AddrSize/2*)
  let nn : nat := n + (N.to_nat ContractAddrBase) in (* ContractAddrBase <= nn <= AddrSize*)
  let bound_opt : option (BoundedN.BoundedN AddrSize):= @decode_bounded AddrSize (Pos.of_nat nn) in
  match bound_opt with
  | Some b => returnGen b
  | None => returnGen (BoundedN.of_Z_const AddrSize (Z.of_N ContractAddrBase)) 
  end.


Definition gLocalBaseGens (n : nat) : G (BaseGens LocalChainBase) := 
  let addr_eqb := @address_eqb LocalChainBase in 
  let default : Amount := Z0 in
  amounts    <- vectorOf n arbitrary ;;
  addrs      <- vectorOf n arbitrary ;;
  (* let acc_bal := fun x => default in *)
  let acc_bal := mkMapFromList addr_eqb default addrs amounts in
  returnGen (mkBaseGens LocalChainBase arbitrary acc_bal gValidContractAddr').

Instance genLocalBaseGens : GenSized (BaseGens LocalChainBase) :=
  {|
    arbitrarySized := gLocalBaseGens
  |}.

Definition gLocalChainSized : nat -> G (@Chain LocalChainBase) := 
  fun n => lb <- gLocalBaseGens n ;; mkChainGen LocalChainBase lb n.

  
Instance genLocalChainSized : GenSized (@Chain LocalChainBase) :=
{|
  arbitrarySized := gLocalChainSized
|}.


Open Scope N_scope.
Definition validcontractaddr_valid := (forAll gValidContractAddr' (fun a => (BoundedN.to_N a) <=? AddrSize)).
(* QuickChick validcontractaddr_valid. *)
(* Passed 10000 tests (0 discards) *)
Close Scope N_scope.


Open Scope list_scope.
Definition acc_bal := mkMapFromList (fun x y => x =? y) 42 [10;20;30;40] [1;2;3;4].
Definition testGChain : G Chain := arbitrary.


Sample (gLocalChainSized 4).
Sample (gLocalBaseGens 10).
Sample (@arbitrarySized Chain _ 2).
Sample (gEnvFromLocalChain lc_initial).

