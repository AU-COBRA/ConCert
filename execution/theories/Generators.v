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
From Coq Require Import Morphisms.
Import BoundedN.Stdpp.

Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.

Definition AddrSize := (2^8)%N.
Print ContractAddrBase.
(* Let ContractAddrBase : N := @ContractAddrBase AddrSize. *)
Instance LocalChainBase : ChainBase := LocalChainBase AddrSize.
Instance LocalChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.


Record ChainContext (BaseTypes : ChainBase) := 
  mkBaseGens {
    gAddress              : G (@Address BaseTypes);
    accounts              : list (@Address BaseTypes);
    contracts             : list (@Address BaseTypes);
    gValidContractAddr    : G (@Address BaseTypes);
    gInvalidContractAddr  : G (@Address BaseTypes);    
  }.
  
Open Scope string_scope.

Instance showBaseGens {BaseTypes : ChainBase} : Show (ChainContext BaseTypes)  :=
  {|
    show bg := "ChainContext{...}"
  |}.

Instance shrinkAmount : Shrink Amount := 
  {|
    shrink := @shrink Z _
  |}.

Definition empty_str : string := "".
Definition sep : string := ", ".

Instance showChain (BaseTypes : ChainBase) : Show (@Chain BaseTypes) :=
  {|
    show c := 
      let height := show (chain_height c) in
      let slot := show (current_slot c) in
      let fin_height := show (finalized_height c) in
        "Chain{" ++ "height: "       ++ height     ++ sep 
                 ++ "current slot: " ++ slot       ++ sep 
                 ++ "final height: " ++ fin_height ++ "}"
  |}.

Instance showEnvironment (BaseTypes : ChainBase) `{Show Chain}: Show Environment :=
  {|
    show env := "Environment{" 
                ++ "chain: " ++ show (env_chain env) ++ sep 
                ++ "contract states:..."             ++ "}"
  |}.

Close Scope string_scope.
Open Scope list_scope.

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

(* returns a generator in the given interval (inclusive).
   If low > high, then it will always generate the value high *)
Definition gIntervalNat (low : nat) (high : nat) : G nat :=
  offset <- arbitrarySized (high - low) ;; returnGen (low + offset).

(* Makes a generator for BlockChains, given generators for the necessary types: Address, Setup, Msg, State, SerializedValue. 
   Ensures that all address usages are consistent with the generated address mapping. *)
Definition mkChainGen (BaseTypes : ChainBase) 
                      (ctx : ChainContext BaseTypes) 
                      (n : nat)
                      : G Chain  := 
    fin_height  <- arbitrarySized n ;;
    cur_slot   <- arbitrarySized fin_height ;; (* We make sure current slot is <= finalized height *)
    amounts <- vectorOf (length (@accounts BaseTypes ctx)) arbitrary ;;
    let acc_bal := mkMapFromLists address_eqb 0%Z (accounts _ ctx) amounts in
    returnGen (build_chain n cur_slot fin_height acc_bal). 
    
(* For now, shrinking does nothing *)
Instance shrinkChain (BaseTypes : ChainBase) : Shrink (@Chain BaseTypes) :=
  {|
    shrink c := cons c nil
  |}.

Definition mkChainStateGen (BaseTypes : ChainBase)
                           (env : Environment)
                           (actionList : list Action)
                           : G ChainState 
  := returnGen (@build_chain_state BaseTypes env actionList).


Derive Arbitrary for SerializedType.
Derive Show for SerializedType.
Import SerializedType.
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
              (* ++ show (ser_value_type v) ++ sep *)
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

(* The Contract, WeakContract, and ContractCallContext types *)

Definition gContractCallContext {BaseTypes : ChainBase} 
                                (ctx : ChainContext BaseTypes) 
                                : G ContractCallContext :=
  liftM3 build_ctx (gAddress _ ctx) (gValidContractAddr _ ctx) arbitrary.
  (* TODO: what kind of address is the first argument? should it be a contract address, or a non-contract address?
     also, maybe replace the '_' with 'BaseTypes' if we get bugs *)


Definition mkContractGen (Setup Msg State : Type)
                        `{Serializable Setup}
                        `{Serializable Msg}
                        `{Serializable State}
                         (BaseTypes : ChainBase)
                         (init :
                            Chain ->
                            ContractCallContext ->
                            Setup ->
                            option State)
                         (init_proper :
                            Proper (ChainEquiv ==> eq ==> eq ==> eq) init)
                         (receive :
                            Chain ->
                            ContractCallContext ->
                          State ->
                            option Msg ->
                            option (State * list ActionBody))
                         (receive_proper :
                            Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive)
                         : G (Contract Setup Msg State) := returnGen (build_contract init init_proper receive receive_proper).

Definition gWeakContractFromContract {Setup Msg State : Type}
                                    `{Serializable Setup}
                                    `{Serializable Msg}
                                    `{Serializable State}
                                     (BaseTypes : ChainBase)
                                     : (Contract Setup Msg State) -> WeakContract 
                                     := contract_to_weak_contract.


Definition gContractInterfaceFromSendAction {Msg : Type} 
                                            {BaseTypes : ChainBase} 
                                            (ctx : ChainContext BaseTypes)
                                            (send : Amount -> option Msg -> ActionBody) 
                                            : G (ContractInterface Msg) := 
  addr <- (gValidContractAddr _ ctx) ;;
  returnGen (build_contract_interface Msg addr send).

Definition gDeploymentAction
  {Setup Msg State : Type}
 `{Serializable Setup}
 `{Serializable Msg}
 `{Serializable State}
  {BaseTypes : ChainBase} 
  (contract : @Contract BaseTypes Setup Msg State _ _ _)
  (setup : Setup) : G ActionBody :=
  amount <- arbitrary ;;
  returnGen (act_deploy amount contract (serialize setup)).

Definition gTransferAction {BaseTypes : ChainBase} 
                           (ctx : ChainContext BaseTypes) 
                           : G ActionBody 
                           := liftM2 act_transfer (gInvalidContractAddr _ ctx) arbitrary.

Definition gCallAction {Msg : Type}
                      `{Serializable Msg}
                       {BaseTypes : ChainBase} 
                       (ctx : ChainContext BaseTypes)
                       (gMsg : G Msg) 
                       : G ActionBody 
                       := liftM3 act_call (gInvalidContractAddr _ ctx) arbitrary (liftM serialize gMsg).

Definition gActionBodyFromContract {Setup Msg State : Type}
                                  `{Serializable Setup}
                                  `{Serializable Msg}
                                  `{Serializable State}
                                   {BaseTypes : ChainBase} 
                                   (ctx : ChainContext BaseTypes)
                                   (gSetup : G Setup)
                                   (gMsg : G Msg)
                                   (c : @Contract BaseTypes Setup Msg State _ _ _) 
                                   : G ActionBody 
  := freq [
    (1, gCallAction ctx gMsg);
    (1, setup <- gSetup ;; (gDeploymentAction c setup));
    (1, gTransferAction ctx)
  ].

Definition gActionFromContract  {Setup Msg State : Type}
                               `{Serializable Setup}
                               `{Serializable Msg}
                               `{Serializable State}
                                {BaseTypes : ChainBase} 
                                (ctx : ChainContext BaseTypes)
                                (gSetup : G Setup)
                                (gMsg : G Msg)
                                (c : @Contract BaseTypes Setup Msg State _ _ _) 
                                : G Action := 
                                actionbody <- gActionBodyFromContract ctx gSetup gMsg c ;;
                                addr <- (@gInvalidContractAddr BaseTypes ctx) ;;
                                returnGen (build_act addr actionbody).
                                (* TODO: what kind of address should we be generating here? *)

Definition zero_address : Address := BoundedN.of_Z_const AddrSize 0.
Definition b9 : option (BoundedN.BoundedN AddrSize) := @BoundedN.of_nat AddrSize 9.

(* Show instances *)
Open Scope string_scope.

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
    show := @show (BoundedN.BoundedN AddrSize) showBoundedNAddrSize
  |}.

Compute (show zero_address).

Instance showLocalChain : Show (@LocalChain AddrSize) := 
  {|
    show lc := "LocalChain{" 
                ++ show (lc_height lc) ++ sep 
                ++ show (lc_slot lc)   ++ sep 
                ++ show (lc_fin_height lc) 
                ++ sep ++ "... }"
  |}.


Close Scope string_scope.

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

(* Sample (@arbitrary (@Address LocalChainBase) _). *)

(* Definition genDummyChainedList : G (ChainTrace empty_state (build_chain_state lcb_lc [])) :=
  returnGen clnil. *)



Definition gDummyLocalChain : G (@LocalChain AddrSize) :=
  returnGen lc_initial.

(* always generates the initial local chain builder, which contains the initial local chain, and initial, empty trace *)
Definition gDummyLocalChainBuilder : G LocalChainBuilder :=
  returnGen (lcb_initial AddrSize).

Definition gEnvFromLocalChain (lc : LocalChain) : G Environment := returnGen (lc_to_env lc) .

(* Instance genEnvFromLocalChain (lc : LocalChain) : Gen Environment :=
  {| 
    arbitrary := gEnvFromLocalChain lc
  |}. *)
Definition gValidContractAddr' : G (@Address LocalChainBase) :=
  let baseAddr := (N.to_nat (@ContractAddrBase AddrSize)) in
  n <- arbitrarySized baseAddr  ;; (* generates a value between 0 and ContractAddrBase (= AddrSize/2*)
  let nn : nat := n + baseAddr in (* ContractAddrBase <= nn <= AddrSize*)
  let bound_opt : option (BoundedN.BoundedN AddrSize):= @decode_bounded AddrSize (Pos.of_nat nn) in
  match bound_opt with
  | Some b => returnGen b
  | None => returnGen (BoundedN.of_Z_const AddrSize (Z.of_N (@ContractAddrBase AddrSize))) 
  end.

(* a generator which makes values n such that 0 <= n < ContractAddrBase*)
Definition gInvalidValidContractAddr' : G (@Address LocalChainBase) :=
  n <- arbitrarySized ((N.to_nat (@ContractAddrBase AddrSize)) - 1) ;; 
  let bound_opt : option (BoundedN.BoundedN AddrSize):= @decode_bounded AddrSize (Pos.of_nat n) in
  match bound_opt with
  | Some b => returnGen b
  | None => returnGen (BoundedN.of_Z_const AddrSize (Z.of_N 0)) 
  end.


Definition gLocalChainContext (n : nat) : G (ChainContext LocalChainBase) := 
  let addr_eqb := @address_eqb LocalChainBase in 
  let default : Amount := Z0 in
  let gAddr := (@arbitrary (@Address LocalChainBase) _) in
  amounts    <- vectorOf n arbitrary ;;
  contracts      <- vectorOf n gValidContractAddr' ;;
  accounts      <- vectorOf n gInvalidValidContractAddr' ;;
  let contractAddrBase := BoundedN.of_Z_const AddrSize (Z.of_N (@ContractAddrBase AddrSize)) in
  let gContractAddr := elems_ contractAddrBase contracts in
  let gAccountAddr := elems_ zero_address accounts in
  returnGen (mkBaseGens LocalChainBase gAddr accounts contracts gContractAddr gAccountAddr).

Instance genLocalBaseGens : GenSized (ChainContext LocalChainBase) :=
  {|
    arbitrarySized := gLocalChainContext
  |}.

Definition gLocalChainSized : nat -> G (@Chain LocalChainBase) := 
  fun n => lb <- gLocalChainContext n ;; mkChainGen LocalChainBase lb n.

  
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
Definition acc_bal := mkMapFromLists (fun x y => x =? y) 42 [10;20;30;40] [1;2;3;4].
Definition testGChain : G Chain := arbitrary.

Sample (gLocalChainContext 10).

Sample (gLocalChainSized 4).
(* Sample (@arbitrarySized Chain _ 2). *)
Sample (bh <- gLocalChainContext 2 ;; @gAddress LocalChainBase bh). (* IMPORTANT NOTE: if we omit the explicit types, it will not work *)
Sample (gEnvFromLocalChain lc_initial).

Open Scope string_scope.
(* Show and Generator instances for types related to Traces (an execution sequence of contracts on the BC) *)
Instance showBlockHeader (BaseTypes : ChainBase) `{Show (@Address BaseTypes)} : Show (@BlockHeader BaseTypes) :=
  {|
    show bh := 
      "BlockHeader{" ++ "bheight: "     ++ show (block_height bh)           ++ sep
                     ++ "bslot: "       ++ show (block_slot bh)             ++ sep 
                     ++ "bfin_height: " ++ show (block_finalized_height bh) ++ sep
                     ++ "breward: "     ++ show (block_reward bh)           ++ sep
                     ++ "bcreator: "    ++ show (block_creator bh)          ++ "}" 
  |}.


Close Scope string_scope.

(* make a generator for a BlockHeader from a given chain.
   Should satisfy the IsValidNextBlock predicate. *)
Definition mkBlockHeaderGenSized (BaseTypes : ChainBase) 
                                 (ctx : ChainContext BaseTypes) 
                                 (c : @Chain BaseTypes) 
                                 (n : nat)
                                 : G (@BlockHeader BaseTypes) :=
  let gAddr : G (@Address BaseTypes) := @gInvalidContractAddr BaseTypes ctx in
  slot_offset    <- arbitrarySized n ;;
  reward  <- liftM Z.of_nat arbitrary  ;;
  creator <- gAddr ;;
  let height := 1 + chain_height c in
  let slot := slot_offset + current_slot c + 1 in
  fin_height <- gIntervalNat (finalized_height c) (height - 1) ;; (*fin_height c <= fin_height < block_height*)
  returnGen (@build_block_Header BaseTypes height slot fin_height reward creator).

Definition gLocalBCBlockHeaderSizedFromChain : nat -> (@Chain LocalChainBase) -> G (@BlockHeader LocalChainBase) := 
  fun n c => ctx <- gLocalChainContext n ;; mkBlockHeaderGenSized LocalChainBase ctx c n.

Definition gLocalBCBlockHeaderSized : nat -> G (@BlockHeader LocalChainBase) := 
  fun n => c <- arbitrarySized n ;; gLocalBCBlockHeaderSizedFromChain n c.

Instance genLocalBCBlockHeaderSized : GenSized (@BlockHeader LocalChainBase) :=
  {|
    arbitrarySized := gLocalBCBlockHeaderSized
  |}.

Definition blockHeader_ex : (@BlockHeader LocalChainBase) := build_block_Header 0 0 0 0 zero_address.
Definition gbh_dummy := returnGen blockHeader_ex.

Compute (show blockHeader_ex).
Sample gbh_dummy.

Sample (gLocalBCBlockHeaderSized 2).

Open Scope core_scope.
Definition validate_header_P : BlockHeader * Chain -> bool :=  fun p => match validate_header (fst p) (snd p) with Some _ => true | None => false end.

(* QuickChick (forAll 
  (c <- arbitrary ;; 
  n <- arbitrary ;;
  header <- gLocalBCBlockHeaderSizedFromChain n c ;;
  returnGen (header, c)) 
  validate_header_P). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)