Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.

From ConCert.Execution.QCTests Require Import TestUtils ChainPrinters.

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

Instance LocalChainBase : ChainBase := LocalChainBase AddrSize.
Instance LocalChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.


Open Scope list_scope.

(* returns a generator in the given interval (inclusive).
   If low > high, then it will always generate the value high *)
Definition gIntervalNat (low : nat) (high : nat) : G nat :=
  offset <- arbitrarySized (high - low) ;; returnGen (low + offset).

(* Makes a generator for BlockChains, given generators for the necessary types: Address, Setup, Msg, State, SerializedValue. 
   Ensures that all address usages are consistent with the generated address mapping. *)
Definition mkChainGen (BaseTypes : ChainBase) 
                      (ctx : ChainContext BaseTypes) 
                      (n : nat)
                      : G (@Chain BaseTypes)  := 
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

  
(* Sample (@arbitrarySized SerializedType _ 3). *)
(* Sample (@arbitrarySized SerializedValue _ 3). *)

(* The Contract, WeakContract, and ContractCallContext types *)

Definition gContractCallContext {BaseTypes : ChainBase} 
                                (ctx : ChainContext BaseTypes) 
                                : G ContractCallContext :=
  let gAccountAddr := @gAccountAddr BaseTypes ctx in
  let gContractAddr := @gContractAddr BaseTypes ctx in
  liftM3 build_ctx gAccountAddr gContractAddr arbitrary.
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
  addr <- (gContractAddr _ ctx) ;;
  returnGen (build_contract_interface Msg addr send).

Definition gDeploymentAction {Setup Msg State : Type}
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
                           := liftM2 act_transfer (gAccountAddr _ ctx) arbitrary.

Definition gCallAction {Msg : Type}
                      `{Serializable Msg}
                       {BaseTypes : ChainBase} 
                       (ctx : ChainContext BaseTypes)
                       (gMsg : G Msg) 
                       : G ActionBody 
                       := liftM3 act_call (gAccountAddr _ ctx) arbitrary (liftM serialize gMsg).

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

Definition gActionFromContract {Setup Msg State : Type}
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
  addr <- (@gAccountAddr BaseTypes ctx) ;;
  returnGen (build_act addr actionbody).
  (* TODO: what kind of address should we be generating here? *)

Definition zero_address : Address := BoundedN.of_Z_const AddrSize 0.

Derive Arbitrary for SerializedType.
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
Definition gContractAddr' : G (@Address LocalChainBase) :=
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
  contracts      <- vectorOf n gContractAddr' ;;
  accounts      <- vectorOf n gInvalidValidContractAddr' ;;
  let contractAddrBase := BoundedN.of_Z_const AddrSize (Z.of_N (@ContractAddrBase AddrSize)) in
  let gContractAddr := elems_ contractAddrBase contracts in
  let gAccountAddr := elems_ zero_address accounts in
  returnGen (mkBaseGens LocalChainBase gAddr accounts contracts gContractAddr gAccountAddr).

Instance genLocalBaseGens : GenSized (ChainContext LocalChainBase) :=
  {|
    arbitrarySized := gLocalChainContext
  |}.


Definition gLocalChainSized : nat -> (ChainContext LocalChainBase) -> G (@Chain LocalChainBase) := 
  fun n ctx => mkChainGen LocalChainBase ctx n.

Open Scope N_scope.
Definition validcontractaddr_valid := (forAll gContractAddr' (fun a => (BoundedN.to_N a) <=? AddrSize)).
(* QuickChick validcontractaddr_valid. *)
(* Passed 10000 tests (0 discards) *)
Close Scope N_scope.


Open Scope list_scope.
Definition acc_bal := mkMapFromLists (fun x y => x =? y) 42 [10;20;30;40] [1;2;3;4].
Definition testGChain : G Chain := ctx <- arbitrary ;; gLocalChainSized 2 ctx.

(* Sample (@arbitrarySized Chain _ 2). *)
Sample (bh <- gLocalChainContext 1 ;; @gAddress LocalChainBase bh). (* IMPORTANT NOTE: if we omit the explicit types, it will not work *)
Sample (gEnvFromLocalChain lc_initial).


(* make a generator for a BlockHeader from a given chain.
   Should satisfy the IsValidNextBlock predicate. *)
Definition mkBlockHeaderGenSized (BaseTypes : ChainBase) 
                                 (ctx : ChainContext BaseTypes) 
                                 (c : @Chain BaseTypes) 
                                 (n : nat)
                                 : G (@BlockHeader BaseTypes) :=
  let gAccountAddr := @gAccountAddr BaseTypes ctx in
  slot_offset    <- arbitrarySized n ;;
  reward  <- liftM Z.of_nat arbitrary  ;;
  creator <- gAccountAddr ;;
  let height := 1 + chain_height c in
  let slot := slot_offset + current_slot c + 1 in
  fin_height <- gIntervalNat (finalized_height c) (height - 1) ;; (*fin_height c <= fin_height < block_height*)
  returnGen (@build_block_Header BaseTypes height slot fin_height reward creator).

Definition gLocalBCBlockHeaderSizedFromChainAndContext : nat -> 
                                                         (@Chain LocalChainBase) -> 
                                                         (ChainContext LocalChainBase) -> 
                                                         G (@BlockHeader LocalChainBase) := 
  fun n c ctx => mkBlockHeaderGenSized LocalChainBase ctx c n.

(* Definition gLocalBCBlockHeaderSized : nat -> G (@BlockHeader LocalChainBase) := 
  fun n => c <- arbitrarySized n ;; gLocalBCBlockHeaderSizedFromChain n c. *)


Definition blockHeader_ex : (@BlockHeader LocalChainBase) := build_block_Header 0 0 0 0 zero_address.
Definition gbh_dummy := returnGen blockHeader_ex.

Sample gbh_dummy.
(* Sample (ctx <- arbitrary ;; @gContractCallContext LocalChainBase ctx). *)

Sample (ctx <- arbitrary ;; c <- gLocalChainSized 1 ctx ;; gLocalBCBlockHeaderSizedFromChainAndContext 1 c ctx).

Definition validate_header_P : BlockHeader * Chain -> bool :=  fun p => match validate_header (fst p) (snd p) with Some _ => true | None => false end.

(* QuickChick (forAll 
  (ctx <- arbitrary ;;
  c <- arbitrary ;; 
  n <- arbitrary ;;
  header <- gLocalBCBlockHeaderSizedFromChainAndContext n c ctx ;;
  returnGen (header, c)) 
  validate_header_P). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)