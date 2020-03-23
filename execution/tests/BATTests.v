Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import Containers.
From ConCert Require Import BAT.
Require Import Extras.

From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters SerializablePrinters BATPrinters BATGens TraceGens.

(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List Int.
Import BoundedN.Stdpp.
Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.

(* -------------------------- Tests of the BAT Implementation -------------------------- *)

Let serializeMsg := @serialize BAT.Msg _.
Let deserializeMsg := @deserialize BAT.Msg _.

Definition bat_setup : BAT.Setup := {|
  _batFund						:= 100%N;
  _fundDeposit 				:= creator;
  _batFundDeposit 		:= person_1;
  _fundingStart	  		:= 0;
  _fundingEnd					:= 5;
  _tokenExchangeRate  := 1; (* one token corresponds to one ConCert currency *)
  _tokenCreationCap 	:= 400%N;
  _tokenCreationMin 	:= 200%N;
|}.

Definition deploy_bat : @ActionBody Base := create_deployment 0 BAT.contract bat_setup.
Let bat_caddr := BoundedN.of_Z_const AddrSize 128%Z.

Definition bat_chain :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 15);
    build_act creator (act_transfer person_2 15);
    build_act creator (act_transfer person_3 15);
    build_act creator deploy_bat
  ]).

Definition gBATChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun lc _ => 
    gBATAction lc bat_caddr) length max_acts_per_block.

Definition token_reachableFrom (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc (gBATChainTraceList 1) pf.

Definition token_reachableFrom_implies_reachable (lc : LocalChain) pf1 pf2 : Checker := 
  reachableFrom_implies_reachable lc (gBATChainTraceList 1) pf1 pf2.

Example ex1 : SerializedValue := serializeMsg (create_tokens).
(* Example ex2 : SerializedValue := serialize 2. *)
(* Example ex3 : option nat := deserialize ex2. *)
Example ex_ab :=  act_call person_1 0%Z ex1.
Example ex_act :=  build_act creator ex_ab.

(* Compute ex3. *)
(* Compute (deserialize ex2). *)
Print deserialize.
Check deserialize.
Check (@deserialize _ _ ex1).
Compute (show (@deserialize BAT.Msg _ ex1)).


Instance serializableBATMsg : Show SerializedValue :=
{|
  show v := show (deserializeMsg v)
|}.
Existing Instance serializableBATMsg | 0.

Compute (show ex1).

Compute (show ex_ab).

Compute (show ex_act).

(* Set Typeclasses Debug Verbosity 2. *)
Sample (gBATAction bat_chain bat_caddr).

(* QuickChick (forAll (gBATAction bat_chain bat_caddr)
  (fun act => 
    conjoin [
      checker (isSome act) ; 
      isSomeCheck act (fun act =>
        isSome (my_add_block bat_chain [act]))
    ]
  )
). *)
Local Open Scope string_scope.

Sample (gBATChainTraceList 1 bat_chain 10).

Definition can_execute_action trace := 
  let last_lc := List.last (map next_lc_of_lcstep trace) bat_chain in
  forAll (gBATAction last_lc bat_caddr)
  (fun act_opt => isSomeCheck act_opt (fun act => isSome (my_add_block last_lc [act]))).


QuickChick (forAll (gBATChainTraceList 1 bat_chain 8) can_execute_action).

QuickChick (
  trace <- (gBATChainTraceList 1 bat_chain 8) ;;
  let last_lc := List.last (map next_lc_of_lcstep trace) bat_chain in
  match (FMap.find bat_caddr (lc_bat_contracts_states_deserialized last_lc)) with
  | Some state => whenFail (show trace ++ nl ++ show state) (checker false)
  | None => false ==> true
  end
).