Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable. Import SerializedType.
From ConCert Require Import BoundedN ChainedList.

From ConCert.Execution.QCTests Require Import TestUtils.

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
Instance LocalChainBase : ChainBase := LocalChainBase AddrSize.
Instance LocalChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.

Open Scope list_scope.
Open Scope string_scope.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.


Derive Show for positive.
Derive Show for SerializedType.

Instance showLCB : Show LocalChainBuilder :=
  {| show a := "LocalChainBuilder{...}" |}.


Instance showLocalChainBuilderDepthFirst {n : N} : Show (LocalChainBuilderDepthFirst n) :=
  {| show a := "LocalChainBuilderDepthFirst{...}" |}.

Instance showChainBuilderType {BaseTypes : ChainBase}: Show (@ChainBuilderType BaseTypes) :=
  {| show a := "ChainBuilderType{...}" |}.


Instance showBaseGens {BaseTypes : ChainBase} : Show (ChainContext BaseTypes)  :=
  {|
    show bg := "ChainContext{...}"
  |}.

Instance shrinkAmount : Shrink Amount := 
  {|
    shrink := @shrink Z _
  |}.

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

Instance showContract {Setup Msg State : Type}
                     `{Serializable Setup}
                     `{Serializable Msg}
                     `{Serializable State} 
                      : Show (Contract Setup Msg State) :=
{|
  show c := "Contract{...}"
|}.

Instance showEnvironment (BaseTypes : ChainBase) `{Show Chain}: Show Environment :=
{|
  show env := "Environment{" 
              ++ "chain: " ++ show (env_chain env) ++ sep 
              ++ "contract states:..."             ++ "}"
|}.


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
(* Compute (interp_type ex_serialized_type). *)
Definition ex_val := ([[true;false];[true;true];[false];[]], 2%Z).
(* Compute (string_of_interp_type ex_serialized_type ex_val). *)

(* Print Serializable.
Instance showSerializable {ty : Type} `{Show ty} : Show (Serializable ty) :=
{|
  show s := match deserialize s with
            | Some v => ""
            | None => "<FAILED DESERIALIZATION>"
            end 
|}. *)


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


Instance showLocalChain : Show (@LocalChain AddrSize) := 
{|
  show lc := "LocalChain{" 
              ++ show (lc_height lc) ++ sep 
              ++ show (lc_slot lc)   ++ sep 
              ++ show (lc_fin_height lc) 
              ++ sep ++ "... }"
|}.

Instance showLocalContractCallContext : Show (@ContractCallContext LocalChainBase) :=
{|
show cctx := "ContractCallContext{"
             ++ "ctx_from: " ++ show (@ctx_from LocalChainBase cctx) ++ sep
             ++ "ctx_contract_addr: " ++ show (@ctx_contract_address LocalChainBase cctx) ++ sep
             ++ "ctx_amount: " ++ show (@ctx_amount LocalChainBase cctx) ++ "}"
|}.


Instance showActionBody `{Show SerializedValue} : Show ActionBody :=
{|
  show a := match a with
    | act_transfer addr amount => 
      "(act_transfer " ++ show addr ++ sep ++ show amount ++ ")" 
    | act_call addr amount ser_value => 
      "(act_call " ++ show addr ++ sep ++ show amount ++ sep ++ show ser_value ++ ")"
    | act_deploy amount contract ser_value =>
      "(act_deploy " ++ show amount ++ sep ++ show ser_value ++ ")"
    end
|}. 


Instance showLocalAction `{Show ActionBody} : Show (@Action LocalChainBase) :=
{|
  show a := "Action{"
            ++ "act_from: " ++ show (act_from a) ++ sep
            ++ "act_body: " ++ show (act_body a) ++ "}"
|}. 

Instance showChainState : Show (@ChainState LocalChainBase) :=
{|
  show a := "ChainState{" ++ "}"
|}.

Instance showContractCallInfo {Msg : Type} `{Show Msg} : Show (ContractCallInfo Msg) :=
{|
  show info := "ContractCallInfo{" 
                ++ "call_from: " ++ show (call_from info) ++ sep
                ++ "call_amount: " ++ show (call_amount info) ++ sep
                ++ "call_msg: " ++ show (call_msg info) ++ sep ++ "}"
|}.

Close Scope string_scope.
Close Scope list_scope.