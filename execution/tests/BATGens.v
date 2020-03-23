From ConCert Require Import Blockchain LocalBlockchain BAT.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters BATPrinters SerializablePrinters EIP20TokenGens.
Require Import ZArith Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
Require Import Containers.

(* Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits. *)

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.
(* Definition serializeMsg := serialize BAT.Msg _ . *)

Definition lc_bat_contracts_states_deserialized (lc : LocalChain) : FMap Address BAT.State :=
  let els_list : list (Address * SerializedValue) := FMap.elements (lc_contract_state lc) in
  FMap.of_list (List.fold_left 
                (fun acc p => 
                  match @deserialize BAT.State _ (snd p) with
                  | Some state => (fst p, state) :: acc
                  | None => acc
                  end)  
                els_list []).

Definition gBATAction (lc : LocalChain) (contract_addr : Address) : G (option Action) := 
  let mk_call contract_addr caller_addr amount msg :=
		returnGen (Some {|
			act_from := caller_addr;
			act_body := act_call contract_addr amount msg 
		|}) in 
  match FMap.find contract_addr (lc_bat_contracts_states_deserialized lc) with
  | Some state =>
    let token_state := state.(token_state) in
    backtrack [
      (* generate an EIP20 action; transfer, transfer_from, or approve *)
      (1, let token_act_gen := backtrack [(1, liftM Some (gTransfer lc token_state)) ; 
                                          (1, gTransfer_from token_state) ; 
                                          (1, gApprove token_state)] in
          bindGenOpt token_act_gen (fun token_act_pair =>
            let caller_addr := fst token_act_pair in
            let token_msg := (snd token_act_pair) in
            let msg := @serialize BAT.Msg _ (tokenMsg token_msg) in
            mk_call contract_addr caller_addr 0%Z msg
          ) 
      )
    ]
  | None => returnGen None
  end.