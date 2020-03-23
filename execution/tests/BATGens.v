From ConCert Require Import Blockchain LocalBlockchain BAT.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters BATPrinters EIP20TokenGens.
Require Import ZArith Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
Require Import Containers.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.
Definition serializeMsg := serialize BAT.Msg _ .

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
    let is_funding_over := state.(fundingEnd) <? lc.(lc_slot) in
    let current_total_supply := token_state.(EIP20Token.total_supply) in
    let fund_has_succeeded_requirement := N.leb state.(tokenCreationMin) current_total_supply  in 
    backtrack [
      (* generate an EIP20 action; transfer, transfer_from, or approve *)
      (0, let token_act_gen := backtrack [(1, liftM Some (gTransfer lc token_state)) ; 
                                          (1, gTransfer_from token_state) ; 
                                          (1, gApprove token_state)] in
          bindGenOpt token_act_gen 
          (fun token_act_pair =>
            let caller_addr := fst token_act_pair in
            let token_msg := (snd token_act_pair) in
            let msg := serializeMsg (tokenMsg token_msg) in
            mk_call contract_addr caller_addr 0%Z msg
          ) 
      ) ;
      (* generate a create_tokens action *)
      (1, if state.(isFinalized) || is_funding_over
          then returnGen None
          else bindGenOpt (sampleFMapOpt lc.(lc_account_balances))
          (fun p =>
            if Z.eqb 0%Z (snd p) 
            then returnGen None
            else amount <- choose (1%Z, snd p) ;;
                 mk_call contract_addr (fst p) amount (serializeMsg create_tokens)
          )
      ) ;
      (* generate a finalize action, when the funding period is over *)
      (1, if state.(isFinalized) 
             || N.ltb current_total_supply state.(tokenCreationMin) 
             || ((Nat.leb lc.(lc_slot) state.(fundingEnd)) && negb (negb (N.eqb current_total_supply state.(tokenCreationCap))))
          then returnGen None
          else mk_call contract_addr state.(fundDeposit) 0%Z (serializeMsg finalize)) ;
      (* generate a refund action *)
      (* only generates callers which already have created tokens on the contract *)
      (1, if state.(isFinalized) 
             || fund_has_succeeded_requirement
             || negb is_funding_over
          then returnGen None
          else let bals := EIP20Token.balances token_state in
          let is_not_batFundDeposit p := negb (address_eqb (fst p) state.(batFundDeposit)) in
          let has_bats p := N.ltb 0 (snd p) in   
          bindGenOpt (sampleFMapOpt_filter bals (fun p => is_not_batFundDeposit p && has_bats p) )
          (fun p => mk_call contract_addr (fst p) 0%Z (serializeMsg refund))
      )
    ]
  | None => returnGen None
  end.