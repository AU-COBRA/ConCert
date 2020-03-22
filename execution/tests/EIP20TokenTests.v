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
From ConCert Require Import EIP20Token.
Require Import Extras.

From ConCert.Execution.QCTests Require Import 
	ChainGens TestUtils ChainPrinters SerializablePrinters EIP20TokenPrinters EIP20TokenGens TraceGens.

(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List Int.
Import BoundedN.Stdpp.
Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.

(* -------------------------- Tests of the EIP20 Token Implementation -------------------------- *)

Definition token_setup := EIP20Token.build_setup creator (100%N).
Definition deploy_eip20token : @ActionBody Base := create_deployment 0 EIP20Token.contract token_setup.

Let contract_base_addr := BoundedN.of_Z_const AddrSize 128%Z.

Definition chain_with_token_deployed :=  
  unpack_option (my_add_block lc_initial 
  [
    build_act creator (act_transfer person_1 10);
    build_act creator (act_transfer person_2 10);
    build_act creator (act_transfer person_3 10);
    build_act creator deploy_eip20token
  ]).

Definition gEIP20TokenChainTraceList max_acts_per_block lc length := 
  gLocalChainTraceList_fix lc (fun lc _ => 
    gEIP20TokenAction lc contract_base_addr) length max_acts_per_block.

Definition token_reachableFrom (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc (gEIP20TokenChainTraceList 1) pf.

Definition token_reachableFrom_implies_reachable (lc : LocalChain) pf1 pf2 : Checker := 
  reachableFrom_implies_reachable lc (gEIP20TokenChainTraceList 1) pf1 pf2.

Compute (show (map fst (FMap.elements (lc_contracts chain_with_token_deployed)))).
Compute (show (lc_token_contracts_states_deserialized chain_with_token_deployed)).
Compute (show (lc_account_balances chain_with_token_deployed)).
(* Sample (gEIP20TokenChainTraceList chain_with_token_deployed 10). *)
Open Scope string_scope.
Definition debug_gEIP20Checker {A : Type}
                              `{Checkable A}
                               lc 
                               (act : option Action)
                               : A -> Checker :=
  let print_valid_actions := match act with
                            | Some act => "valid actions: " ++ show (validate_actions [act]) ++ sep ++ nl
                            | None => ""
                            end in
  whenFail 
    ("lc balances: " ++ show (lc_account_balances lc) ++ sep ++ nl
    ++ print_valid_actions
    ++ "token state: " ++ show (lc_token_contracts_states_deserialized lc) ++ sep ++ nl 
    ).

(* QuickChick (forAll 
  (gEIP20TokenAction chain_with_token_deployed contract_base_addr) 
  (fun act_opt => isSomeCheck act_opt (fun act => 
    (isSomeCheck (my_add_block chain_with_token_deployed [act]) (fun _ => checker true))
  ))). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

(* Sample (gEIP20TokenAction chain_with_token_deployed contract_base_addr). *)
Sample (gEIP20TokenChainTraceList 1 chain_with_token_deployed 10).
(* QuickChick (forAll 
  (gEIP20TokenAction chain_with_token_deployed contract_base_addr) 
  (fun act_opt => isSomeCheck act_opt (fun act => 
    (debug_gEIP20Checker chain_with_token_deployed (Some act))  
      ((checker o isSome) (my_add_block chain_with_token_deployed [act]))))). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition last_state trace := List.last (map next_lc_of_lcstep trace) chain_with_token_deployed.

(* Generate a trace, and then execute an action on the last state of the trace. Check that this always succeeds *)
(* QuickChick (forAll2 
  (gEIP20TokenChainTraceList chain_with_token_deployed 5) 
  (fun trace => 
    gEIP20TokenAction (last_state trace) 
                      contract_base_addr)
  (fun trace act_opt => isSomeCheck act_opt (fun act => 
    (debug_gEIP20Checker (last_state trace) (Some act))  
      ((checker o isSome) (my_add_block (last_state trace) [act]))))). *)

Local Open Scope N_scope.
(* One key property: the sum of the balances is always equal to the initial supply *)
Definition sum_balances_eq_init_supply_P maxLength := 
  forAllTraces maxLength chain_with_token_deployed (gEIP20TokenChainTraceList 2)
    (fun (lc : LocalChain) =>
      debug_gEIP20Checker lc None
      ( match FMap.find contract_base_addr (lc_token_contracts_states_deserialized lc) with
      | Some state => 
        let balances_list := (map snd o FMap.elements) state.(balances) in
        let balances_sum : N := fold_left N.add balances_list 0%N in
        balances_sum =? state.(total_supply)
      | None => false
      end)).

(* QuickChick (sum_balances_eq_init_supply_P 7). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

(* INVALID PROPERTY: accounts may allow multiple other accounts to transfer tokens, but the actual transfer ensures that
   no more tokens are sent than the balance of the sender. *)
Definition sum_allowances_le_init_supply_P maxLength :=
  forAllTraces maxLength chain_with_token_deployed (gEIP20TokenChainTraceList 2)
    (fun (lc : LocalChain) =>
      debug_gEIP20Checker lc None
      (match FMap.find contract_base_addr (lc_token_contracts_states_deserialized lc) with
      | Some state => 
        let allowances := map_values_FMap 
          (fun allowance_map => fold_left N.add ((map snd o FMap.elements) allowance_map) 0)
          state.(allowances) in
        let allowances_list := (map snd o FMap.elements) allowances in
        let allowances_sum := fold_left N.add allowances_list 0%N in 
        allowances_sum <=? state.(total_supply)
      | None => false
      end)).
    
(* QuickChick (sum_allowances_le_init_supply_P 5). *)

Definition person_has_tokens person (n : N) := 
  fun lc =>
    match FMap.find contract_base_addr (lc_token_contracts_states_deserialized lc) with
    | Some state => if n =? (FMap_find_ person state.(balances) 0)
                    then Some n
                    else None  
    | None => None
    end.

(* Notation "lc '~~>' pf" :=
  (token_reachableFrom lc pf)
  (at level 45, no associativity). *)

(* QuickChick (chain_with_token_deployed ~~> person_has_tokens person_3 12). *)
(* QuickChick (chain_with_token_deployed ~~> person_has_tokens creator 0). *)

(* QuickChick (token_reachableFrom_implies_reachable 
  chain_with_token_deployed
  (person_has_tokens creator 10)
  (person_has_tokens creator 0)        
). *)

Notation "'{' lc '~~>' pf1 '===>' pf2 '}'" :=
  (reachableFrom_implies_tracePropSized_new 3 lc (gEIP20TokenChainTraceList 1) pf1 pf2)   
  (at level 90, left associativity).

(* This (false) property says that from the initial chain where the token contract has been deployed,
   if there is a reachable state where the creator has 5 tokens, then any trace afterwards
   will satisfy that the creator has 10 tokens. This is obviously not true, and QC will give us a counterexample. *)
QuickChick (
  {
    chain_with_token_deployed 
    ~~> (person_has_tokens creator 5 o next_lc_of_lcstep) 
    ===> (fun _ _ post_trace => isSome (person_has_tokens creator 10 (last_state post_trace)))
  }
).

Definition get_approve_act (act : Action) : option (Address * Address * EIP20Token.Msg) := 
  match act.(act_body) with
  | act_call caddr _ ser_msg =>
    match deserialize EIP20Token.Msg _ ser_msg with
    | Some (approve _ _ as msg) => Some (caddr, act.(act_from), msg)
    | _ => None
    end
  | _ => None
  end.

Definition get_transferFrom_act (act : Action) : option (Address * Address * EIP20Token.Msg) := 
  match act.(act_body) with
  | act_call caddr _ ser_msg =>
    match deserialize EIP20Token.Msg _ ser_msg with
    | Some (transfer_from _ _ _ as msg) => Some (caddr, act.(act_from), msg)
    | _ => None
    end
  | _ => None
  end.

Definition state_has_some_approve_act {AddrSize : N} (step : @LocalChainStep AddrSize) := 
  match step with
  | step_action prev_lc header next_lc acts =>
    match find (isSome o get_approve_act) acts with
    | Some x => get_approve_act x
    | None => None
    end
  | _ => None
  end.

Definition delegate_made_no_transferFroms (approve_act_p :  (Address * Address * EIP20Token.Msg)) 
                                          (trace : list LocalChainStep) := 
  let caddr := fst (fst approve_act_p) in
  let approver := snd (fst approve_act_p) in
  match (snd approve_act_p) with
  | approve delegate amount =>
    forallb (fun step =>
      let acts := acts_of_lcstep step in
      let act_not_transferFrom_delegate act :=
        match get_transferFrom_act act with
        | Some (caddr', caller, (transfer_from from to _)) =>
          if (address_eqb caddr' caddr) 
          then negb ((address_eqb caller delegate) || (address_eqb from approver))
          else true
        | _ => true
        end in
      forallb act_not_transferFrom_delegate acts  
    ) trace
  | _ => false
  end.

(* Definition forAnyStateInTrace n trace c := 
  let trace' := map prev_lc_of_lcstep trace in
  forAll (elems_ chain_with_token_deployed trace') (fun lc =>
  forAllTraces_traceProp n lc (gEIP20TokenChainTraceList 2) c). *)

Definition allower_addr (approve_act_p : (Address * Address * EIP20Token.Msg)) := 
  match snd approve_act_p with
  | (approve _ _ ) => snd (fst approve_act_p)
  | (transfer_from allower _ _) => allower
  | _ => zero_address
  end.
Definition delegate_addr (approve_act_p : (Address * Address * EIP20Token.Msg)) := 
  match (snd approve_act_p) with
  | (approve delegate _ ) => Some delegate
  | (transfer_from _ _ _) => Some (snd (fst approve_act_p))
  | _ => None 
  end.

Definition approve_amount (approve_act_p : (Address * Address * EIP20Token.Msg)) := 
  match (snd approve_act_p) with
  | (approve _ amount ) => amount
  | _ => 0
  end.

Definition transfer_from_amount (transferFrom_act_p : (Address * Address * EIP20Token.Msg)) := 
  match (snd transferFrom_act_p) with
  | (transfer_from _ _ amount ) => amount
  | _ => 0
  end.

Definition allower_reapproves_delegate_step allower delegate step := 
  let acts := acts_of_lcstep step in
  match find isSome (map get_approve_act acts) with
  | Some (Some (caddr, caller, (approve delegate' amount)) as act)  =>  
    if address_eqb caller allower && address_eqb delegate delegate'
    then Some amount
    else None
  | _ => None
  end.

Definition delegate_transferFrom_sum_of_approver approver delegate trace := 
  fold_left (fun acc step =>
    let transfer_from_acts := fold_left (fun acc act =>
      match get_transferFrom_act act with
      | Some x => x :: acc
      | None => acc
      end 
    ) (acts_of_lcstep step) [] in
    let filter_p p := if address_eqb (allower_addr p) approver
                      then match delegate_addr p with
                           | Some delegate' => address_eqb delegate delegate'
                           | None => false
                           end 
                      else false in
    let relevant_transfer_from_acts := filter filter_p transfer_from_acts in
    let step_sum := fold_left (fun acc p => (transfer_from_amount p) + acc) relevant_transfer_from_acts 0 in
    step_sum + acc
  ) trace 0.

Extract Constant defNumDiscards => "(3 * defNumTests)".

Fixpoint last_opt {A : Type} (l : list A) : option A :=
  match l with
  | [] => None
  | x::[] => Some x
  | x::xs => last_opt xs
  end.

Definition allower_reapproves_transferFrom_correct trace allower delegate (first_approval_amount : N) :=
  match last_opt trace with
  | None => false ==> true
  | Some start_step =>
    let start_lc := next_lc_of_lcstep start_step in
    reachableFrom_implies_tracePropSized_new 2 start_lc (gEIP20TokenChainTraceList 2)
    (allower_reapproves_delegate_step allower delegate)
    (fun new_approval_amount pre_trace _ =>
      let trace_until_reapproval := app trace (removelast pre_trace) in
      let delegate_spent_until_reapproval := delegate_transferFrom_sum_of_approver allower delegate trace_until_reapproval in 
      let delegate_spent_incl_reapproval_act := 
        delegate_transferFrom_sum_of_approver allower delegate (trace ++ pre_trace) in 
      let total_allowed := delegate_spent_until_reapproval + new_approval_amount in
      (new_approval_amount <? first_approval_amount) ==>
      whenFail (show delegate ++ " spent "
        ++ show delegate_spent_incl_reapproval_act
        ++ " on behalf of " ++ show allower
        ++ " when they were only allowed to spend at most "
        ++ show total_allowed  ++ nl)
      (delegate_spent_incl_reapproval_act <=? total_allowed) 
    )
  end.

Definition reapprove_transfer_from_safe_P := 
  (reachableFrom_implies_tracePropSized_new 3 chain_with_token_deployed (gEIP20TokenChainTraceList 1))
  state_has_some_approve_act
  (fun approve_act_p pre_trace post_trace =>
    (* (delegate_made_no_transferFroms approve_act_p post_trace   *)
    isSomeCheck (delegate_addr approve_act_p) (fun delegate =>
      allower_reapproves_transferFrom_correct post_trace
                                              (allower_addr approve_act_p)
                                              delegate
                                              (approve_amount approve_act_p)     
      ) 
    (* ) *)
  ).

QuickChick reapprove_transfer_from_safe_P.

(* Definition transfer_from_reduces_balance_correctly_P := . *)