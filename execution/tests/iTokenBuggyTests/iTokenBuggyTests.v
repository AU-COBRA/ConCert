Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.

From ConCert Require Import Blockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN.
From ConCert Require Import Containers.
From ConCert Require Import iTokenBuggy.
From ConCert Require Import ResultMonad.
Require Import Extras.

From ConCert.Execution.QCTests Require Import
  TestUtils ChainPrinters iTokenBuggyPrinters iTokenBuggyGens TraceGens.

From Coq Require Import List. 
Import ListNotations.
Import BoundedN.Stdpp.
Import LocalBlockchain.

(* -------------------------- Tests of the Buggy iToken Implementation -------------------------- *)

(* F# style piping notation *)
Notation "f <| x" := (f x) (at level 91, left associativity, only parsing).
(* i.e. f <| x <| y = (f <| x) <| y, and means (f x) y *)
Notation "x |> f" := (f x) (at level 31, left associativity, only parsing).
(* i.e. x |> f |> g = (x |> f) |> g, and means g (f x) *)

Existing Instance showTokenState.
Existing Instance iTokenBuggyPrinters.showMsg.

Open Scope string_scope.
Global Instance showSerializedValue : Show SerializedValue :=
{|
    show v := match @deserialize iTokenBuggy.Msg _ v with
    | Some v => show v
    | None => "<FAILED DESERIALIZATION>"
    end
|}.
Close Scope string_scope.
Definition token_setup := iTokenBuggy.build_setup creator (100%N).
Definition deploy_iToken := create_deployment 0 iTokenBuggy.contract token_setup.
Definition token_caddr := BoundedN.of_Z_const AddrSize 128%Z.

(* In the initial chain we transfer some assets to a few accounts, just to make the addresses
   present in the chain state. The amount transferred is irrelevant. *)
Definition token_cb :=
  ResultMonad.unpack_result (TraceGens.add_block (lcb_initial AddrSize)
  [
    build_act creator (act_transfer person_1 0);
    build_act creator (act_transfer person_2 0);
    build_act creator (act_transfer person_3 0);
    build_act creator deploy_iToken
  ]).

Module TestInfo <: iTokenBuggyGensInfo.
  Definition contract_addr := token_caddr.
  Definition gAccount (c : Chain) := elems [person_1; person_2; person_3].
End TestInfo.
Module MG := iTokenBuggyGens TestInfo. Import MG.

Definition gTokenChain max_acts_per_block token_cb max_length := 
  let act_depth := 1 in 
  gChain token_cb
    (fun env act_depth => giTokenBuggyAction env) max_length act_depth max_acts_per_block.
(* Sample (gTokenChain 2 token_cb 7).  *)

(* 'forAll' checker for this iToken chain generator *)
Definition forAllTokenChainTraces n :=
  let max_acts_per_block := 2 in
  forAllBlocks n token_cb (gTokenChain max_acts_per_block).

Instance genBuggyTokenChainSized : GenSized ChainBuilder := {
  arbitrarySized n := gTokenChain 5 token_cb n
}.

Definition pre_post_assertion_token P c Q :=
  let max_acts_per_block := 2 in
  let trace_length := 4 in
  pre_post_assertion trace_length token_cb (gTokenChain max_acts_per_block) iTokenBuggy.contract c P Q.
Notation "{{ P }} c {{ Q }}" := (pre_post_assertion_token P c Q) ( at level 50).

Definition checker_get_state {prop} `{Checkable prop} (pf : State -> prop) (cs : ChainState) : Checker := 
  match get_contract_state iTokenBuggy.State cs token_caddr with
  | Some state => checker (pf state)
  | None => checker true (* trivially true case *) 
  end.

(* bool variant of checker_get_state *)
Definition get_state (pf : State -> bool) (cs : ChainState) : bool := 
  match get_contract_state iTokenBuggy.State cs token_caddr with
  | Some state => pf state
  | None => true (* trivially true case *) 
  end.

Open Scope N_scope.
Open Scope string_scope.
(* One key property: the sum of the balances is always equal to the initial supply *)
Definition sum_balances_eq_init_supply_checker (state : iTokenBuggy.State) :=
  let balances_list := state.(balances) |> FMap.elements |> map snd in
  let balances_sum : N := fold_left N.add balances_list 0%N in
  whenFail
    <| "balances_sum: " ++ show balances_sum ++ nl ++
       "total_supply: " ++ show state.(total_supply) ++ nl ++
       "balances: " ++ show state.(balances)
    <| N.eqb balances_sum state.(total_supply).
  
Close Scope string_scope.

Definition sum_balances_eq_init_supply (state : iTokenBuggy.State) : bool :=
  let balances_sum := state.(balances) |> FMap.elements
                                       |> map snd 
                                       |> fold_right N.add 0 in
  balances_sum =? state.(total_supply).

Conjecture token_supply_preserved : forall sig_to : {to | reachable to}, 
  let to := proj1_sig sig_to in
  get_state sum_balances_eq_init_supply to = true.

(* QuickChick token_supply_preserved. *)
(* Or alternatively, for better output: *)
(* QuickChick (forAllTokenChainTraces 4 (checker_get_state sum_balances_eq_init_supply_checker)). *)
(* *** Failed after 5 tests and 1000 shrinks. (0 discards) *)
(* Action{act_from: 11%256, act_body: (act_call 128%256, 0, withdraw)}}
balances_sum: 12
total_supply: 10
balances: [11%256-->1; 13%256-->2; 10%256-->9] *)

Definition msg_is_not_mint_or_burn (state : iTokenBuggy.State) (msg : iTokenBuggy.Msg) :=
  match msg with
  | mint _ => false
  | burn _ => false
  | _ => true
  end.

Definition sum_balances_unchanged (chain : Chain)
                                  (cctx : ContractCallContext)
                                  (old_state : State)
                                  (msg : Msg)
                                  (result_opt : option (State * list ActionBody))
                                  : Checker :=
  (* sum all entries in the balances field of a given iToken contract state *)
  let balances_sum s := s.(balances) |> FMap.elements 
                                     |> map snd
                                     |> fold_right N.add 0%N in
  match result_opt with
  | Some (new_state, _) => checker <| balances_sum old_state =? balances_sum new_state 
  | None => false ==> true
  end.

(* QuickChick (
  {{msg_is_not_mint_or_burn}}
  token_caddr
  {{sum_balances_unchanged}}
). *)
(* *** Failed after 1 tests and 0 shrinks. (0 discards)
       On Msg: transfer_from 13%256 13%256 1 *)