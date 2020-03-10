
Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import Containers.
Require Import Extras.

From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters CongressGens SerializablePrinters TraceGens.

(* For monad notations *)
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

From Coq Require Import List Int BinInt FunInd.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import MSets.MSetGenTree.
From Coq Require Import Permutation.

Import BoundedN.Stdpp.

Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.

Definition deploy_congress : @ActionBody Base := create_deployment 5 Congress.contract setup.
(* Definition chain4 : ChainBuilder :=
  unpack_option (add_block chain3 [build_act person_1 deploy_congress]). *)
(* Compute (show chain4). *)
(* Sample (gCongressActionSizedFromLC chain1.(builder_env) 4). *)

QuickChick (forAll 
  (optToVector 1 (gActionOfCongressFromLC c3 3))
  (fun actions => isSome (my_add_block c1 actions) && (0 <? length actions))).
(*
coqtop-stdout:[Action{act_from: 10%256, act_body: (act_call 128%256, 0, create_proposal (transfer: 11%256, 2))}]
*** Failed after 2 tests and 0 shrinks. (0 discards)
*)

Definition add_block_actions_succeeds_P c_opt actions_opt :=
  isSomeCheck c_opt
  (fun c => 
    whenFail (show (lc_account_balances c)) 
      (match actions_opt with
      | Some actions => (0 <? length actions) && isSome (my_add_block c actions)
      | None => false
      end)
  ).

Definition check_add_two_blocks_succeeds := 
  (forAll3 
    (optToVector 3 (gActionOfCongressFromLC c1 2))
    (fun actions => returnGen (my_add_block c1 actions))
    (fun _ c_opt => 
      match c_opt with
      | Some c => acts <- (optToVector 3 (gActionOfCongressFromLC c 2)) ;; returnGen (Some acts) 
      | None => returnGen None
      end)
    (fun _ c_opt actions_opt => add_block_actions_succeeds_P c_opt actions_opt)
  ).

	Definition glctracetree (height : nat) := glctracetree_fix lc_initial gCongressActionNew height.
	Definition glctracetreeFromLC lc (height : nat) := glctracetree_fix lc gCongressActionNew height.
	
	Definition c4 : LocalChain :=
	let acts := [build_act person_1 (add_person person_1);
							 build_act person_1 (add_person person_2);
							 build_act person_1 create_proposal_call] in
			unpack_option (add_block_exec true c3 (next_header_lc c3) acts).
	
	Compute (show (lc_account_balances c4)).
	Compute (show (map fst (FMap.elements (lc_contracts c4)))).
	Compute (show (lc_contract_owners c4)).
	Compute (show (congressContractsMembers c4)).
	Compute (show (congressContractsMembers_nonempty_nonowners c4)).
	Compute (show (lc_proposals c4)).
	
	QuickChick (forAll
		(gCongressActionNew c4 1)
		(fun act_opt => isSomeCheck act_opt
		(fun act => whenFail 
			(show (lc_account_balances c4) ++ sep ++ nl
			++ "valid actions: " ++ show (validate_actions [act]) ++ sep ++ nl
			++ "congress members: " ++ show (congressContractsMembers c4) ++ nl)
			(* ++ "valid header: " ++ (show o isSome) (validate_header (next_header_lc c4) c4)) *)
			(isSome (mk_basic_step_action c4 [act]))))    
	).
	(* Wow!:
		coqtop-stdout:+++ Passed 10000 tests (0 discards) *)
	
	(* Sample (bindGenOpt (gCongressActionNew c4 3) (fun act => if isSome (mk_basic_step_action c4 [act]) 
																																then returnGen ( Some ("success", act)) 
																																else returnGen (Some ("fail", act)))). *)

Definition gCongressChainTraceList lc length := gLocalChainTraceList_fix lc gCongressActionNew length.



(* Sample (liftM allPaths (glctracetreeFromLC c4 3)). *)

(* Sample (gCongressChainTraceList c4 15). *)

	