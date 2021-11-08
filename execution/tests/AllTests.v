Set Warnings "-extraction-inside-module".

From QuickChick Require Import QuickChick. Import QcNotation.
Require Import BinNat.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution.QCTests Require Import TraceGens TestUtils.
From ConCert.Execution.QCTests Require CongressTests Congress_BuggyTests DexterTests EIP20TokenTests EscrowTests FA2TokenTests iTokenBuggyTests.


Module Congress.
Import CongressTests.

QuickChick (
  {{fun _ _ => true}}
  congress_caddr
  {{receive_state_well_behaved_P}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (forAllCongressChainTraces 5 state_proposals_proposed_in_valid).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (chain5 ~~> congress_has_votes_on_some_proposal).
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 4 tests and 0 shrinks. (0 discards) *)

QuickChick (chain5 ~~> congress_finished_a_vote).
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 11 tests and 0 shrinks. (0 discards) *)
End Congress.



Module Congress_Buggy.
Import Congress_BuggyTests.

QuickChick (expectFailure (
  {{fun _ _ => true}}
  congress_caddr
  {{receive_state_well_behaved_P}}
)).
(* *** Failed (as expected) after 10 tests and 1 shrinks. (0 discards) *)
End Congress_Buggy.



(* DexterTests *)
Module Dexter.
Import DexterTests.

QuickChick (expectFailure tokens_to_asset_correct).
(* *** Failed (as expected) after 1 tests and 1 shrinks. (0 discards) *)
End Dexter.



Module EIP20Token.
Import EIP20TokenTests.
Import TestInfo.

QuickChick (
  {{msg_is_transfer}}
  contract_addr
  {{post_transfer_correct}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (forAllTokenChainTraces 5 (checker_get_state sum_balances_eq_init_supply)).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (expectFailure (sum_allowances_le_init_supply_P 5)).
(* *** Failed (as expected) after 21 tests and 8 shrinks. (0 discards) *)

QuickChick (token_cb ~~> (person_has_tokens person_3 12)).
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 1 tests and 0 shrinks. (0 discards) *)

(* Test doesn't work *)(*
QuickChick (chain_with_token_deployed ~~> (fun lc => isSome (person_has_tokens person_3 12 lc))).*)

(* Test doesn't work *)(*
QuickChick (chain_with_token_deployed ~~> person_has_tokens creator 0).*)

(* Test doesn't work *)(*
QuickChick (token_reachableFrom_implies_reachable
  chain_with_token_deployed
  (person_has_tokens creator 10)
  (person_has_tokens creator 0)
).*)

(* Test doesn't work *)(*
QuickChick (
  {
    chain_with_token_deployed
    ~~> (person_has_tokens creator 5 o next_lc_of_lcstep)
    ===> (fun _ _ post_trace => isSome (person_has_tokens creator 10 (last_state post_trace)))
  }
).*)

QuickChick (expectFailure reapprove_transfer_from_safe_P).
(* *** Failed (as expected) after 1 tests and 4 shrinks. (14 discards) *)
End EIP20Token.



Module Escrow.
Import EscrowTests.
Import MG.

QuickChick (forAllEscrowChainBuilder gEscrowTrace 7 escrow_chain escrow_correct_P).
(* *** Gave up! Passed only 8529 tests
Discarded: 20000 *)

QuickChick (forAllEscrowChainBuilder gEscrowTraceBetter 7 escrow_chain escrow_correct_P).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick escrow_valid_steps_P.
(* +++ Passed 10000 tests (0 discards) *)
End Escrow.



Module FA2Token.
Import FA2TokenTests.
Import TestInfo.

QuickChick (forAll gUniqueAddrPair (fun p => isSomeCheck p (fun '(addr1, addr2) => negb (address_eqb addr1 addr2)))).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (
  {{ msg_is_transfer }}
    token_contract_base_addr
  {{ post_transfer_correct }}
  chain_without_transfer_hook).

QuickChick (forAllFA2TracesStatePairs chain_with_transfer_hook 1 transfer_balances_correct).

QuickChick (forAllFA2TracesStatePairs chain_with_transfer_hook 10 transfer_satisfies_policy_P).

QuickChick (
  {{msg_is_update_operator}}
  token_contract_base_addr
  {{post_last_update_operator_occurrence_takes_effect}}
  chain_without_transfer_hook
).
End FA2Token.



Module iTokenBuggy.
Import iTokenBuggyTests.

QuickChick (expectFailure token_supply_preserved).
(* *** Failed (as expected) after 5 tests and 1000 shrinks. (0 discards) *)

QuickChick (expectFailure (forAllTokenChainTraces 4 (checker_get_state sum_balances_eq_init_supply_checker))).
(* *** Failed (as expected) after 1 tests and 7 shrinks. (0 discards) *)

QuickChick (expectFailure (
  {{msg_is_not_mint_or_burn}}
  token_caddr
  {{sum_balances_unchanged}}
)).
(* *** Failed (as expected) after 3 tests and 8 shrinks. (0 discards) *)
End iTokenBuggy.
