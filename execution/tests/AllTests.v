Set Warnings "-extraction-inside-module".

From QuickChick Require Import QuickChick. Import QcNotation.
Require Import BinNat.
From ConCert Require Import Blockchain.
From ConCert.Execution.QCTests Require Import TraceGens TestUtils.
From ConCert.Execution.QCTests Require
  CongressTests Congress_BuggyTests DexterTests EIP20TokenTests
  EscrowTests FA2TokenTests iTokenBuggyTests BATTests
  BAT_FixedTests.


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

QuickChick (
  {{fun _ _ => true}}
  congress_caddr
  {{receive_state_well_behaved_P}}
).
(* *** Failed after 10 tests and 1 shrinks. (0 discards) *)
End Congress_Buggy.



(* DexterTests *)
Module Dexter.
Import DexterTests.

QuickChick tokens_to_asset_correct.
(* *** Failed after 1 tests and 1 shrinks. (0 discards) *)
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

QuickChick (sum_allowances_le_init_supply_P 5).
(* *** Failed after 21 tests and 8 shrinks. (0 discards) *)

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

QuickChick reapprove_transfer_from_safe_P.
(* *** Failed after 1 tests and 4 shrinks. (14 discards) *)
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

(* Test doesn't work *)(*
QuickChick (
  {{ msg_is_transfer }}
    token_contract_base_addr
  {{ post_transfer_correct }}
  chain_without_transfer_hook).*)

(* Test doesn't work *)(*
QuickChick (forAllFA2TracesStatePairs chain_with_transfer_hook 1 transfer_balances_correct).*)

(* Test doesn't work *)(*
QuickChick (forAllFA2TracesStatePairs chain_with_transfer_hook 10 transfer_satisfies_policy_P).*)

(* Test doesn't work *)(*
QuickChick (
  {{msg_is_update_operator}}
  token_contract_base_addr
  {{post_last_update_operator_occurrence_takes_effect}}
  chain_without_transfer_hook
).*)
End FA2Token.



Module iTokenBuggy.
Import iTokenBuggyTests.

QuickChick token_supply_preserved.
(* *** Failed after 5 tests and 1000 shrinks. (0 discards) *)

QuickChick (forAllTokenChainTraces 4 (checker_get_state sum_balances_eq_init_supply_checker)).
(* *** Failed after 1 tests and 7 shrinks. (0 discards) *)

QuickChick (
  {{msg_is_not_mint_or_burn}}
  token_caddr
  {{sum_balances_unchanged}}
).
(* *** Failed after 3 tests and 8 shrinks. (0 discards) *)
End iTokenBuggy.



Module BAT.
Import BATTests.
Import TestInfo.

QuickChick (expectFailure (
  {{fun state msg => negb (msg_is_create_tokens state msg)}}
  contract_addr
  {{amount_is_zero}}
)).
(* +++ Failed (as expected) after 65 tests and 9 shrinks. (0 discards) *)

QuickChick (
  {{msg_is_create_tokens}}
  contract_addr
  {{amount_is_positive}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (
  {{msg_is_eip_msg ||| msg_is_create_tokens}}
  contract_addr
  {{produces_no_actions}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (
  {{msg_is_refund ||| msg_is_finalize}}
  contract_addr
  {{produces_one_action}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (
  {{fun state msg => true}}
  contract_addr
  {{constants_unchanged}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_create_tokens}} contract_addr {{create_tokens_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_finalize}} contract_addr {{finalize_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_refund}} contract_addr {{post_refund_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_refund}} contract_addr {{refund_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_refund}} contract_addr {{post_refund_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer}} contract_addr {{transfer_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer_from}} contract_addr {{transfer_from_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_approve}} contract_addr {{post_approve_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_approve}} contract_addr {{approve_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_approve}} contract_addr {{post_approve_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{contract_balance_lower_bound}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (expectFailure ({{contract_balance_lower_bound'}})).
(* +++ Failed (as expected) after 2 tests and 7 shrinks. (0 discards) *)

QuickChick (partially_funded_cb ~~> is_fully_refunded).
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 140 tests and 0 shrinks. (0 discards) *)

QuickChick (expectFailure ({{can_always_fully_refund}})).
(* +++ Failed (as expected) after 6 tests and 7 shrinks. (0 discards) *)

QuickChick (token_cb ~~> is_finalized).
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 6 tests and 0 shrinks. (0 discards) *)

QuickChick final_is_final.
(* +++ Passed 10000 tests (6329 discards) *)

QuickChick can_only_finalize_once.
(* +++ Passed 10000 tests (0 discards) *)

QuickChick final_implies_total_supply_in_range.
(* +++ Passed 10000 tests (6125 discards) *)

QuickChick final_implies_total_supply_constant.
(* +++ Passed 10000 tests (6246 discards) *)

QuickChick final_implies_contract_balance_is_zero.
(* +++ Passed 10000 tests (6179 discards) *)

QuickChick (expectFailure ({{total_supply_bounds}})).
(* +++ Failed (as expected) after 3 tests and 7 shrinks. (0 discards) *)

QuickChick ({{total_supply_eq_sum_balances}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{paid_tokens_modulo_exchange_rate}}).
(* +++ Passed 10000 tests (0 discards) *)
End BAT.



Module BAT_Fixed.
Import BAT_FixedTests.
Import TestInfo.

QuickChick (
  {{fun state msg => negb (msg_is_create_tokens state msg)}}
  contract_addr
  {{amount_is_zero}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (
  {{msg_is_create_tokens}}
  contract_addr
  {{amount_is_positive}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (
  {{msg_is_eip_msg ||| msg_is_create_tokens}}
  contract_addr
  {{produces_no_actions}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (
  {{msg_is_refund ||| msg_is_finalize}}
  contract_addr
  {{produces_one_action}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (
  {{fun state msg => true}}
  contract_addr
  {{constants_unchanged}}
).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_create_tokens}} contract_addr {{create_tokens_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_finalize}} contract_addr {{finalize_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_refund}} contract_addr {{post_refund_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_refund}} contract_addr {{refund_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_refund}} contract_addr {{post_refund_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer}} contract_addr {{transfer_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer_from}} contract_addr {{transfer_from_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_approve}} contract_addr {{post_approve_update_correct}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_approve}} contract_addr {{approve_valid}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{msg_is_approve}} contract_addr {{post_approve_safe}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{contract_balance_lower_bound}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{contract_balance_lower_bound'}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (partially_funded_cb ~~> is_fully_refunded).
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 140 tests and 0 shrinks. (0 discards) *)

QuickChick ({{can_always_fully_refund}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick (token_cb ~~> is_finalized).
(* Success - found witness satisfying the predicate!
+++ Failed (as expected) after 6 tests and 0 shrinks. (0 discards) *)

QuickChick final_is_final.
(* +++ Passed 10000 tests (4310 discards) *)

QuickChick can_only_finalize_once.
(* +++ Passed 10000 tests (0 discards) *)

QuickChick final_implies_total_supply_in_range.
(* +++ Passed 10000 tests (4281 discards) *)

QuickChick final_implies_total_supply_constant.
(* +++ Passed 10000 tests (4223 discards)) *)

QuickChick final_implies_contract_balance_is_zero.
(* +++ Passed 10000 tests (4153 discards) *)

QuickChick ({{total_supply_bounds}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{total_supply_eq_sum_balances}}).
(* +++ Passed 10000 tests (0 discards) *)

QuickChick ({{paid_tokens_modulo_exchange_rate}}).
(* +++ Passed 10000 tests (0 discards) *)
End BAT_Fixed.

