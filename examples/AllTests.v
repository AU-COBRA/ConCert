Set Warnings "-extraction-inside-module".

From Coq Require Import BinNat.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Congress Require CongressTests.
From ConCert.Examples.Congress Require Congress_BuggyTests.
From ConCert.Examples.ExchangeBuggy Require ExchangeBuggyTests.
From ConCert.Examples.Dexter Require DexterTests.
From ConCert.Examples.Dexter2 Require Dexter2Tests.
From ConCert.Examples.EIP20 Require EIP20TokenTests.
From ConCert.Examples.Escrow Require EscrowTests.
From ConCert.Examples.FA2 Require FA2TokenTests.
From ConCert.Examples.iTokenBuggy Require iTokenBuggyTests.
From ConCert.Examples.BAT Require BATTestCommon.
From ConCert.Examples.BAT Require BATTests.
From ConCert.Examples.BAT Require BATFixedTests.
From ConCert.Examples.BAT Require BATAltFixTests.


Module Congress.
  Import CongressTests.
  Import TN.

  Time QuickChick (
    {{fun _ _ => true}}
    congress_caddr
    {{receive_state_well_behaved_P}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (forAllBlocks state_proposals_proposed_in_valid).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (chain5 ~~> congress_has_votes_on_some_proposal).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 4 tests and 0 shrinks. (0 discards) *)

  Time QuickChick (chain5 ~~> congress_finished_a_vote).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 11 tests and 0 shrinks. (0 discards) *)
End Congress.



Module Congress_Buggy.
  Import Congress_BuggyTests.
  Import TN.

  Time QuickChick (expectFailure (
    {{fun _ _ => true}}
    congress_caddr
    {{receive_state_well_behaved_P}}
  )).
  (* *** Failed (as expected) after 10 tests and 1 shrinks. (0 discards) *)
End Congress_Buggy.



Module ExchangeBuggy.
  Import ExchangeBuggyTests.

  Time QuickChick (expectFailure tokens_to_asset_correct).
  (* *** Failed (as expected) after 1 tests and 1 shrinks. (0 discards) *)
End ExchangeBuggy.



Module Dexter.
  Import DexterTests.

  Extract Constant DepthFirst => "false".
  Time QuickChick (expectFailure tokens_to_asset_correct).
  (* +++ Failed (as expected) after 26 tests and 2 shrinks. (0 discards) *)

  Extract Constant DepthFirst => "true".
  Time QuickChick (tokens_to_asset_correct).
  (* +++ Passed 10000 tests (0 discards) *)
End Dexter.



Module Dexter2.
  Import Dexter2Tests.
  Import TestInfo.
  Import TN.

  (* Run tests in breadth-first execution model *)
  Extract Constant DepthFirst => "false".
  Time QuickChick ({{msg_is_balance_of_callback}} cpmm_contract_base_addr {{callback_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{is_syncing}} cpmm_contract_base_addr {{only_callbacks}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (forAllBlocks token_reserve_safe).
  (* +++ Passed 10000 tests (0 discards) *)


  (* Run tests in depth-first execution model *)
  Extract Constant DepthFirst => "true".
  Time QuickChick ({{msg_is_balance_of_callback}} cpmm_contract_base_addr {{callback_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{is_syncing}} cpmm_contract_base_addr {{only_callbacks}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (forAllBlocks token_reserve_safe).
  (* +++ Passed 10000 tests (0 discards) *)
End Dexter2.



Module EIP20Token.
  Import EIP20TokenTests.
  Import TestInfo.
  Import TN.

  Time QuickChick (
    {{fun _ _ => true}}
    contract_addr
    {{post_not_payable}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{fun _ _ => true}}
    contract_addr
    {{post_no_new_acts}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{fun _ _ => true}}
    contract_addr
    {{post_total_supply_constant}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_transfer}}
    contract_addr
    {{post_transfer_correct}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_transfer_from}}
    contract_addr
    {{post_transfer_from_correct}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_approve}}
    contract_addr
    {{post_approve_correct}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (forAllBlocks (checker_get_state sum_balances_eq_total_supply)).
  (* Passed 10000 tests (0 discards) *)

  Time QuickChick (forAllBlocks (checker_get_state init_supply_eq_total_supply)).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (expectFailure (sum_allowances_le_init_supply_P)).
  (* *** Failed (as expected) after 21 tests and 8 shrinks. (0 discards) *)

  Time QuickChick (token_cb ~~> (person_has_tokens person_3 12)).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 1 tests and 0 shrinks. (0 discards) *)

  Time QuickChick (token_cb ~~> person_has_tokens creator 0).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 1 tests and 0 shrinks. (0 discards)*)
  
  Time QuickChick (expectFailure (
    token_cb
    ~~~> (fun cs => if person_has_tokens creator 5 cs.(chain_state_env) then Some tt else None)
    ===> (fun _ _ post_trace => person_has_tokens creator 10 (last post_trace empty_state))
  )).
  (* *** Failed after 1 tests and 9 shrinks. (0 discards) *)

  Time QuickChick (expectFailure reapprove_transfer_from_safe_P).
  (* *** Failed (as expected) after 1 tests and 4 shrinks. (14 discards) *)
End EIP20Token.



Module Escrow.
  Import EscrowTests.
  Import MG.

  Time QuickChick (forAllEscrowChainBuilder gEscrowTrace 7 escrow_chain escrow_correct_P).
  (* *** Gave up! Passed only 8529 tests
  Discarded: 20000 *)

  Time QuickChick (forAllEscrowChainBuilder gEscrowTraceBetter 7 escrow_chain escrow_correct_P).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick escrow_valid_steps_P.
  (* +++ Passed 10000 tests (0 discards) *)
End Escrow.



Module FA2Token.
  Import FA2TokenTests.
  Import TestInfo.
  Import TN.

  Time QuickChick (
    {{ msg_is_transfer }}
      token_contract_base_addr
    {{ post_transfer_correct }}
    chain_without_transfer_hook).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (forAllChainStatePairs transfer_balances_correct).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (forAllChainStatePairs transfer_satisfies_policy_P).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_update_operator}}
    token_contract_base_addr
    {{post_last_update_operator_occurrence_takes_effect}}
    chain_without_transfer_hook
  ).
  (* +++ Passed 10000 tests (0 discards) *)
End FA2Token.



Module iTokenBuggy.
  Import iTokenBuggyTests.
  Import TN.

  Time QuickChick (expectFailure token_supply_preserved).
  (* *** Failed (as expected) after 5 tests and 1000 shrinks. (0 discards) *)

  Time QuickChick (expectFailure (forAllBlocks (checker_get_state sum_balances_eq_init_supply_checker))).
  (* *** Failed (as expected) after 1 tests and 7 shrinks. (0 discards) *)

  Time QuickChick (expectFailure (
    {{msg_is_not_mint_or_burn}}
    token_caddr
    {{sum_balances_unchanged}}
  )).
  (* *** Failed (as expected) after 3 tests and 8 shrinks. (0 discards) *)
End iTokenBuggy.



Module BAT.
  Import BATTests.
  Import TestInfo.
  Import MG TN.
  Import BATTestCommon.

  Time QuickChick (
    {{fun state msg => negb (msg_is_create_tokens state msg)}}
    contract_addr
    {{amount_is_zero}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_create_tokens}}
    contract_addr
    {{amount_is_positive}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_eip_msg ||| msg_is_create_tokens}}
    contract_addr
    {{produces_no_actions}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_refund ||| msg_is_finalize}}
    contract_addr
    {{produces_one_action}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{fun state msg => true}}
    contract_addr
    {{constants_unchanged}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{create_tokens_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{finalize_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{post_refund_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{refund_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{post_refund_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{transfer_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{transfer_from_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{post_approve_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{approve_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{post_approve_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{contract_balance_lower_bound}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (expectFailure ({{contract_balance_lower_bound'}})).
  (* +++ Failed (as expected) after 2 tests and 7 shrinks. (0 discards) *)

  Time QuickChick (partially_funded_cb ~~> is_fully_refunded).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 140 tests and 0 shrinks. (0 discards) *)

  Time QuickChick (expectFailure ({{can_always_fully_refund}})).
  (* +++ Failed (as expected) after 6 tests and 7 shrinks. (0 discards) *)

  Time QuickChick (token_cb ~~> is_finalized).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 6 tests and 0 shrinks. (0 discards) *)

  Time QuickChick final_is_final.
  (* +++ Passed 10000 tests (6329 discards) *)

  Time QuickChick can_only_finalize_once.
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick final_implies_total_supply_in_range.
  (* +++ Passed 10000 tests (6125 discards) *)

  Time QuickChick final_implies_total_supply_constant.
  (* +++ Passed 10000 tests (6246 discards) *)

  Time QuickChick final_implies_contract_balance_is_zero.
  (* +++ Passed 10000 tests (6179 discards) *)

  Time QuickChick (expectFailure ({{total_supply_bounds}})).
  (* +++ Failed (as expected) after 3 tests and 7 shrinks. (0 discards) *)

  Time QuickChick ({{total_supply_eq_sum_balances}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{paid_tokens_modulo_exchange_rate}}).
  (* +++ Passed 10000 tests (0 discards) *)
End BAT.



Module BATFixed.
  Import BATFixedTests.
  Import TestInfo.
  Import MG TN.
  Import BATTestCommon.

  Time QuickChick (
    {{fun state msg => negb (msg_is_create_tokens state msg)}}
    contract_addr
    {{amount_is_zero}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_create_tokens}}
    contract_addr
    {{amount_is_positive}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_eip_msg ||| msg_is_create_tokens}}
    contract_addr
    {{produces_no_actions}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_refund ||| msg_is_finalize}}
    contract_addr
    {{produces_one_action}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{fun state msg => true}}
    contract_addr
    {{constants_unchanged}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{create_tokens_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{finalize_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{post_refund_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{refund_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{post_refund_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{transfer_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{transfer_from_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{post_approve_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{approve_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{post_approve_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{contract_balance_lower_bound}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{contract_balance_lower_bound'}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (partially_funded_cb ~~> is_fully_refunded).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 140 tests and 0 shrinks. (0 discards) *)

  Time QuickChick ({{can_always_fully_refund}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (token_cb ~~> is_finalized).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 6 tests and 0 shrinks. (0 discards) *)

  Time QuickChick final_is_final.
  (* +++ Passed 10000 tests (4310 discards) *)

  Time QuickChick can_only_finalize_once.
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick final_implies_total_supply_in_range.
  (* +++ Passed 10000 tests (4281 discards) *)

  Time QuickChick final_implies_total_supply_constant.
  (* +++ Passed 10000 tests (4223 discards)) *)

  Time QuickChick final_implies_contract_balance_is_zero.
  (* +++ Passed 10000 tests (4153 discards) *)

  Time QuickChick ({{total_supply_bounds}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{total_supply_eq_sum_balances}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{paid_tokens_modulo_exchange_rate}}).
  (* +++ Passed 10000 tests (0 discards) *)
End BATFixed.



Module BATAltFix.
  Import BATAltFixTests.
  Import TestInfo.
  Import MG TN.
  Import BATTestCommon.

  Time QuickChick (
    {{fun state msg => negb (msg_is_create_tokens state msg)}}
    contract_addr
    {{amount_is_zero}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_create_tokens}}
    contract_addr
    {{amount_is_positive}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_eip_msg ||| msg_is_create_tokens}}
    contract_addr
    {{produces_no_actions}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{msg_is_refund ||| msg_is_finalize}}
    contract_addr
    {{produces_one_action}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (
    {{fun state msg => true}}
    contract_addr
    {{constants_unchanged}}
  ).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{create_tokens_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_create_tokens}} contract_addr {{post_create_tokens_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{finalize_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_finalize}} contract_addr {{post_finalize_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{post_refund_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{refund_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_refund}} contract_addr {{post_refund_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{transfer_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer}} contract_addr {{post_transfer_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{transfer_from_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_transfer_from}} contract_addr {{post_transfer_from_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{post_approve_update_correct}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{approve_valid}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{msg_is_approve}} contract_addr {{post_approve_safe}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{contract_balance_lower_bound}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (partially_funded_cb ~~> is_fully_refunded).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 13 tests and 0 shrinks. (0 discards) *)

  Time QuickChick ({{can_always_fully_refund}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick (token_cb ~~> is_finalized).
  (* Success - found witness satisfying the predicate!
  +++ Failed (as expected) after 7 tests and 0 shrinks. (0 discards) *)

  Time QuickChick final_is_final.
  (* +++ Passed 10000 tests (4517 discards) *)

  Time QuickChick can_only_finalize_once.
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick final_implies_total_supply_in_range.
  (* +++ Passed 10000 tests (4529 discards) *)

  Time QuickChick final_implies_total_supply_constant.
  (* +++ Passed 10000 tests (4662 discards) *)

  Time QuickChick final_implies_contract_balance_is_zero.
  (* +++ Passed 10000 tests (4424 discards) *)

  Time QuickChick ({{total_supply_bounds}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{total_supply_eq_sum_balances}}).
  (* +++ Passed 10000 tests (0 discards) *)

  Time QuickChick ({{paid_tokens_modulo_exchange_rate}}).
  (* +++ Passed 10000 tests (0 discards) *)
End BATAltFix.
