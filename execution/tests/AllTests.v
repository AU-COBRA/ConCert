From QuickChick Require Import QuickChick. Import QcNotation.
From ConCert.Execution.QCTests Require Import
 CongressTests Congress_BuggyTests DexterTests EIP20TokenTests EscrowTests FA2TokenTests iTokenBuggyTests TraceGens TestUtils.
Require Import BinNat.
From ConCert Require Import Blockchain.

(* CongressTests *)
QuickChick (CongressTests.CongressTests.pre_post_assertion_congress (fun _ _ => true)
  congress_caddr CongressTests.CongressTests.receive_state_well_behaved_P).
QuickChick (CongressTests.CongressTests.forAllCongressChainTraces 5 CongressTests.CongressTests.state_proposals_proposed_in_valid).
QuickChick (reachableFrom_chaintrace_congress CongressTests.CongressTests.chain5 CongressTests.CongressTests.congress_has_votes_on_some_proposal).
QuickChick (reachableFrom_chaintrace_congress CongressTests.CongressTests.chain5 CongressTests.CongressTests.congress_finished_a_vote).

(* Congress_BuggyTests *)
QuickChick (Congress_BuggyTests.pre_post_assertion_congress (fun _ _ => true) congress_caddr Congress_BuggyTests.receive_state_well_behaved_P).

(* DexterTests *)
QuickChick DexterTests.tokens_to_asset_correct.

(* EIP20TokenTests *)
QuickChick (EIP20TokenTests.pre_post_assertion_token EIP20TokenTests.msg_is_transfer
  EIP20TokenTests.contract_base_addr EIP20TokenTests.post_transfer_correct).
QuickChick (EIP20TokenTests.forAllTokenChainTraces 5 (EIP20TokenTests.checker_get_state EIP20TokenTests.sum_balances_eq_init_supply)).
QuickChick (EIP20TokenTests.sum_allowances_le_init_supply_P 5).
QuickChick (reachableFrom_chaintrace EIP20TokenTests.token_cb (EIP20TokenTests.gTokenChain 2)
  (EIP20TokenTests.person_has_tokens person_3 12%N)).
QuickChick (reachableFrom_chaintrace EIP20TokenTests.token_cb (EIP20TokenTests.gTokenChain 2)
  (EIP20TokenTests.person_has_tokens creator 0%N)).
QuickChick EIP20TokenTests.reapprove_transfer_from_safe_P.

(* EscrowTests *)
QuickChick (EscrowTests.forAllEscrowChainBuilder EscrowTests.MG.gEscrowTrace 7 EscrowTests.escrow_chain escrow_correct_P).
QuickChick (EscrowTests.forAllEscrowChainBuilder EscrowTests.MG.gEscrowTraceBetter 7 EscrowTests.escrow_chain escrow_correct_P).
QuickChick EscrowTests.escrow_valid_steps_P.

(* FA2TokenTests *)
QuickChick (forAll FA2TokenTests.TestInfo.gUniqueAddrPair (fun p => isSomeCheck p (fun '(addr1, addr2) => negb (address_eqb addr1 addr2)))).
QuickChick (pre_post_assertion 7 FA2TokenTests.chain_with_token_deployed_without_hook (FA2TokenTests.gFA2TokenChain 1)
  FA2Token.contract FA2TokenTests.token_contract_base_addr FA2TokenTests.msg_is_transfer FA2TokenTests.post_transfer_correct).
QuickChick (FA2TokenTests.forAllFA2TracesStatePairs FA2TokenTests.chain_with_token_deployed_with_hook 1 FA2TokenTests.transfer_balances_correct).
QuickChick (FA2TokenTests.forAllFA2TracesStatePairs FA2TokenTests.chain_with_token_deployed_with_hook 10 FA2TokenTests.transfer_satisfies_policy_P).
QuickChick (pre_post_assertion 7 FA2TokenTests.chain_with_token_deployed_without_hook (FA2TokenTests.gFA2TokenChain 1)
  FA2Token.contract FA2TokenTests.token_contract_base_addr FA2TokenTests.msg_is_update_operator
  FA2TokenTests.post_last_update_operator_occurrence_takes_effect).

(* iTokenBuggyTests *)
QuickChick iTokenBuggyTests.token_supply_preserved.
QuickChick (iTokenBuggyTests.forAllTokenChainTraces 4 (iTokenBuggyTests.checker_get_state iTokenBuggyTests.sum_balances_eq_init_supply_checker)).
QuickChick (iTokenBuggyTests.pre_post_assertion_token iTokenBuggyTests.msg_is_not_mint_or_burn
  iTokenBuggyTests.token_caddr iTokenBuggyTests.sum_balances_unchanged).
