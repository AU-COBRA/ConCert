# Smart Contract Examples

This subproject contains examples of smart contract implementations along with proofs of
correctness and safety, property-based testing and code extraction.
Each example is described below.

## Basic Attention Token
The Basic Attention Token smart contract is an Ethereum smart contract used by the Brave browser.
This example includes a port of the contract in ConCert along with property-based testing showing
new previously undiscovered bugs in the smart contract.

Additionally, we provide to alternative implementations of the smart contract with the
flaws fixed, and prove these implementations correct and safe.

## Boardroom Voting
In [BoardroomVoting.v](../examples/boardroomVoting/BoardroomVoting.v) we verify functional
correctness of a private boardroom voting contract based on [1] under some
simplifying assumptions. In particular, we do not verify anything about the
zero-knowledge proofs required to make sure that everyone participates correctly
in the smart contract. Instead, we assume that everyone participates correctly
and then show that the smart contract in this case computes the correct result
(i.e. a public tally of the private votes). The statement is the following:

```coq
Theorem boardroom_voting_correct
        bstate caddr (trace : ChainTrace empty_state bstate)
        (* list of all public keys, in the order of signups *)
        (pks : list A)
        (* function mapping a party to his signup index *)
        (index : Address -> nat)
        (* function mapping a party to his secret key *)
        (sks : Address -> Z)
        (* function mapping a party to his vote *)
        (svs : Address -> bool) :
    env_contracts bstate caddr = Some (boardroom_voting : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\

      (* assuming that the message sent were created with the
          functions provided by this smart contract *)
      MsgAssumption pks index sks svs inc_calls ->

      (* ..and that people signed up in the order given by 'index'
          and 'pks' *)
      SignupOrderAssumption pks index inc_calls ->

      (* ..and that the correct number of people register *)
      (finish_registration_by (setup cstate) < Blockchain.current_slot bstate ->
       length pks = length (signups inc_calls)) ->

      (* then if we have not tallied yet, the result is none *)
      ((has_tallied inc_calls = false -> result cstate = None) /\
       (* or if we have tallied yet, the result is correct *)
       (has_tallied inc_calls = true ->
        result cstate = Some (sumnat (fun party => if svs party then 1 else 0)%nat
                                     (FMap.keys (registered_voters cstate))))).
```
The simplifying assumptions are expressed over the messages seen in the
blockchain state. For instance, `MsgAssumption` above captures that everyone
participates correctly by saying that all messages sent to the contract were
created using functions provided by the smart contract:

```coq
Fixpoint MsgAssumption
         (pks : list A)
         (index : Address -> nat)
         (sks : Address -> Z)
         (svs : Address -> bool)
         (calls : list (ContractCallInfo Msg)) : Prop :=
  match calls with
  | call :: calls =>
    let caller := Blockchain.call_from call in
    match Blockchain.call_msg call with
    | Some (signup pk as m) => m = make_signup_msg (sks caller)
    | Some (submit_vote _ _ as m) =>
      m = make_vote_msg pks (index caller) (sks caller) (svs caller)
    | _ => True
    end /\ MsgAssumption pks index sks svs calls
  | [] => True
  end.
```

Here `make_signup_msg` and `make_vote_msg` are the functions provided by the
smart contract and could potentially be extracted with the rest of the smart
contract to have functionally verified boardroom voting contract with privacy.

The BoardroomVoting smart contract is extracted to both
[Liquidity](boardroomVoting/BoardroomVotingExtractionLiquidity.v) and
[CameLIGO](boardroomVoting/BoardroomVotingExtractionCameLIGO.v).

## CIS1
A formalization of the [CIS1](https://proposals.concordium.software/CIS/cis-1.html) standard
for the Concordium blockchain. It includes a [specification](cis1/CIS1Spec.v) of the standard and a verified
[implementation](cis1/Cis1wccd.v) of the standard.

## Congress
In [Congress.v](../examples/congress/Congress.v) we implement the _Congress_ contract, a
simplified version of the DAO, which does complex dynamic interactions with the
blockchain and other contracts deployed on the blockchain. We specify and prove
a property about this contract at the end of this file. This property is
somewhat related to reentrancy in that it caps the number of transactions the
Congress will make. The formal statement reads as follows:

```coq
Corollary congress_txs_after_block
          {ChainBuilder : ChainBuilderType}
          prev new header acts :
  builder_add_block prev header acts = Some new ->
  forall addr,
    env_contracts new addr = Some (Congress.contract : WeakContract) ->
    length (outgoing_txs (builder_trace new) addr) <=
    num_acts_created_in_proposals (incoming_txs (builder_trace new) addr).
```

This is saying that, after adding a block, the number of transactions sent out
by any deployed Congress is capped by the number of actions that were created in
proposals up to this point. This is an approximation of the fact that any
outgoing transaction should correspond to some proposal created and discussed in
the past.

In [Congress_Buggy.v](../examples/congress/Congress_Buggy.v) we try the opposite: we take
the same contract as above, but introduce a reentrancy issue into it. We then
formally prove that this version of the Congress does _not_ satisfy the property
proven for the other version. This is proven by using one of our implementations
of our semantics and just asking Rocq to compute.

In [LocalBlockchainTests.v](../examples/congress/LocalBlockchainTests.v) we test that Rocq is
able to compute with the Congress by deploying it and interacting with it using
one of our implementations of blockchains. We also specialize the proof shown
about to our actual implementations of the execution layer described above.

We also use property-based testing to show that the buggy version is buggy.

## Counter
In [Counter.v](../examples/counter/Counter.v) we implement a simple counter contract that
serves as a tutorial on how one can use ConCert to develop and verify smart
contracts.

## Crowdfunding
An example of a deep embedding of a crowdfunding contract. We prove some of its functional
correctness properties using the corresponding shallow embedding.
The smart contract is extracted to CameLIGO and Liquidity.

## Dexter
This examples show a partial implementation of a token-asset exchange contract based on the
Tezos Dexter decentralized exchange. We show how the implementation is vulnerable using
property-based testing.

## Dexter 2
A formalization of the Dexter2 decentralized exchange. We prove correctness for the
two main smart contracts making up the exchange.

## EIP20
In [EIP20Token.v](../examples/eip20/EIP20Token.v) we implement the EIP 20 Token Specification (https://eips.ethereum.org/EIPS/eip-20).
EIP 20 is a standard interface for tokens - customizable assets for blockchains.
The implementation is tested, proven correct and extracted to Liquidity and CameLIGO.

## Escrow
In [Escrow.v](../examples/escrow/Escrow.v) we verify functional correctness of an escrow
contract based on the
[safe remote purchase](https://solidity.readthedocs.io/en/v0.6.1/solidity-by-example.html#safe-remote-purchase)
example in the Solidity documentation. This contract works by financially
incentivizing the participants to follow the protocol correctly, so it assumes
they are economically rational. This is done by requiring both the buyer and
seller to commit money to the contract that they will get back after the escrow
is done. The formal statement is:

```coq
Corollary escrow_correct
          {ChainBuilder : ChainBuilderType}
          prev new header acts :
  builder_add_block prev header acts = Some new ->
  let trace := builder_trace new in
  forall caddr,
    env_contracts new caddr = Some (Escrow.contract : WeakContract) ->
    exists (depinfo : DeploymentInfo Setup)
           (cstate : State)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state new caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      let item_worth := deployment_amount depinfo / 2 in
      let seller := deployment_from depinfo in
      let buyer := setup_buyer (deployment_setup depinfo) in
      is_escrow_finished cstate = true ->
      (buyer_confirmed inc_calls buyer = true /\
       net_balance_effect trace caddr seller = item_worth /\
       net_balance_effect trace caddr buyer = -item_worth \/

       buyer_confirmed inc_calls buyer = false /\
       net_balance_effect trace caddr seller = 0 /\
       net_balance_effect trace caddr buyer = 0).
```

The most important parts are the last lines which say that once the escrow is
finished (`is_escrow_finished`) then either
1. the buyer confirmed receiving the goods, in which case the seller has
   profited the item's worth and the buyer has lost the same, or
2. the buyer did not confirm receiving the goods, in which case neither party is
   affected.

Note that the second point above is for the case where the buyer never commits
any money to the escrow, in which case the seller is allowed to withdraw his own
commitment after a deadline.

## Exchange
An implementation of a buggy token-asset exchange contract inspired by UniSwap and Dexter.
The example includes property-based testing showing how the smart contract is vulnerable
to reentrancy and message ordering.

## FA1.2
A verified implementation of a Tezos FA1.2 token smart contract.

## FA2
Formalization of the Tezos FA2 token standard in ConCert.

## iToken
Implementation of core parts of the an old vulnerable version of the bZx iToken.
The example includes property-based testing showing how the smart contract is vulnerable.

## Piggybank
A verified implementation of a piggy bank smart contract.
The contract is based on the Concordium
[example](https://developer.concordium.software/en/mainnet/smart-contracts/tutorials/piggy-bank/writing.html#piggy-bank-writing).

## DSL Interpreter
Smart contract implementation of an interpreter for a stack based DSL.
The interpreter is extracted to Rust, Liquidity and CameLIGO.

## References
[1] McCorry, Patrick, Siamak F. Shahandashti, and Feng Hao. "A smart contract for
boardroom voting with maximum voter privacy." International Conference on
Financial Cryptography and Data Security. Springer, Cham, 2017.
