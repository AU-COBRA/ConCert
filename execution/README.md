# Smart Contracts
This repo is a formalization of execution layers of modern blockchains in Coq.

## Structure of the project
The best place to start exploring the project is in
[Blockchain.v](theories/Blockchain.v). Here we define the basic types describing
blockchains, smart contracts and the semantics of the execution layer of
blockchains. We give proofs of some interesting general lemmata here as well,
for instances that undeployed contracts cannot have sent out any transactions.

We also define a typeclass that captures what it means to satisfy our semantics.
We exhibit two instances of this typeclass in
[LocalBlockchain.v](theories/LocalBlockchain.v); these are essentially
implementations of execution layers of modern blockchains. One is implemented
with depth-first execution and the other with breadth-first execution order.

In [Congress.v](theories/Congress.v) we implement the _Congress_ contract, a
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

In [Congress_Buggy.v](theories/Congress_Buggy.v) we try the opposite: we take
the same contract as above, but introduce a reentrancy issue into it. We then
formally prove that this version of the Congress does _not_ satisfy the property
proven for the other version. This is proven by using one of our implementations
of our semantics and just asking Coq to compute.

In [Escrow.v](theories/Escrow.v) we verify functional correctness of an escrow
contract based on the
[safe remote purchase](https://solidity.readthedocs.io/en/v0.6.1/solidity-by-example.html#safe-remote-purchase)
example in the Solidity documentation. This contract works by financially
incentivising the participants to follow the protocol correctly, so it assumes
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

In [Circulation.v](theories/Circulation.v) we prove a small sanity check for our
semantics. Specifically we prove that the total sum of the money in the system
is equal to the sum of the rewards handed out in blocks.

In [LocalBlockchainTests.v](theories/LocalBlockchainTests.v) we test that Coq is
able to compute with the Congress by deploying it and interacting with it using
one of our implementations of blockchains. We also specialize the proof shown
about to our actual implementations of the execution layer described above.

## Building/Developing
This project uses the std++ library. This must be installed first and can be
installed via Opam, after adding the dev repo of Iris:
```bash
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp
```
For more instructions, see [the stdpp readme](https://gitlab.mpi-sws.org/iris/stdpp).

After stdpp is installed, this project should build with
```bash
make
```
