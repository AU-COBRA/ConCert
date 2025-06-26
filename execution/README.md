# Smart Contracts
This repo is a formalization of execution layers of modern blockchains in Rocq, along with property-based testing tools for testing smart contracts in ConCert.

## Structure of the project
The best place to start exploring the project is in
[Blockchain.v](theories/Blockchain.v). Here we define the basic types describing
blockchains, smart contracts and the semantics of the execution layer of
blockchains. We give proofs of some interesting general lemmata here as well,
for instance that undeployed contracts cannot have sent out any transactions.
We also provide a custom induction principle for proving properties involving
the executions layer. It helps to simplify proofs by reducing the boilerplate
code. See applications of the induction principle in the [example
contracts](../examples).

We also define a typeclass that captures what it means to satisfy our semantics.
We exhibit two instances of this typeclass in
[LocalBlockchain.v](test/LocalBlockchain.v); these are essentially
implementations of execution layers of modern blockchains. One is implemented
with depth-first execution and the other with breadth-first execution order.

In [Circulation.v](theories/Circulation.v) we prove a small sanity check for our
semantics. Specifically we prove that the total sum of the money in the system
is equal to the sum of the rewards handed out in blocks.

### Smart contract implementations

The [examples](../examples) folder contains various smart contracts along with
proofs of their properties, property-based testing and extraction of the smart contracts.

### Property-based Testing of Smart Contracts with QuickChick
Tests can be found in the [examples](../examples/) folder.
The [AllTests.v](../examples/AllTests.v) collects all property-based tests into one file.
Input generators for the contract under test can be found in files ending in 'Gens.v',
printers for the contracts can be found in files ending in 'Printers.v', and the QuickChick
properties/tests can be found in files ending in 'Tests.v'.
[TraceGens.v](test/TraceGens.v) contains key generator combinators for deriving "arbitrary"
input generators of blockchain execution traces for a given smart contract, along with
QuickChick `Checker`s that define the kind of properties we can test.
The simplest example is the [EIP20Tests](../examples/eip20/).
Here, we primarily test functional correctness of the EIP20 Token, namely the three properties:

```coq
balances_sum = state.(total_supply).

sum_allowances <= total_supply.

{msg_is_transfer}
  EIP20Token.receive
{post_transfer_balance_update_correct}
```
The first property states that the total supply of tokens is preserved by the `total_supply`
field of the contract's state. In our implementation, the contract has no way of minting
and burning tokens, so in this case `total_supply` is a constant.

The second property states that the combined allowances (as provided by the `approve`
endpoint of the token contract) cannot exceed the total number of tokens.

The third property is a hoare-triple on the `receive` function of the token contract,
stating that if there is an incoming `transfer` message, then the balances are updated
correct according to the `transfer` message. We also test a similar property for
`transfer_from` messages.

In [iTokenBuggy/iTokenBuggyTests.v](../examples/iTokenBuggy/iTokenBuggyTests.v) we test an
implementation which has a bug in the `transfer_from` method, similar to the one discovered
in the [iToken](https://bzx.network/blog/incident) contract. The bug allows an attacker to
create (mint) arbitrary tokens for themselves by performing self-transfers. When testing
this implementation against the first property above,
QuickChick reports a counterexample - an execution trace leading to a violation of the property.

The testing framework was developed as part of a Master's Thesis at Aarhus University, and
the thesis detailing (an earlier state of) the development can be found
[here](https://github.com/mikkelmilo/ConCert-QuickChick-Testing-Thesis).
