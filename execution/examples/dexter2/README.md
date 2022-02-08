# Dexter 2

Formalisation of the Dexter 2 decentralised exchange based on the informal spec https://gitlab.com/dexter2tz/dexter2tz/-/tree/master/docs/informal-spec

The development consists of the following parts.

## Dexter 2 Liquidity Token

This contract is an extension of a basic FA1.2 token contract with an extra entrypoint that allows an admin to mint and burn tokens.
The purpose of this contract is to keep track of ownership of the exchanges funds.

[Dexter2FA12.v](Dexter2FA12.v) contains the implementation of the token, proofs of functional correctness properties and proofs of invariants required for inter-contract communication proofs.

## Dexter 2 CPMM

This contract is an implementation of a Constant Product Market Maker (CPMM), the main Dexter 2 functionality.

[Dexter2CPMM.v](Dexter2CPMM.v) contains the implementation along with the proofs of functional correctness properties and proofs of inter-contract invariants.

Important lemmas:

* `contract_balance_correct` - XTZ pool correct (`xtzPool` should always be equal to the actual XTZ held by the main contract)

* `transfer_bound` - Transfers valid (the contract never attempts to transfer more XTZ than it holds).

* `lqt_pool_correct_interface` - Liquidity total correct (`lqtTotal` of the main contract is equal to `total_supply` of the liquidity token). Proved for any liquidity token that satisfies the `LqtTokenInterface`)

* `lqt_pool_correct_lqt_fa12` - Liquidity total correct for the our verified implementation of the liquidity token given in [Dexter2FA12.v](Dexter2FA12.v).

# Inter-contract communication reasoning

Lemmas and tactics for [reasoning about communicating contracts](../../theories/InterContractCommunication.v)

# Code extraction to CameLIGO

See [the extraction setup](../../../extraction/examples/Dexter2Extract.v)

