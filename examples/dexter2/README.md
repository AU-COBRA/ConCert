# Dexter 2

Formalisation of the Dexter 2 decentralised exchange based on the informal spec https://gitlab.com/dexter2tz/dexter2tz/-/tree/1713941489e0e646b632b42017a041c59158b6fb/docs/informal-spec

The development consists of the following parts.

## Dexter 2 Liquidity Token

This contract is an extension of a basic FA1.2 token contract with an extra entrypoint that allows an admin to mint and burn tokens.
The purpose of this contract is to keep track of ownership of the exchanges funds.

[Dexter2FA12.v](Dexter2FA12.v) contains the implementation of the token.

[Dexter2FA12Correct.v](Dexter2FA12Correct.v) contains proofs of functional correctness properties and proofs of invariants required for inter-contract communication proofs.

## Dexter 2 CPMM

This contract is an implementation of a Constant Product Market Maker (CPMM), the main Dexter 2 functionality.

[Dexter2CPMM.v](Dexter2CPMM.v) contains the implementation of the exchange.

[Dexter2CPMMCorrect.v](Dexter2CPMMCorrect.v) contains proofs of functional correctness properties and proofs of inter-contract invariants.

# Code extraction to CameLIGO

See the extraction setup for [CPMM](Dexter2CPMMExtractLIGO.v) and [Liquidity Token](Dexter2FA12ExtractLIGO.v)

Main Contract code [extracted/dexter2CPMM.mligo](extracted/dexter2CPMM.mligo)

Liquidity Token code [extracted/dexter2Lqt.mligo](extracted/dexter2Lqt.mligo)

# Property-based Testing
This folder also contains some property-based tests for the Dexter2 decentralized exchange.
The tests can be found in [Dexter2Tests.v](Dexter2Tests.v).
Generators for the contract are located in [Dexter2Gens.v](Dexter2Gens.v).
