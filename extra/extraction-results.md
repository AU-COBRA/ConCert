# ConCert Extraction Results
This repository contains source code of programs extracted from Coq using the [ConCert](https://github.com/AU-COBRA/ConCert) framework.

The programs were written in Coq, verified and extracted to several languages using verified code extraction.
The original programs can be found [here](https://github.com/AU-COBRA/ConCert/tree/master/examples).

## Structure of the project
Each folder contain extracted programs for a specific language.

* [cameligo-extract](cameligo-extract/tests) contains smart contracts extracted to the CameLIGO smart contract language for the Tezos blockchain.
* [concordium-extract](concordium-extract) contains smart contracts extracted to the smart contract language for the Concordium blockchain.
* [elm-extract](elm-extract/tests) contains test programs extracted to Elm.
* [elm-wev-extract](elm-web-extract/src) contains a simple web application extracted to Elm.
* [liquidity-extract](liquidity-extract/tests) contains smart contracts extracted to the Liquidity smart contract language for the Dune blockchain.
* [midlang-extract](midlang-extract/tests) contains smart contracts extracted to the Midlang smart contract language.
* [rust-extract](rust-extract) contains programs extracted to Rust.
