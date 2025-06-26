# Extraction

Contains an implementation of extraction based on the certified erasure provided by MetaRocq.
The `theories` folder contains the implementation and correctness theorems.
The [examples](../examples/) folder, as the name suggests, contains examples of smart contracts
and programs extracted using our development. The [tests](tests/) folder contains tests for
our extensions to the certified erasure.

The extraction framework currently supports four languages: CameLIGO, Liquidity, Rust and Elm.

Rust and Elm extraction have been moved to https://github.com/AU-COBRA/coq-rust-extraction and
https://github.com/AU-COBRA/coq-elm-extraction

## Extracting and compiling code

After building the project (running `make` from the project's root, or running `make` in this folder),
the folders `tests/extracted-code/*-extract/` are populated with the extracted code.

The extraction can be tested (compiled and run for the targets that have tests).
Use `make test-extraction` after the project is compiled.
Note that running this step locally requires additional compilers installed (see below).
Alternatively, the required compilers are available in the docker image
[`aucobra/concert:deps-8.16.1-with-compilers`](https://hub.docker.com/r/aucobra/concert/tags).

### Compiling LIGO code:
Install the [LIGO compiler](https://ligolang.org/docs/intro/installation?lang=cameligo).
The extraction pipeline is tested to work with v0.59.0 and targets the Kathmandu protocol.

### Compiling Liquidity code:

Install the [Liquidity compiler](https://www.liquidity-lang.org/doc/installation/index.html).
Alternatively, the Liquidity code can be run using the online IDE: https://www.liquidity-lang.org/

### Compiling Elm code:

Install the [Elm compiler](https://guide.elm-lang.org/install/elm.html).
Running Elm tests also requires `elm-explorations/test` package (see the required dependencies in
[`elm.json`](https://github.com/AU-COBRA/coq-elm-extraction/blob/master/tests/extracted-code/elm-extract/elm.json)).

### Compiling Rust code with the Concordium infrastructure:

* requires `cargo` and the Rust compiler;
* download `cargo-concordium`: https://developer.concordium.software/en/mainnet/net/installation/downloads.html#cargo-concordium
* add the directory with `cargo-concordium` to `PATH`;
* install `cargo`;
* use `cargo concordium test` to build and run tests (if tests are available);
* read the details here: https://developer.concordium.software/en/mainnet/smart-contracts/guides/setup-tools.html#setup-tools

## Extraction results

As part of the CI, the extraction results from the `tests/extracted-code/*-extract/` directories
are compiled (and tested, for the targets with tests).
Moreover, the extracted source code is pushed to another repository (https://github.com/AU-COBRA/extraction-results),
so one can always browse through the code produced by the last successful build.

## Extracted Smart Contracts

| Contract\Language                                                    | Liquidity (Dune)                                                               | CameLIGO (Tezos)                                                       | Rust (Concordium)                                                 | MidLang                                                        |
|----------------------------------------------------------------------|--------------------------------------------------------------------------------|------------------------------------------------------------------------|-------------------------------------------------------------------|----------------------------------------------------------------|
| [Counter (simple types)](../examples/counter/)                       | [yes](../examples/counter/extraction/CounterCertifiedLiquidity.v)              | [yes](../examples/counter/extraction/CounterLIGO.v)                    | [yes](../examples/counter/extraction/CounterRust.v)               |                                                                |
| [Counter (subset types)](../examples/counter/)                       | [yes](../examples/counter/extraction/CounterSubsetTypesLiquidity.v)            | [yes](../examples/counter/extraction/CounterSubsetTypesLIGO.v)**       |                                                                   | [yes](../examples/counter/extraction/CounterRefTypesMidlang.v) |
| [Counter (Prop)](../examples/counter/)                               | [yes](../examples/counter/extraction/CounterDepCertifiedLiquidity.v)           |                                                                        |                                                                   |                                                                |
| [ERC20 token](../examples/eip20/EIP20Token.v)                        | [yes](../examples/eip20/EIP20LiquidityExtraction.v)                            | [yes](../examples/eip20/EIP20CameLIGOExtraction.v)                     | in progress***                                                    |                                                                |
| [Crowdfunding](../examples/crowdfunding/Crowdfunding.v)              | [yes](../examples/crowdfunding/CrowdfundingLiquidity.v)                        | [yes](../examples/crowdfunding/CrowdfundingCameLIGO.v)                 |                                                                   |                                                                |
| [DSL Interpreter](../examples/stackInterpreter/StackInterpreter.v)   | [yes](../examples/stackInterpreter/StackInterpreterLiquidityExtract.v)         | [yes](../examples/stackInterpreter/StackInterpreterLIGOExtract.v)      | [yes](../examples/stackInterpreter/StackInterpreterRustExtract.v) |                                                                |
| [Escrow](../examples/escrow/Escrow.v)                                | [yes](../examples/escrow/extraction/EscrowLiquidity.v)                         | [yes](../examples/escrow/extraction/EscrowLIGO.v)                      | [yes](../examples/escrow/extraction/EscrowRust.v)                 | [yes](../examples/escrow/extraction/EscrowMidlang.v)           |
| [Boardroom voting](../examples/boardroomVoting/BoardroomVoting.v)    | [partially](../examples/boardroomVoting/BoardroomVotingExtractionLiquidity.v)* | [yes](../examples/boardroomVoting/BoardroomVotingExtractionCameLIGO.v) |                                                                   |                                                                |
| [Dexter2 CPMM (main)](../examples/dexter2/Dexter2CPMM.v)             |                                                                                | [yes](../examples/dexter2/Dexter2CPMMExtractLIGO.v)                    | not yet****                                                       |                                                                |
| [Dexter2 FA1.2 (liquidity token)](../examples/dexter2/Dexter2FA12.v) |                                                                                | [yes](../examples/dexter2/Dexter2FA12ExtractLIGO.v)                    | not yet****                                                       |                                                                |

\*issue with typing of lambdas in liquidity (see https://github.com/OCamlPro/liquidity/issues/264).

\**[resolved] the issue with parametric types when extracting `sig` is resolved after the support for polymorphism was added to LIGO.

\***issue with maps of maps (the values can be only by-reference, and this causes problems).

\**** extracting the contracts should be doable, no map of maps issue as with ERC20. However, remapping of contract calls should be addressed, so far all the contracts extracted to Rust emit transfers only.

Some highlights of extracted examples:

* [CounterCertifiedLiquidity.v](../examples/counter/extraction/CounterCertifiedLiquidity.v)
  -- A simple counter contract.
* [CounterDepCertifiedLiquidity.v](../examples/counter/extraction/CounterDepCertifiedLiquidity.v)
  -- A counter contract that uses propositions to filter out the correct input. It also serves as an example application of the certifying eta-expansion.
* [CounterRefinementTypes](../examples/counter/extraction/CounterRefTypesMidlang.v)
  -- A counter contract that uses refinement types for expressing partial functional correctness.
* [CrowdfundingCertifiedExtraction.v](../examples/crowdfunding/CrowdfundingCameLIGO.v)
  -- Machinery for extraction of a crowdfunding contract.
* [EscrowMidlang.v](../examples/escrow/extraction/EscrowMidlang.v)
  -- Extraction of the escrow contract defined in [Escrow.v](../examples/escrow/Escrow.v) to Midlang.
* [StackInterpreterExtract.v](../examples/stackInterpreter/StackInterpreterRustExtract.v)
  -- An interpreter for a simple stack-based language.

## Project structure

Part of the extraction pipeline have been moved to the MetaRocq project.
The moved files are described here:

* [ExAst.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/ExAst.v)
  -- An extension of the MetaRocq's certified erasure EAst data-structures with additional
  information about erased types.
* [Erasure.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/Erasure.v)
  -- An extension of the MetaRocq's certified erasure with erasure for types and erasing only
  required dependencies. Also implements erasure for global environments with extra typing
  information for global definitions.
* [ErasureCorrectness.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/ErasureCorrectness.v)
  -- Correctness lemmas for definitions from
  [Erasure.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/Erasure.v),
  proving that our erasure produces a well-formed erased environment.
* [Extraction.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/Extraction.v)
  -- High-level interface to extraction. Provides different pipelines for doing extraction
  with different trusted computing bases.
* [ExtractionCorrectness.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/ExtractionCorrectness.v)
  -- Top-level correctness theorem relating the stages.
* [Optimize.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/Optimize.v)
  -- Optimizations (dead argument elimination, logical parameter elimination) on `λ□` terms.
* [OptimizeCorrectness.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/OptimizeCorrectness.v)
  -- Correctness of optimization (dead argument elimination).
* [CertifyingEta.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/CertifyingEta.v)
  -- An eta-expansion procedure.
* [CertifyingInlinig.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/CertifyingInlining.v)
  -- An inlining procedure.
* [CertifyingBeta.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/CertifyingBeta.v)
  -- A procedure that finds an evaluates redexes (if the reduction leads to new redexes, these are not reduced further)
* [Certifying.v](https://github.com/MetaRocq/metarocq/tree/coq-8.16/erasure/theories/Typed/Certifying.v)
  -- proof-generating procedure; it is used to generate proofs after running inlining/eta-expansion/etc.

The remaining of the project consists of

* [LiquidityPretty.v](theories/LiquidityPretty.v) -- Pretty-printer for Liquidity from `λ□`.
* [LiquidityExtract.v](theories/LiquidityExtract.v) -- A high-level interface to Liquidity extraction.
* [CameLIGOPretty.v](theories/CameLIGOPretty.v) -- Pretty-printer for CameLIGO from `λ□`.
* [CameLIGOExtract.v](theories/CameLIGOExtract.v) -- A high-level interface to CameLIGO extraction.
* [ConcordiumExtract.v](theories/ConcordiumExtract.v) -- A high-level interface to Concordium extraction.
* [PrettyPrinterMonad.v](theories/PrettyPrinterMonad.v) -- A monad for implementing pretty-printing in Rocq.
