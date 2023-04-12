# Extraction

Contains an implementation of extraction based on the certified erasure provided by MetaCoq. The
`theories` folder contains the implementation and correctness theorems. The [examples](../examples/) folder, as
the name suggests, contains examples of smart contracts and programs extracted using our development. The [tests](tests/) folder contains tests for our extensions to the certified erasure.

After building the project (running `make` from the project's root, or running `make` in this folder), the folders
`tests/extracted-code/*-extract/` are populated with the extracted code.

The extraction can be tested (compiled and run for the targets that have tests).
Use `make test-extraction` after the project is compiled.
Note that running this step locally requires additional compilers installed (see below).
Alternatively, the required compilers are available in the docker image `aucobra/concert:deps-coq-8.11-with-compilers`.

Compiling Liquidity code:
install the [Liquidity compiler](https://www.liquidity-lang.org/doc/installation/index.html).
Alternatively, the Liquidity code can be run using the online IDE: https://www.liquidity-lang.org/

Compiling Elm code:
install the [Elm compiler](https://guide.elm-lang.org/install/elm.html).
Running Elm tests also requires `elm-explorations/test` package (see the required dependencies in
`examples/elm-extract/elm.json`)

Compiling Rust code with the Concordium infrastructure:

* requires `cargo` and the Rust compiler;
* download `cargo-concordium`: https://developer.concordium.software/en/mainnet/net/installation/downloads.html#cargo-concordium
* add the directory with `cargo-concordium` to `PATH`;
* install `cargo`;
* use `cargo concordium test` to build and run tests (if tests are available);
* read the details here: https://developer.concordium.software/en/mainnet/smart-contracts/guides/setup-tools.html#setup-tools

## Extraction results

As part of the CI, the extraction results from the `tests/extracted-code/*-extract/` directories are compiled (and tested, for the targets with tests).
Moreover, the extracted source code is pushed to another repository https://github.com/AU-COBRA/extraction-results, so one can always browse through the code produced by the last successful build.

Some highlights from [theories](theories/):


* [ExAst.v](theories/ExAst.v) -- An extension of the MetaCoq's certified erasure EAst data-structures with additional information about erased types.
* [Erasure.v](theories/Erasure.v) -- An extension of the MetaCoq's certified erasure with erasure for types and erasing only required dependencies. Also implements erasure for global environments with extra typing information for global definitions.
* [ErasureCorrectness.v](theories/ErasureCorrectness.v) -- Correctness lemmas for definitions from [Erasure.v](theories/Erasure.v), proving that our erasure produces a well-formed erased environment.
* [Extraction.v](theories/Extraction.v) -- High-level interface to extraction. Provides different pipelines for doing extraction with different trusted computing bases.
* [ExtractionCorrectness.v](theories/ExtractionCorrectness.v) -- Top-level correctness theorem relating the stages.
* [Optimize.v](theories/Optimize.v) -- Optimizations (dead argument elimination, logical parameters elimination) on `λ□` terms.
* [OptimizeCorrectness.v](theories/OptimizeCorrectness.v) -- Correctness of optimization (dead argument elimination).
* [CertifyingEta.v](theories/CertifyingEta.v) -- An eta-expansion procedure.
* [CertifyingInlinig.v](theories/CertifyingInlinig.v) -- An inlining procedure.
* [CertifyingBeta.v](theories/ertifyingBeta.v) -- A procedure that finds an evalues redexes (if the reduction leads to new redexes, these are not reduced further)
* [Certifying.v](theories/Certifying.v) -- proof-generating procedure; it is used to generate proofs after running inlining/eta-expansion/etc.
* [LiquidityPretty.v](theories/LiquidityPretty.v) -- Pretty-printer for Liquidity from `λ□`.
* [Liquidity.v](theories/Liquidity.v) -- A pretty printer that works directly on the deep embedding of `λsmart` language.
* [LiquidityExtract.v](theories/LiquidityExtract.v) - A high-level interface to Liquidity extraction.
* [MidlangExtract.v](theories/MidlangExtract.v) -- A high-level interface to Midlang extraction including the pretty-printer to Midlang/Elm.
* [PrettyPrinterMonad.v](theories/PrettyPrinterMonad.v) -- A monad for implementing pretty-printing in Coq.


Some highlights of extracted examples:

* [CounterCertifiedLiquidity.v](../examples/counter/extraction/CounterCertifiedLiquidity.v) -- A simple counter contract.
* [CounterDepCertifiedLiquidity.v](../examples/counter/extraction/CounterDepCertifiedLiquidity.v) -- A counter contract that uses propositions to filter out the correct input. It also serves as an example application of the certifying eta-expansion.
* [CounterRefinementTypes](../examples/counter/extraction/CounterRefTypesMidlang.v) -- A counter contract that uses refinement types for expressing partial functional correctness.
* [CrowdfundingCertifiedExtraction.v](../examples/crowdfunding/CrowdfundingCertifiedExtraction.v) -- Machinery for extraction of a crowdfunding contract.
* [EscrowMidlang.v](../examples/escrow/extraction/EscrowMidlang.v) -- Extraction of the escrow contract defined in [Escrow.v](../examples/escrow/Escrow.v) to Midlang.
* [StackInterpreterExtract.v](../examples/stackInterpreter/StackInterpreterExtract.v) -- An interpreter for a simple stack-based language.
