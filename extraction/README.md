# Extraction

Contains an implementation of extraction based on the certified erasure provided by MetaCoq. The
`theories` folder contains the implementation and correctness theorems.  The `examples` folder, as
the name suggests, contains examples of smart contracts and programs extracted using our development
and tests for our extensions to the certified erasure.

After building the project (running `make` from the project's root), the folders
`examples/*-extract/` are populated with the extracted code.

The extraction can be tested (compiled and run for the targets that has tests).
Use `make test-extraction` after the project is compiled.
Note that running this step requires additional compilers installed (see below).

Compiling Liquidity code:
install the [Liquidity compiler](https://www.liquidity-lang.org/doc/installation/index.html).
Alternatively, the Liquidity code can be run using the online IDE: https://www.liquidity-lang.org/

Compiling Elm code:
install the [Elm compiler](https://guide.elm-lang.org/install/elm.html).
Running Elm tests also requires `elm-explorations/test` package (see the required dependencies in
`examples/elm-extract/elm.json`)

Compiling Rust code with the Concordium infrastructure:

* requres `cargo` and the Rust compiler;
* download `cargo-concordium`: http://developer.concordium.software/en/mainnet/net/installation/downloads.html#cargo-concordium
* add the directory with `cargo-concordium` to `PATH`;
* install `cargo`;
* use `cargo concordium build`;
* read the details here: http://developer.concordium.software/en/mainnet/smart-contracts/guides/setup-tools.html#setup-tools

Some highlights from `theories`:


* `theories/ExAst.v` -- An extension of the MetaCoq's certified erasure EAst data-structures with additional information about erased types.
* `theories/Erasure.v` -- An extension of the MetaCoq's certified erasure with erasure for types and erasing only required dependencies. Also implements erasure for global environments with extra typing information for global definitions.
* `theories/ErasureCorrectness.v` -- Correctness lemmas for definitions from `Erasure.v`, proving that our erasure produces a well-formed erased environment.
* `theories/Extraction.v` -- High-level interface to extraction. Provides different pipelines for doing extraction with different trusted computing bases.
* `theories/ExtractionCorrectness.v` -- Top-level correctness theorem relating the stages.
* `theories/Optimize.v` -- Optimisations (dead argument elimination, logical parameters elimination) on `λ□` terms.
* `theories/OptimizeCorrectness.v` -- Correctness of optimisation (dead argument elimination).
* `theories/CertifyingEta.v` -- An eta-expansion procedure.
* `theories/CertifyingInlinig.v` -- An inlining procedure.
* `theories/CertifyingBeta.v` -- A procedure that finds an evalues redexes (if the reduction leads to new redexes, these are not reduced further)
* `theories/Certifying.v` -- proof-generating procedure; it is used to generate proofs after running inlining/eta-expansion/etc.
* `theories/LPretty.v` -- Pretty-printer for Liquidity from `λ□`.
* `theories/Liquidity.v` -- A pretty printer that works directly on the deep embedding of `λsmart` language.
* `theories/LiquidityExtract.v` - A high-level interface to Liquidity extraction.
* `theories/MidlangExtract.v` -- A high-level interface to Midlang extraction including the pretty-printer to Midlang/Elm.
* `theories/PrettyPrinterMonad.v` -- A monad for implementing pretty-printing in Coq.


Some highlights from `examples`:

* `examples/CounterCertifiedExtraction.v` -- A simple counter contract.
* `examples/CounterDepCertifiedExtraction.v` -- A counter contract that uses propositions to filter out the correct input. It also serves as an example application of the certifying eta-expansion.
* `examples/CounterRefinementTypes.v` -- A counter contract that uses refinement types for expressing partial functional correctness.
* `examples/CrowdfundingCertifiedExtraction.v` -- Machinery for extraction of a crowdfunding contract (defined in `examples/crowdfunding_extract/Crowdfunding.v`).
* `examples/ElmExtractTests.v` -- Several examples of extraction into Elm.
* `examples/MidlangEscrow.v` -- Extraction of the escrow contract defined in [../execution/examples/Escrow.v](../execution/examples/Escrow.v) to Midlang.
* `examples/StackInterpreter.v` -- An interpreter for a simple stack-based language.
