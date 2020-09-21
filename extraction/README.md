# Extraction

Contains an implementation of extraction based on the certified erasure provided by MetaCoq. The
`theories` folder contains the implementation and correctness theorems.  The `examples` folder, as
the name suggests, contains examples of smart contracts and programs extracted using our development
and tests for our extensions to the certified erasure.

After building the project (running `make` from the project's root), the folders
`liquidity-extract/tests` and `elm-extract/tests` are populated with the extracted code. 

Compiling Liquidity code:
install the [Liquiditycompiler](https://www.liquidity-lang.org/doc/installation/index.html). Be
aware of some issues while installing Liquidity: https://github.com/OCamlPro/liquidity/issues/254.
Alternatively, the Liquidity code can be run using the online IDE: https://www.liquidity-lang.org/

Compiling Elm code:
install the [Elm compiler] (https://guide.elm-lang.org/install/elm.html).
Running Elm tests also requires `elm-explorations/test` package (see the required dependencies in
`elm-extract/elm.json`)

Some highlights from `theories`:


* `theories/ExAst.v` -- An extension of the MetaCoq's certified erasure EAst data-structures with additional information about erased types. 
* `theories/Erasure.v` -- An extension of the MetaCoq's certified erasure with erasure for types. Also implements erasure for global environments with extra typing information for global definitions.
* `theories/ExTyping.v` -- Well-formedness of erased terms and erased global environments.
* `theories/ErasureCorrectness.v` -- Correctness lemmas for definition from `Erasure.v`.
* `theories/MetaCoqErasureCorrectnessStrong.v` -- A strengthened version of the correctness proof from MetaCoq (erasing dependencies only, not the full environment).
* `theories/Extraction.v` -- High-level interface to extraction. Provides different pipelines for doing extraction with different trusted computing bases.
* `theories/ExtractionCorrectness.v` -- Top-level correctness theorem relating the stages.
* `theories/Optimize.v` -- Optimisations (dead argument elimination, logical parameters elimination) on `λ□` terms.
* `theories/OptimizeCorrectness.v` -- Correctness of optimisation (dead argument elimination).
* `theories/CertifyingEta.v` -- A eta-expansion procedure which generated proofs of equality of between the result and the original.
* `theories/LPretty.v` -- Pretty-printer for Liquidity from `λ□`.
* `theories/Liquidity.v` -- A pretty printer that works directly on the deep embedding of `λsmart` language.
* `theories/LiquidityExtract.v` - A high-level interface to Liquidity extraction.
* `theories/MidlangExtract.v` -- A high-level interface to Midlang extraction, incudes a pretty-printed and some examples.
* `theories/PrettyPrinterMonad.v` -- A monad for implementing pretty-printing in Coq.
* `theories/WcbvEvalType.v` -- Big-step cbv realtion of MetaCoq valued in `Type` instead of `Prop`. Eventually will be removed, once MetaCoq relation is updated.


Some highlights from `examples`:

* `examples/CounterCertifiedExtraction.v` -- A simple counter contract.
* `examples/CounterDepCertifiedExtraction.v` -- A counter contract that uses propositions to filter out the correct input. It also serves as an example appication of the certifying eta-expansion.
* `examples/CounterRefinementTypes.v` -- A counter contract that uses refinement types for expressing partial functional correctness.
* `examples/CrowdfundingCertifiedExtraction.v` -- Machinery for extraction of a crowdfunding contract (defined in `examples/crowdfunding_extract/Crowdfunding.v`).
* `examples/ElmExtractTests.v` -- Several examples of extraction into Elm.
* `examples/StackInterpreter.v` -- An interpreter for a simple stack-based language.
