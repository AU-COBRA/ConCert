# Extraction

The content of this folder corresponds to Section 3 of the paper. See more references below starting
with the prefix "PAPER:"

Contains an implementation of extraction based on the certified erasure provided by MetaCoq. The
`theories` folder contains the implementation and correctness theorems.  The `examples` folder, as
the name suggests, contains examples of smart contracts and programs extracted using our development
and tests for our extensions to the certified erasure.

After building the project (running `make` from the project's root), the folders
`examples/liquidity-extract/tests`, `examples/elm-extract/tests` and
`examples/midlang-extract/tests` are populated with the extracted code.

Compiling Liquidity code: install the [Liquidity compiler](https://www.liquidity-lang.org/doc/installation/index.html).
Follow the instructions, but pin the version of `ocaml-migrate-parsetree` to 1.5.5. Alternatively,
the Liquidity code can be run using the online IDE: https://www.liquidity-lang.org/

Compiling Elm code: install the [Elm compiler](https://guide.elm-lang.org/install/elm.html).
Running Elm tests also requires `elm-explorations/test` package (see the required dependencies in
`examples/elm-extract/elm.json`)

Midlang code: unfortunately the Midlang compiler is not publicly available. The generated code has
been compiled with the private version of the Midlang compiler for the testing purposes.

Some highlights from `theories`:

* `theories/ExAst.v` -- An extension of the MetaCoq's certified erasure EAst data-structures
      with additional information about erased types.
* `theories/Erasure.v` -- An extension of the MetaCoq's certified erasure with erasure for types and
      erasing only required dependencies. Also implements erasure for global environments with extra
      typing information for global definitions
      (PAPER: Section 3.1/Erasure for types).
* `theories/ErasureCorrectness.v` -- Correctness lemmas for definitions from `Erasure.v`, proving
      that our erasure produces a well-formed erased environment.
* `theories/MetaCoqErasureCorrectnessStrong.v` -- A strengthened version of the correctness proof
      from MetaCoq (erasing dependencies only, not the full environment).
* `theories/Extraction.v` -- High-level interface to extraction. Provides different pipelines for
      doing extraction with different trusted computing bases.
* `theories/ExtractionCorrectness.v` -- Top-level correctness theorem relating the stages
      (PAPER: Theorem 2 (Soundness of extraction)).
* `theories/Optimize.v` -- Optimisations (dead argument elimination, logical parameters elimination)
      on `λ□` terms (PAPER: Section 3.1/Optimisations).
* `theories/OptimizeCorrectness.v` -- Correctness of optimisation (dead argument elimination)
      (PAPER: Theorem 1 (Soundness of dearging)).
* `theories/CertifyingEta.v` -- A eta-expansion procedure which generated proofs of equality of
      between the result and the original.
* `theories/LPretty.v` -- Pretty-printer for Liquidity from `λ□` (PAPER: Section 3.2).
* `theories/Liquidity.v` -- A pretty printer that works directly on the deep embedding of `λsmart`
      language.
* `theories/LiquidityExtract.v` - A high-level interface to Liquidity extraction (PAPER: Section 3.2).
* `theories/MidlangExtract.v` -- A high-level interface to Midlang extraction including the
      pretty-printer to Midlang/Elm (PAPER: Section 3.3).
* `theories/PrettyPrinterMonad.v` -- A monad for implementing pretty-printing in Coq.
* `theories/WcbvEvalType.v` -- Big-step cbv relation of MetaCoq valued in `Type` instead of
      `Prop`. Used purely as an intermediate step for some proofs and not in the top level statements.


Some highlights from `examples`:

* `examples/CounterCertifiedExtraction.v` -- A simple counter contract.
* `examples/CounterDepCertifiedExtraction.v` -- A counter contract that uses propositions to filter
      out the correct input. It also serves as an example application of the certifying eta-expansion.
* `examples/CounterRefinementTypes.v` -- A counter contract that uses refinement types for
      expressing partial functional correctness, extracts to Liquidity
      (PAPER: implementation shown in Figure 2, extracted code: Figure 3a).
* `examples/CrowdfundingCertifiedExtraction.v` -- Machinery for extraction of a crowdfunding
      contract (defined in `examples/crowdfunding_extract/Crowdfunding.v`).
* `examples/ElmExtractTests.v` -- Several examples of extraction into Elm
    (PAPER: examples mentioned in Section 3.3).
* `examples/MidlangCounterRefTypes.v` -- extraction of a counter contract with refinement types to
      Midlang (PAPER: implementation shown in Figure 2, extracted code: Figure 3b).
* `examples/MidlangEscrow.v` -- Extraction of the Escrow contract, which was tested and verified in
      ConCert (implementation is available in
      [../execution/examples/Escrow.v](../execution/examples/Escrow.v))
* `examples/StackInterpreter.v` -- An interpreter for a simple stack-based language
    (PAPER: example mentioned in Section 3.2).
