# ConCert

A framework for smart contract verification in Coq.

## How to build


Our development works with Coq 8.11.2. and depends on MetaCoq installed from source,
std++ and coq-bignums. The tests depend on QuickChick. Most of the dependencies can be installed through `opam`.

To set up a switch with the necessary dependencies run the following commands from the root of the project:

```bash
opam switch create . 4.07.1
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -j 4 coq.8.11.2 coq-bignums coq-stdpp.1.5.0 coq-quickchick
opam pin -j 4 add https://github.com/MetaCoq/metacoq.git#75f0cb9b8494cd0a856b77a664c662a59ddde447
```

After completing the procedures above, run `make` to build the development, and `make html` to build the documentation. 
The documentation will be located in the docs folder after `make html`.

## Dexter 2 formalisation

The [execution/examples/dexter2](execution/examples/dexter2/) folder contains implementation and proofs related to the Dexter 2 exchange.
The folder also contains a README file describing the contents.


## Structure of the project

Each folder contains a separate README file with more details.

The [embedding](embedding/) folder contains the development of the verified embedding of ``λsmart`` to Coq.

The [execution](execution/) folder contains the formalization of the smart
contract execution layer, which allows reasoning about, and property-based testing of, interacting contracts. The [tests](execution/tests) folder contains example tests. The key generators used for automatically generating blockchain execution traces for testing can be found in [TraceGens.v](execution/tests/TraceGens.v). The testing framework was developed as part of a Master's Thesis at Aarhus University, and the thesis detailing (an earlier state of) the development can be found [here](https://github.com/mikkelmilo/ConCert-QuickChick-Testing-Thesis).

The [extraction](extraction/) folder contains an implementation of the extraction pipeline based on MetaCoq's **verified erasure** extended with an erasure procedure for types.
It also features *certifying*(proof-generating) pre-processing steps and verified dead argument elimination.
Currently, we support smart contract languages Liquidity and CameLIGO, and general-purpose languages Elm and Rust as targets.
Pretty-printers to these languages are implemented directly in Coq.
One also can obtain an OCaml plugin for Coq by extracting our pipeline using the standard extraction of Coq (currently, it is possible for extraction to Rust).

## Documentation

We use the standard Coqdoc with improved styles and scripts of [CoqdocJS](https://github.com/tebbi/coqdocjs) ([license](extra/resources/coqdocjs/LICENSE)) and local table of contents by [TOC](https://github.com/jgallen23/toc)([license](extra/resources/toc/LICENSE)).

See the the `docs` folder for the documentation in the html format.
