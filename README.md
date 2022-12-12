# Dexter 2 formalisation in ConCert

The development is also available in an anonymised git repository: https://anonymous.4open.science/r/CCS-Dexter2/

## How to build


Our development works with Coq 8.16. and depends on MetaCoq,
std++ and coq-bignums. The tests depend on QuickChick. The dependencies can be installed through `opam`.

To set up a switch with the necessary dependencies run the following commands:

```bash
git clone https://github.com/AU-COBRA/ConCert.git
cd ConCert
git submodule init
git submodule update
opam switch create . 4.10.2 --repositories default,coq-released=https://coq.inria.fr/opam/released --deps-only
eval $(opam env)
```

After completing the procedures above, run `make` to build the development, and `make html` to build the documentation. 
The documentation will be located in the docs folder after `make html`.

## Dexter 2 formalisation

The `execution/examples/dexter2` folder contains implementation and proofs related to the Dexter 2 exchange.
The folder also contains a [README](examples/dexter2/README.md) file describing the contents.


## Structure of the project

Each folder contains a separate README file with more details.

The [embedding](embedding/) folder contains the development of the verified embedding of ``λsmart`` to Coq.

The [execution](execution/) folder contains the formalization of the smart
contract execution layer, which allows reasoning about, and property-based testing of, interacting contracts. The [test](execution/test) folder contains the property-based testing framework. The key generators used for automatically generating blockchain execution traces for testing can be found in [TraceGens.v](execution/test/TraceGens.v). The testing framework was developed as part of a Master's Thesis at Aarhus University, and the thesis detailing (an earlier state of) the development can be found [here](https://github.com/mikkelmilo/ConCert-QuickChick-Testing-Thesis).

The [typed-extraction](https://github.com/AU-COBRA/typed-extraction) submodule contains an implementation of the extraction pipeline based on MetaCoq's **verified erasure** extended with an erasure procedure for types.
It also features *certifying*(proof-generating) pre-processing steps and verified dead argument elimination.

The [extraction](extraction/) folder contains an extraction pipeline for smart contract languages.
Currently, we support smart contract languages Liquidity and CameLIGO, and general-purpose languages Elm and Rust as targets.
Pretty-printers to these languages are implemented directly in Coq.
One also can obtain an OCaml plugin for Coq by extracting our pipeline using the standard extraction of Coq (currently, it is possible for extraction to Rust).

The [examples](examples/) folder contains examples of smart contract implementations, embedding, extraction, and tests. Extracted smart contracts can be found [here](https://github.com/AU-COBRA/extraction-results).

## Documentation

We use the standard Coqdoc with improved styles and scripts of [CoqdocJS](https://github.com/tebbi/coqdocjs) ([license](extra/resources/coqdocjs/LICENSE)) and local table of contents by [TOC](https://github.com/jgallen23/toc)([license](extra/resources/toc/LICENSE)).

See the the `docs` folder for the documentation in the html format.
