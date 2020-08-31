# ConCert

A framework for smart contract verification in Coq.

The work on this fork is aimed at building infrastructure for random property testing of the Smart Contracts (and the execution environment) using QuickChick.

## How to build


Our development works with Coq 8.11. and depends on MetaCoq 1.0,
std++ and coq-bignums. The tests depend on QuickChick. These dependencies can be installed through `opam`.

Install Coq (see https://coq.inria.fr/opam-using.html for detailed instructions on how to manage
multiple Coq installations using opam).:

```bash
opam install coq.8.11
```

Then dependencies:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-metacoq.1.0~alpha2+8.11
opam install coq-bignums
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp
opam install coq-quickchick
```

After completing the procedures above, run `make` to build the development, and
`make html` to build the documentation. The documentation will be located in the
docs folder after `make html`.

## Structure of the project

The [embedding](embedding/) folder contains the development of the embedding.

The [execution](execution/) folder contains the formalization of the smart
contract execution layer, which allows reasoning about, and property-based testing of, interacting contracts. The [tests](execution/tests) folder contains example tests. The key generators used for automatically generating blockchain execution traces for testing can be found in [TraceGens.v](execution/tests/TraceGens.v). The testing framework was developed as part of a Master's Thesis at Aarhus University, and the thesis detailing the development can be found [here](https://github.com/mikkelmilo/ConCert-QuickChick-Testing-Thesis).

The [extraction](extraction/) folder contains a printing procedure for the deep embedding into the Liquidity syntax. For extraction using MetaCoq's **certified erasure** see the [extract-cert](https://github.com/AU-COBRA/ConCert/tree/extract-cert) branch (requires [MetaCoq's fork](https://github.com/annenkov/template-coq/tree/coq-8.11-erase-annotated) to compile).


## Notes for developers

The [execution](execution/) subproject can be built independently via running `make` in the `execution` folder. This also means that the `_CoqProject` file inside the `execution` folder must be manually kept in sync with the main `_CoqProject` in the root.
