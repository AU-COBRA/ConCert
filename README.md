# ConCert

A framework for smart contract verification in Coq.

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
opam install coq-bignums
opam install coq-stdpp
opam install coq-quickchick
```

Install MetaCoq's coq-8.11 branch from source. The simplest way is to clone the MetaCoq repo, check out [this](https://github.com/MetaCoq/metacoq/commit/df8ef08832d4b30f1b354a8e751cdaf154d0b9a0) commit by running `git checkout df8ef08832d4b30f1b354a8e751cdaf154d0b9a0` in the cloned folder, and then run `opam install <path to MetaCoq>`.
For more instructions, see the [official MetaCoq repo](https://github.com/MetaCoq/metacoq#installing-from-github-repository-for-developers).

After completing the procedures above, run `make` to build the development, and
`make html` to build the documentation. The documentation will be located in the
docs folder after `make html`.

To test the code produced by our extraction run `make test-extraction`. 
However, this command requires [Elm compiler](https://guide.elm-lang.org/install/elm.html) and
[Liquidity compiler](https://www.liquidity-lang.org/doc/installation/index.html) 
(follow the instructions, but pin the version of `ocaml-migrate-parsetree` to 1.5.5).

## Structure of the project

See notes with "PAPER:" prefix referencing to the corresponding sections/definitions in the paper.

The [embedding](embedding/) folder contains the development of the embedding.

The [execution](execution/) folder contains the formalization of the smart contract execution layer, which allows reasoning about, and property-based testing of, interacting contracts. Contains a README file with the details of the execution layer structure.

The [execution/examples](execution/examples) folder contains implementations of and theorems about smart contracts. 
It includes the [Escrow](execution/examples/Escrow.v) contract (PAPER: Section 4) and the [Boardroom voting](execution/examples/BoardroomVoting.v) contract (PAPER: Section 5)

The [execution/tests](execution/tests) folder contains example tests. The key generators used for automatically generating blockchain execution traces for testing can be found in [TraceGens.v](execution/tests/TraceGens.v). (PAPER: Section 6)

The [extraction](extraction/) folder contains an implementation of extraction based on MetaCoq's **certified erasure**. 
It supports Liquidity, Midlang, and Elm as target languages. The extraction also features verified optimisations. 
Contains a README file with the details of the extraction implementation. (PAPER: Section 3)
