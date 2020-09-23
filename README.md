# ConCert

A framework for smart contract verification in Coq.

## How to build

Our development works with Coq 8.11 and depends on MetaCoq 1.0 installed from source, std++ and
coq-bignums. The tests depend on QuickChick.

There are two ways to build the artifact. You can either set up an opam switch and build the sources
in that switch. Doing so will allow you to build the Coq files, but not run the extracted examples
using the Liquidity or Elm compilers, which you will have to install separately. Alternatively,
there is a Dockerfile provided that installs everything (including Liquidity and Elm) and then
builds the project. For instructions on that, see the next section.

To install from source you must first have opam install. With opam installed, run the following
commands from the project root:

```bash
opam switch create . 4.07.1
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -j 4 coq.8.11.2 coq-equations.1.2.3+8.11 coq-bignums.8.11.0 coq-stdpp.1.4.0 coq-ext-lib.0.11.2 coq-quickchick.1.3.2
opam pin -j 4 add https://github.com/MetaCoq/metacoq.git#df8ef08832d4b30f1b354a8e751cdaf154d0b9a0
```

After completing the procedures above, run `make` to build the development, and `make html` to build
the documentation. The documentation will be located in the docs folder after `make html`.

To test the code produced by our extraction run `make test-extraction`. This command requires [Elm
compiler](https://guide.elm-lang.org/install/elm.html) with the `elm-explorations/test` package and
[Liquidity compiler](https://www.liquidity-lang.org/doc/installation/index.html) (follow the
instructions, but pin the version of `ocaml-migrate-parsetree` to 1.5.5).

## Building with Docker

To build and install everything (including the Elm and Liquidity compilers) you can instead use
Docker. With Docker installed, simply run

```bash
docker build --tag concert .
```

This will produce an image with everything installed. Additionally, it includes Emacs and Proof
General so that proofs can be explored. To run the image use:
```bash
docker run --interactive --tty concert
```

ConCert is located and built at `~/ConCert` in the image. You can run `make test-extraction` from
this folder and it will test the extracted examples using Liquidity and Elm compilers.

## Structure of the project

See notes with "PAPER:" prefix referencing the corresponding sections/definitions in the paper.

The [embedding](embedding/) folder contains the development of the embedding.

The [execution](execution/) folder contains the formalization of the smart contract execution layer,
which allows reasoning about, and property-based testing of, interacting contracts. Contains a
README file with the details of the execution layer structure.

The [extraction](extraction/) folder contains an implementation of extraction based on MetaCoq's
**certified erasure**.  It supports Liquidity, Midlang, and Elm as target languages. The extraction
also features verified optimisations. Contains a README file with the details of the extraction
implementation (PAPER: Section 3).

The [execution/examples](execution/examples) folder contains implementations of and theorems about
smart contracts.  It includes the [Escrow](execution/examples/Escrow.v) contract (PAPER: Section 4)
and the [Boardroom voting](execution/examples/BoardroomVoting.v) contract (PAPER: Section 5)

The [execution/tests](execution/tests) folder contains example tests. The key generators used for
automatically generating blockchain execution traces for testing can be found in
[TraceGens.v](execution/tests/TraceGens.v) (PAPER: Section 6).
