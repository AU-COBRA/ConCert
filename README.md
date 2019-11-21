# ConCert

A framework for smart contract verification in Coq

## How to build


Our development works with Coq 8.9.1. and depends on MetaCoq 1.0~alpha+8.9 and
the std++ library v.1.2.1. These dependencies can be installed through
`opam`.

Install Coq (see https://coq.inria.fr/opam-using.html for detailed instructions on how to manage
multiple Coq installations using opam).:

```bash
opam install coq.8.9.1
```

Then MetaCoq:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-metacoq.1.0~alpha+8.9
```
And std++:

```bash
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp.1.2.1
```

After completing the procedures above, run `make` to build the development, and
`make html` to build the documentation. The documentation will be located in the
docs folder after `make htmk`.

## Structure of the project

The [embedding](embedding/) folder contains the development of the embedding.
The [execution](execution/) folder contains the formalization of the smart
contract execution layer, which allows reasoning about interacting contracts.
