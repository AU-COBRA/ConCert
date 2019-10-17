# ConCert

A framework for smart contract verification in Coq

## How to build

Our development works with Coq 8.9.1. and depends on MetaCoq 1.0~alpha. Both can be installed through `opam`.

First, install Coq:

```
opam install coq.8.9.1
```

Then MetaCoq:

```
opam install coq-metacoq
```

After completing the procedures above, run `make`. By default, `make` will build all the development and the documentation.

