# ConCert

A framework for smart contract verification in Coq.

## How to build


Our development works with Coq 8.11. and depends on MetaCoq installed from source,
std++ and coq-bignums. The tests depend on QuickChick. Most of the dependencies can be installed through `opam`.

To set up a switch with the necessary dependencies run the following commands from the root of the project:

```bash
opam switch create . 4.07.1
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -j 4 coq.8.11 coq-bignums coq-stdpp coq-quickchick
opam pin -j 4 add https://github.com/MetaCoq/metacoq.git#6f241fe5f0c39d1d33f9ae169c81e0db968b7117
```

After completing the procedures above, run `make` to build the development, and
`make html` to build the documentation. The documentation will be located in the
docs folder after `make html`.

## Structure of the project

The [embedding](embedding/) folder contains the development of the embedding.

The [execution](execution/) folder contains the formalization of the smart
contract execution layer, which allows reasoning about, and property-based testing of, interacting contracts. The [tests](execution/tests) folder contains example tests. The key generators used for automatically generating blockchain execution traces for testing can be found in [TraceGens.v](execution/tests/TraceGens.v). The testing framework was developed as part of a Master's Thesis at Aarhus University, and the thesis detailing (an earlier state of) the development can be found [here](https://github.com/mikkelmilo/ConCert-QuickChick-Testing-Thesis).

The [extraction](extraction/) folder contains an implemention of extraction based on MetaCoq's **certified erasure**.
It supports Liquidity and Elm as target languages. The extraction also features verified optimisations.


## Notes for developers

The [execution](execution/) subproject can be built independently via running `make` in the `execution` folder. This also means that the `_CoqProject` file inside the `execution` folder must be manually kept in sync with the main `_CoqProject` in the root.
