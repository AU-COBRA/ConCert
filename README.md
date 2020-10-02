# ConCert

A framework for smart contract verification in Coq. 

Papers detailing the development:
- [ConCert: A Smart Contract Certification Framework in Coq](https://arxiv.org/abs/1907.10674)
- [Smart Contract Interactions in Coq](https://arxiv.org/abs/1911.04732)
- [Verifying, testing and running smart contracts in ConCert](https://cs.au.dk/fileadmin/site_files/cs/AA_pdf/COBRA_Paper_-_Verifying__testing_and_running_smart_contracts_in_ConCert.pdf)
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
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp
opam install coq-quickchick
```

Install MetaCoq's coq-8.11 branch from source. The simplest way is to clone the MetaCoq repo, check out the coq-8.11 branch, and then run `opam install <path to MetaCoq>`.
For more instructions, see the [official MetaCoq repo](https://github.com/MetaCoq/metacoq#installing-from-github-repository-for-developers).

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
