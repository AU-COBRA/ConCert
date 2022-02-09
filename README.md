# ConCert

A framework for smart contract verification in Coq.

See the [Papers](#papers) for details on the development.
ConCert is able to find real world attacks as explained [here](https://medium.com/blockchain-academy-network/finding-real-world-bugs-in-smart-contract-interactions-with-property-based-testing-9eb59b117785) and [here](https://medium.com/blockchain-academy-network/preventing-an-8m-attack-on-ethereums-bzx-defi-platform-with-property-based-testing-12234d9479b7).

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


## Notes for developers

The project consists of three subprojects: `embedding`, `execution`, and `extraction` located in the corresponding folders.
Each subproject has its own `_CoqProject` file and `Makefile`.
The `Makefile` in the root folder dispatches the calls to the corresponding subproject.

## Documentation

The [project documentation in HTML format](https://au-cobra.github.io/ConCert/toc.html) is generated for each build.
We use the standard Coqdoc with improved styles and scripts of [CoqdocJS](https://github.com/tebbi/coqdocjs) ([license](extra/resources/coqdocjs/LICENSE)) and local table of contents by [TOC](https://github.com/jgallen23/toc)([license](extra/resources/toc/LICENSE)).

## Papers
- ["Code Extraction from Coq to ML-like languages"](papers/ML-family.pdf). Danil Annenkov, Mikkel Milo and Bas Spitters. ["ML'21"](https://icfp21.sigplan.org/details/mlfamilyworkshop-2021-papers/8/Code-Extraction-from-Coq-to-ML-like-languages) at ICFP'21
- ["Extending MetaCoq Erasure: Extraction to Rust and Elm"](https://dannenkov.me/papers/extraction-rust-elm-coq-workshop2021.pdf). Extended abstract. The Coq Workshop 2021  Danil Annenkov, Mikkel Milo, Jakob Botsch Nielsen, and Bas Spitters.
- ["Extracting Smart Contracts Tested and Verified in Coq"](https://arxiv.org/abs/2012.09138) Danil Annenkov, Mikkel Milo, Jakob Botsch Nielsen, Bas Spitters. CPP'21.
- ["Verifying, testing and running smart contracts in ConCert"](https://cs.au.dk/fileadmin/site_files/cs/AA_pdf/COBRA_Paper_-_Verifying__testing_and_running_smart_contracts_in_ConCert.pdf)
  Danil Annenkov, Mikkel Milo, Jakob Botsch Nielsen, Bas Spitters. Coq Workshop 2020.
- ["ConCert: A Smart Contract Certification Framework in Coq"](https://arxiv.org/abs/1907.10674)
  Danil Annenkov, Jakob Botsch Nielsen, Bas Spitters. CPP 2020.
- ["Smart Contract Interactions in Coq"](https://arxiv.org/abs/1911.04732)
   Jakob Botsch Nielsen, Bas Spitters. 1st Workshop on Formal Methods for Blockchains, 3rd Formal Methods World Congress, October 2019.

## Videos
A video collection, presenting various parts of ConCert can be found on [Youtube](https://www.youtube.com/playlist?list=PLtiwJZcxuZ0-Hj64hganyt-WnaHSyA7Pn).

### Citing the papers
```
@inproceedings{ConCert-extraction-testing,
author = {Annenkov, Danil and Milo, Mikkel and Nielsen, Jakob Botsch and Spitters, Bas},
title = {Extracting Smart Contracts Tested and Verified in Coq},
year = {2021},
isbn = {9781450382991},
publisher = {Association for Computing Machinery},
url = {https://doi.org/10.1145/3437992.3439934},
doi = {10.1145/3437992.3439934},
pages = {105–121},
numpages = {17},
location = {Virtual, Denmark},
series = {CPP 2021}
}

@article{ConCert,
   title={ConCert: a smart contract certification framework in Coq},
   ISBN={9781450370974},
   url={http://dx.doi.org/10.1145/3372885.3373829},
   DOI={10.1145/3372885.3373829},
   journal={Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs},
   publisher={ACM},
   author={Annenkov, Danil and Nielsen, Jakob Botsch and Spitters, Bas},
   year={2020},
   month={Jan}
}

@inproceedings{smart-contract-interactions,
  author    = {Jakob Botsch Nielsen and
               Bas Spitters},
  title     = {Smart Contract Interactions in Coq},
  booktitle = {{FM} Workshops {(1)}},
  series    = {Lecture Notes in Computer Science},
  volume    = {12232},
  pages     = {380--391},
  publisher = {Springer},
  year      = {2019}
}
```



