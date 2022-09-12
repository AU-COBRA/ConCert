# ConCert
[![Build](https://github.com/AU-COBRA/ConCert/actions/workflows/build.yml/badge.svg)](https://github.com/AU-COBRA/ConCert/actions/workflows/build.yml)
![GitHub](https://img.shields.io/github/license/AU-COBRA/ConCert)

A framework for smart contract verification in Coq.

See the [Papers](#papers) for details on the development.
ConCert is able to find real world attacks as explained
[here](https://medium.com/blockchain-academy-network/finding-real-world-bugs-in-smart-contract-interactions-with-property-based-testing-9eb59b117785),
[here](https://medium.com/blockchain-academy-network/preventing-an-8m-attack-on-ethereums-bzx-defi-platform-with-property-based-testing-12234d9479b7) and
[here](https://medium.com/@bawspitters/using-formal-methods-to-prevent-creating-money-out-of-thin-air-5f30057fe3d3).

## How to build


Our development works with Coq 8.15 and depends on MetaCoq, std++ and coq-equations.
The tests depend on QuickChick.
The dependencies can be installed through `opam`.

To set up a switch with the necessary dependencies run the following commands from the root of the project:

```bash
git clone https://github.com/AU-COBRA/ConCert.git
cd ConCert
git submodule init
git submodule update
opam switch create . 4.10.2 --repositories default,coq-released=https://coq.inria.fr/opam/released --deps-only
eval $(opam env)
```

If Coq 8.15 is already installed, run

```bash
git clone https://github.com/AU-COBRA/ConCert.git
cd ConCert
git submodule init
git submodule update
opam repo add coq-released https://coq.inria.fr/opam/released
opam install ./coq-concert.opam --deps-only
```

After completing the procedures above, run `make` to build the development, and `make html` to build the documentation.
The documentation will be located in the docs folder after `make html`.
Example contracts can be built by running `make examples`.

## Structure of the project

Each folder contains a separate README file with more details.

The [embedding](embedding/) folder contains the development of the verified embedding of ``λsmart`` to Coq.

The [execution](execution/) folder contains the formalization of the smart
contract execution layer, which allows reasoning about, and property-based testing of, interacting contracts. The [test](execution/test) folder contains the property-based testing framework. The key generators used for automatically generating blockchain execution traces for testing can be found in [TraceGens.v](execution/test/TraceGens.v). The testing framework was developed as part of a Master's Thesis at Aarhus University, and the thesis detailing (an earlier state of) the development can be found [here](https://github.com/mikkelmilo/ConCert-QuickChick-Testing-Thesis).

The [typed-extraction](https://github.com/AU-COBRA/typed-extraction) submodule contains an implementation of the extraction pipeline based on MetaCoq's **verified erasure** extended with an erasure procedure for types.
It also features *certifying*(proof-generating) pre-processing steps and verified dead argument elimination.

The [extraction](extraction/) folder contains extraction pipeline for smart contract languages.
Currently, we support smart contract languages Liquidity and CameLIGO, and general-purpose languages Elm and Rust as targets.
Pretty-printers to these languages are implemented directly in Coq.
One also can obtain an OCaml plugin for Coq by extracting our pipeline using the standard extraction of Coq (currently, it is possible for extraction to Rust).

The [examples](examples/) folder contains examples of smart-contract implementations, embedding, extraction and tests. Extracted smart-contracts can be found [here](https://github.com/AU-COBRA/extraction-resutls).

## Notes for developers

The project consists of five subprojects: `embedding`, `execution`, `extraction`, `typed-extraction`, and `examples` located in the corresponding folders.
Each subproject has its own `_CoqProject` file and `Makefile`.
The `Makefile` in the root folder dispatches the calls to the corresponding subproject.

## Documentation

The [project documentation in HTML format](https://au-cobra.github.io/ConCert/toc.html) is generated for each build.
We use the standard Coqdoc with improved styles and scripts of [CoqdocJS](https://github.com/tebbi/coqdocjs) ([license](extra/resources/coqdocjs/LICENSE)) and local table of contents by [TOC](https://github.com/jgallen23/toc)([license](extra/resources/toc/LICENSE)).

## Papers
- ["Extracting functional programs from Coq, in Coq"](https://arxiv.org/abs/2108.02995).
  Danil Annenkov, Mikkel Milo, Jakob Botsch Nielsen, Bas Spitters.
  Journal of Functional Programming (JFP), Volume 32, 2022, e11. [DOI: 10.1017/S0956796822000077](https://doi.org/10.1017/S0956796822000077)
  <br>
  <details>
    <summary>Cite paper</summary>
    
    ```
    @article{annenkov_milo_nielsen_spitters_2022,
      author={ANNENKOV, DANIL and MILO, MIKKEL and NIELSEN, JAKOB BOTSCH and SPITTERS, BAS},
      title={{Extracting functional programs from Coq, in Coq}},
      volume={32},
      DOI={10.1017/S0956796822000077},
      journal={Journal of Functional Programming},
      publisher={Cambridge University Press},
      year={2022},
      pages={e11}
    }
    ```
  </details>
- ["Finding Smart Contract Vulnerabilities with ConCert’s Property-Based Testing Framework"](https://arxiv.org/abs/2208.00758).
  Mikkel Milo, Eske Hoy Nielsen, Danil Annenkov, and Bas Spitters.
  FMBC 2022.
- ["Formalising Decentralised Exchanges in Coq"](https://arxiv.org/abs/2203.08016).
  Eske Hoy Nielsen, Danil Annenkov and Bas Spitters.
  Preprint.
- ["Code Extraction from Coq to ML-like languages"](papers/ML-family.pdf).
  Danil Annenkov, Mikkel Milo and Bas Spitters.
  ["ML'21"](https://icfp21.sigplan.org/details/mlfamilyworkshop-2021-papers/8/Code-Extraction-from-Coq-to-ML-like-languages) at ICFP'21.
  <br>
  <details>
    <summary>Cite paper</summary>

    ```
    @article{annenkovcode,
      title={Code Extraction from Coq to ML-like languages},
      author={Annenkov, Danil and Milo, Mikkel and Spitters, Bas},
      year = {2021},
      url = {https://icfp21.sigplan.org/details/mlfamilyworkshop-2021-papers/8/Code-Extraction-from-Coq-to-ML-like-languages},
      location = {ML’21 at ICFP’21,}
    }
    ```
  </details>
- ["Extending MetaCoq Erasure: Extraction to Rust and Elm"](https://dannenkov.me/papers/extraction-rust-elm-coq-workshop2021.pdf).
  Danil Annenkov, Mikkel Milo, Jakob Botsch Nielsen, and Bas Spitters.
  Extended abstract. The Coq Workshop 2021.
  <br>
  <details>
    <summary>Cite paper</summary>

    ```
    @article{annenkovextending,
      title={Extending MetaCoq Erasure: Extraction to Rust and Elm},
      author={Annenkov, Danil and Milo, Mikkel and Nielsen, Jakob Botsch and Spitters, Bas},
      year = {2021},
      url = {https://dannenkov.me/papers/extraction-rust-elm-coq-workshop2021.pdf},
      location = {Coq Workshop 2021}
    }
    ```
  </details>
- ["Extracting Smart Contracts Tested and Verified in Coq"](https://arxiv.org/abs/2012.09138).
  Danil Annenkov, Mikkel Milo, Jakob Botsch Nielsen, Bas Spitters.
  CPP'21.
  <br>
  <details>
    <summary>Cite paper</summary>

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
    ```
  </details>
- ["Verifying, testing and running smart contracts in ConCert"](https://cs.au.dk/fileadmin/site_files/cs/AA_pdf/COBRA_Paper_-_Verifying__testing_and_running_smart_contracts_in_ConCert.pdf).
  Danil Annenkov, Mikkel Milo, Jakob Botsch Nielsen, Bas Spitters.
  Coq Workshop 2020.
  <br>
  <details>
    <summary>Cite paper</summary>

    ```
    @article{annenkovverifying,
      title={Verifying, testing and running smart contracts in ConCert},
      author={Annenkov, Danil and Milo, Mikkel and Nielsen, Jakob Botsch and Spitters, Bas},
      year = {2020},
      url = {https://cs.au.dk/fileadmin/site_files/cs/AA_pdf/COBRA_Paper_-_Verifying__testing_and_running_smart_contracts_in_ConCert.pdf},
      location = {Coq Workshop 2020}
    }
    ```
  </details>
- ["ConCert: A Smart Contract Certification Framework in Coq"](https://arxiv.org/abs/1907.10674).
  Danil Annenkov, Jakob Botsch Nielsen, Bas Spitters.
  CPP 2020.
  <br>
  <details>
    <summary>Cite paper</summary>

    ```
    @article{ConCert,
      title={ConCert: a smart contract certification framework in Coq},
      ISBN={9781450370974},
      url={https://dx.doi.org/10.1145/3372885.3373829},
      DOI={10.1145/3372885.3373829},
      journal={Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs},
      publisher={ACM},
      author={Annenkov, Danil and Nielsen, Jakob Botsch and Spitters, Bas},
      year={2020},
      month={Jan}
    }
    ```
  </details>
- ["Smart Contract Interactions in Coq"](https://arxiv.org/abs/1911.04732).
   Jakob Botsch Nielsen, Bas Spitters.
   1st Workshop on Formal Methods for Blockchains, 3rd Formal Methods World Congress, October 2019.
  <br>
  <details>
    <summary>Cite paper</summary>
    
    ```
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
  </details>

## Videos
A video collection, presenting various parts of ConCert can be found on [Youtube](https://www.youtube.com/playlist?list=PLWcJeGdOHpbxb_DhcfppHRrZKW7wPO9qQ).

### Citing the papers

```
@article{annenkov_milo_nielsen_spitters_2022,
   author={ANNENKOV, DANIL and MILO, MIKKEL and NIELSEN, JAKOB BOTSCH and SPITTERS, BAS},
   title={{Extracting functional programs from Coq, in Coq}},
   volume={32},
   DOI={10.1017/S0956796822000077},
   journal={Journal of Functional Programming},
   publisher={Cambridge University Press},
   year={2022},
   pages={e11}
   }

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
  url={https://dx.doi.org/10.1145/3372885.3373829},
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
