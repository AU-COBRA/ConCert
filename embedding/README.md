# ConCert embedding
This subfolder contains the development of an embedding of the functional
programming language ``λsmart`` into Coq.

## Some highlights
* [theories/Ast.v](theories/Ast.v) contains the definition of the ``λsmart``
language.

* [theories/EvalE.v](theories/EvalE.v) contains an interpreter for ``λsmart``
language.

* [theories/pcuic/](theories/pcuic/) contains translation from ``λsmart``
expression to PCUIC terms, proof of soundness and various auxiliary lemmas for
that proof.
* [theories/examples/](theories/examples/) contains examples of smart contract
verification: the crowdfunding contract, verification of ``Acorn`` list
functions, integration with the execution framework.

* [theories/examples/Demo.v](theories/examples/Demo.v) contains a demonstration
using our framework to write definitions using the deep embedding, convert them
to Coq functions, compute with the interpreter and prove simple properties using
the shallow embedding.

* [theories/examples/ExecFrameworkIntegration.v](theories/examples/ExecFrameworkIntegration.v)
is an "end-to-end" example of writing a contract in ``λsmart``, translating it
to Gallina, and integrating it with the execution framework to prove safety
properties about it.
