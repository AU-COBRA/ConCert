# ConCert embedding
This subfolder contains the development of an embedding of the functional
programming language ``λsmart`` into Rocq.

## Some highlights
* [theories/Ast.v](theories/Ast.v) contains the definition of the ``λsmart``
language.

* [theories/EvalE.v](theories/EvalE.v) contains an interpreter for ``λsmart``
language.

* [theories/pcuic/](theories/pcuic/) contains translation from ``λsmart``
expression to PCUIC terms, proof of soundness and various auxiliary lemmas for
that proof.
* [examples/](examples/) contains examples of smart contract
verification: verification of ``Acorn`` list
functions, and integration with the blockchain execution framework.

* [examples/Demo.v](examples/Demo.v) contains a demonstration
using our framework to write definitions using the deep embedding, convert them
to Rocq functions, compute with the interpreter and prove simple properties using
the shallow embedding.

* [examples/ExecFrameworkIntegration.v](../examples/crowdfunding/ExecFrameworkIntegration.v)
is an "end-to-end" example of writing a smart contract in ``λsmart``, translating it
to Gallina, and integrating it with the execution framework and proving safety
properties about it.
