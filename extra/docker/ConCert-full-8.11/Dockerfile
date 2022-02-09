FROM aucobra/concert:deps-coq-8.11-with-compilers-ligo-0.34.0

LABEL maintainer="Cobra Team"

RUN ["/bin/bash", "--login", "-c", "set -x \
  && eval $(opam env --switch=${COMPILER_EDGE} --set-switch) \
  && opam repo add coq-released https://coq.inria.fr/opam/released \
  && cd ~ && git clone https://github.com/AU-COBRA/ConCert.git && cd ConCert && make install "]
