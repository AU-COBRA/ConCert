FROM coqorg/coq:8.11

LABEL maintainer="jakob.botsch.nielsen@gmail.com"

RUN ["/bin/bash", "--login", "-c", "set -x \
  && eval $(opam env --switch=${COMPILER_EDGE} --set-switch) \
  && opam repository add --all-switches --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git \
  && opam update -y -u \
  && opam install -y -v -j ${NJOBS} coq-equations.1.2.1+8.11 coq-stdpp coq-quickchick \
  && git clone https://github.com/MetaCoq/metacoq.git \
  && cd metacoq \
  && git checkout coq-8.11 \
  && opam install -y -v -j ${NJOBS} . \
  && opam clean -a -c -s --logs \
  && opam config list \
  && opam list"]
