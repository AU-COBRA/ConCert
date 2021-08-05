FROM coqorg/coq:8.11

LABEL maintainer="jakob.botsch.nielsen@gmail.com"

RUN ["/bin/bash", "--login", "-c", "set -x \
  && eval $(opam env --switch=${COMPILER_EDGE} --set-switch) \
  && opam repository add --all-switches --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git \
  && opam update -y -u \
  && opam install -y -v -j ${NJOBS} coq-equations.1.2.1+8.11 coq-stdpp coq-quickchick \
  && opam pin -y -j ${NJOBS} add https://github.com/MetaCoq/metacoq.git#75f0cb9b8494cd0a856b77a664c662a59ddde447 \
  && opam clean -a -c -s --logs \
  && opam config list \
  && opam list"]
