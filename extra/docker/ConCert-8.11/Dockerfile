FROM coqorg/coq:8.11

LABEL maintainer="jakob.botsch.nielsen@gmail.com"

RUN ["/bin/bash", "--login", "-c", "set -x \
  && eval $(opam env --switch=${COMPILER_EDGE} --set-switch) \
  && opam repository add --all-switches --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git \
  && opam update -y -u \
  && opam install -y -v -j ${NJOBS} coq-stdpp coq-metacoq.1.0~alpha2+8.11 \
  && opam clean -a -c -s --logs \
  && opam config list \
  && opam list"]
