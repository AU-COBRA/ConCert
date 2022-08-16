FROM coqorg/coq:8.14

# build dependencies
RUN ["/bin/bash", "--login", "-c", "set -x \
  && eval $(opam env --switch=${COMPILER} --set-switch) \
  && opam repository add --all-switches --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git \
  && opam update -y -u \
  && opam install -y -v -j ${NJOBS} coq-equations.1.3+8.14 coq-stdpp.1.6.0 coq-quickchick.1.5.1 \
  && opam pin -y -j ${NJOBS} add https://github.com/MetaCoq/metacoq.git#f47a91c63206d01b853d8abb016e7f04165cd518 \
  && opam clean -a -c -s --logs \
  && opam config list \
  && opam list"]
