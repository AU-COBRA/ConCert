FROM coqorg/coq:8.11

# build dependencies
RUN ["/bin/bash", "--login", "-c", "set -x \
  && eval $(opam env --switch=${COMPILER_EDGE} --set-switch) \
  && opam repository add --all-switches --set-default coq-released https://coq.inria.fr/opam/released \
  && opam update -y -u \
  && opam install -y -v -j ${NJOBS} coq-equations.1.2.3+8.11 coq-stdpp.1.7.0 coq-quickchick.1.6.0 \
  && opam pin -y -j ${NJOBS} add https://github.com/MetaCoq/metacoq.git#75f0cb9b8494cd0a856b77a664c662a59ddde447 \
  && opam clean -a -c -s --logs \
  && opam config list \
  && opam list"]
