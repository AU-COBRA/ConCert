FROM coqorg/coq:8.14

# build dependencies
RUN ["/bin/bash", "--login", "-c", "set -x \
  && eval $(opam env --switch=${COMPILER} --set-switch) \
  && opam repository add --all-switches --set-default coq-released https://coq.inria.fr/opam/released \
  && opam update -y -u \
  && opam install -y -v -j ${NJOBS} coq-equations.1.3+8.14 coq-stdpp.1.7.0 coq-quickchick.1.6.0 coq-metacoq.1.0+8.14 \
  && opam clean -a -c -s --logs \
  && opam config list \
  && opam list"]
