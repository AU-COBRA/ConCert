FROM coqorg/coq:8.16.1

# build dependencies
RUN ["/bin/bash", "--login", "-c", "set -x \
  && eval $(opam env --switch=${COMPILER} --set-switch) \
  && opam repository add --all-switches --set-default coq-released https://coq.inria.fr/opam/released \
  && opam update -y -u \
  && opam install -y -v -j ${NJOBS} coq-equations.1.3+8.16 coq-stdpp.1.8.0 coq-quickchick.1.6.4 coq-metacoq.1.1.1+8.16 \
  && opam clean -a -c -s --logs \
  && opam config list \
  && opam list"]
