FROM coqorg/coq:8.11

COPY . /home/coq/ConCert
RUN sudo chown -R coq:coq /home/coq/ConCert

# Install Emacs and proof general
RUN ["/bin/bash", "--login", "-c", "set -x \
      && sudo apt-get update \
      && sudo apt-get install -y emacs \
      && mkdir ~/.emacs.d"]

ADD extra/docker/init.el /home/coq/.emacs.d

RUN ["/bin/bash", "--login", "-c", "set -x \
      && emacs --batch -l ~/.emacs.d/init.el"]

# Install Liquidity
RUN ["/bin/bash", "--login", "-c", "set -x \
      && git clone https://github.com/OCamlPro/liquidity \
      && cd liquidity \
      && git checkout 62ad71cdb07c6b84cb613ce4d414e9bbd13aae56 \
      && opam switch -j 4 create liquidity 4.06.1 \
      && eval `opam env --switch liquidity` \
      && sudo apt-get install -y libcurl4-gnutls-dev libgmp-dev libsodium-dev \
      && make clone-dune-network \
      && opam switch -j 4 create . 4.07.1 --no-install \
      && eval `opam env` \
      && opam pin -j 4 -y add ocaml-migrate-parsetree 1.5.0 \
      && opam install -j 4 . --deps-only --working-dir -y \
      && make \
      && make install "]

RUN sudo cp /home/coq/liquidity/_opam/bin/liquidity /usr/bin

# Install Elm
RUN ["/bin/bash", "--login", "-c", "set -x \
      && curl -L -o elm.gz https://github.com/elm/compiler/releases/download/0.19.1/binary-for-linux-64-bit.gz \
      && gunzip elm.gz \
      && chmod +x elm \
      && sudo mv elm /usr/bin/ "]

# Install Node and elm-test
RUN ["/bin/bash", "--login", "-c", " \
      curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.35.3/install.sh | bash \
      && . ~/.nvm/nvm.sh \
      && nvm install node \
      && npm install -g elm-test "]

# Install dependencies for ConCert
RUN ["/bin/bash", "--login", "-c", " \
      opam switch ${COMPILER_EDGE} \
      && eval $(opam env) \
      && opam update \
      && opam install -y -v -j 4 coq-equations.1.2.3+8.11 coq-stdpp.1.4.0 coq-ext-lib.0.11.2 coq-quickchick.1.3.2 \
      && opam pin -y -j 4 add https://github.com/MetaCoq/metacoq.git#df8ef08832d4b30f1b354a8e751cdaf154d0b9a0 "]

# Build ConCert and extract examples
RUN ["/bin/bash", "--login", "-c", "set -x \
      && cd ~/ConCert \
      && make -j4 "]
