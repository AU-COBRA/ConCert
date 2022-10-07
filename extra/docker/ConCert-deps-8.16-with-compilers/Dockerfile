FROM aucobra/concert:deps-8.16

LABEL maintainer="The COBRA Team"

# configuring git to use https
RUN git config --global url."https://github.com/".insteadOf git@github.com: && git config --global url."https://".insteadOf git://
ENV CARGO_NET_GIT_FETCH_WITH_CLI=true

# install liquidity 2.1-beta12
COPY liquidity /usr/local/bin

# some extra packages
RUN sudo apt update \
    && sudo apt install --no-install-recommends libcurl4-gnutls-dev libsodium-dev build-essential -y

# install Elm 0.19.1
RUN curl -L -o elm.gz https://github.com/elm/compiler/releases/download/0.19.1/binary-for-linux-64-bit.gz \
    && gunzip elm.gz \
    && sudo chmod +x elm \
    && sudo mv elm /usr/local/bin/ \
    && sudo apt install --no-install-recommends npm -y \
    && sudo npm install -g elm-test

# install Rust and cargo-concordium
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"
RUN rustup target add wasm32-unknown-unknown \
   && curl -L -O https://distribution.concordium.software/tools/linux/cargo-concordium_1.0.0 \
   && sudo chmod +x cargo-concordium_1.0.0 \
   && sudo mv cargo-concordium_1.0.0 /usr/local/bin/cargo-concordium

# install LIGO v0.50.0
RUN curl -L -O https://gitlab.com/ligolang/ligo/-/jobs/2959700000/artifacts/raw/ligo \
    && sudo chmod +x ./ligo \
    && sudo mv ligo /usr/local/bin/

