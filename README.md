# Smart Contracts
This repo is a playground for various experiments with embedding Oak contracts
into Coq and verifying them.

## Building/Developing
This repo uses the std++ library. This must be installed first and can be
installed via Opam, after adding the dev repo of Iris:
```bash
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp
```
For more instructions, see [the stdpp readme](https://gitlab.mpi-sws.org/iris/stdpp).

After stdpp is installed, this repo should build with
```bash
make
```
