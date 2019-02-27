# Smart Contracts
This repo is a playground for various experiments with embedding Oak contracts
into Coq and verifying them.

## Building/Developing
This repo uses the coq-containers library by Stéphane Lescuyer. This must be
installed first. For Coq 8.9 clone [the repo](https://github.com/coq-contribs/containers)
and install it with

```bash
cd containers
make -j
make -f Makefile.coq install
```

For other versions of Coq you will need to use an appropriate tag of this repo.
See [.gitlab-ci.yml](.gitlab-ci.yml) for how the CI builds with older versions
of Coq.

After coq-containers is installed, this repo should build with
```bash
make
```
