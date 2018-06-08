# IRIS-ATOMIC

Atomicity related verification based on Iris logic.

## Prerequisites

This version is known to compile with:

 - Coq 8.7.1 / 8.8.0
 - A development version of [Iris](https://gitlab.mpi-sws.org/FP/iris-coq/)

## Building from source

When building from source, we recommend to use opam (1.2.2 or newer) for
installing the dependencies.  This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update, do `git pull`.  After an update, the development may fail to compile
because of outdated dependencies.  To fix that, please run `opam update`
followed by `make build-dep`.
