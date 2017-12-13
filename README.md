# IRIS-ATOMIC

Atomicity related verification based on Iris logic.

## Prerequisites

This version is known to compile with:

 - Coq 8.6.1 / 8.7.0
 - Ssreflect 1.6.4
 - A development version of [Iris](https://gitlab.mpi-sws.org/FP/iris-coq/)

The easiest way to install the correct versions of the dependencies is through
opam.  You will need the Coq and Iris opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

## Building

Run `make` to build the full development.
