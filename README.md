# IRIS EXAMPLES

Some example verification demonstrating the use of Iris.

## Prerequisites

This version is known to compile with:

 - Coq 8.6.1 / 8.7.0
 - Ssreflect 1.6.4
 - A development version of [Iris](https://gitlab.mpi-sws.org/FP/iris-coq/)
 - The coq86-devel branch of [Autosubst](https://github.com/uds-psl/autosubst)

The easiest way to install the correct versions of the dependencies is through
opam.  You will need the Coq and Iris opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

## Building

Run `make` to build the full development.

## For Developers: How to update the Iris dependency

* Do the change in Iris, push it.
* Wait for CI to publish a new Iris version on the opam archive, then run
  `opam update iris-dev`.
* In iris-examples, change the `opam` file to depend on the new version.
* Run `make build-dep` (in iris-examples) to install the new version of Iris.
  You may have to do `make clean` as Coq will likely complain about .vo file
  mismatches.
