iris-atomic
====

Atomicity related verification based on Iris logic.

Build
--------

1. `git clone` this repo
2. `git submodule update --init` to fetch corresponding Iris library as a submodule
3. `cd iris-coq; make; make install` to install Iris library (system globally). Or you can use `make userinstall` to install user globally.
4. `cd ..; make` to compile this repo

