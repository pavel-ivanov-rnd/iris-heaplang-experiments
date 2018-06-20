These examples are meant to demonstrate the applicability in Iris of the specification style for concurrent data structures described in the paper
[Modular reasoning about separation of concurrent data structures](https://link.springer.com/chapter/10.1007/978-3-642-37036-6_11).

## Overview

* [abstract_bag](abstract_bag.v) describes the generic abstract bag specification (Section 1);
* in [exclusive_bag](exclusive_bag.v) and [shared_bag](shared_bag.v) the exclusive/sequential and shared/concurrent specifications are derived from the generic abstract specification (Section 3);
* [cg_bag.v](cg_bag.v) and [fg_bag](fg_bag.v) provide two implementations for the abstract bag specification (Section 3);
* [concurrent_runners](concurrent_runners.v) implements the (impredicative) concurrent runner specification from Section 4;
* [parfib](parfib.v) demonstrates the usage of the concurrent runners library (Section 4).
* [contrib_bag.v](contrib_bag.v) -- bag specification "with contributions" a-la counter with contributions, allows for multiple concurrent `push` operations and a sequential `pop` operation.

## Differences with the paper proofs

### Circularity in `concurrent_runners`

There is a circularity in the proof of `newRunner`, which is perhaps more poignant in ML/Heap-lang than in C#.

On the first line of `newRunner`, one creates a bag and has to pick a predicate that should hold for every element in the bag.
However, the predicate that we want to have refers to the runner itself -- which is a pair of a `bag` and a `body`.
In this setting, the runner is not yet available at this point in time.
There are (at least) two potential ways of resolving this circularity:

1. Allow the `P` predicate in the `shared_bag` specification to refer to the bag itself (as a formal parameter);
2. Have a specification that would construct a bag in several steps: the `newBag_spec` will return a token that can be view-shifted later at an arbitrary point in time to `bagS b P` -- this will allow the client to pick `P` at a more comfortable point.

We chose to go with option 1 in this formalisation.
