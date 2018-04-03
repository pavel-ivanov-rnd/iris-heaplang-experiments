These examples are meant to demonstrate the applicability in Iris of the specification style for concurrent data structures described in the paper
[Modular reasoning about separation of concurrent data structures](https://link.springer.com/chapter/10.1007/978-3-642-37036-6_11).

## Overview

* [abstract_bag](abstract_bag.v) describes the generic abstract bag specification (Section 1);
* in [exclusive_bag](exclusive_bag.v) and [shared_bag](shared_bag.v) the excluive/sequntial and shared/concurrent specifications are derived from the generic abstract specification (Section 3);
* [cg_bag.v](cg_bag.v) and [fg_bag](fg_bag.v) provide two implementations for the abstract bag specification (Section 3);
* [concurrent_runners](concurrent_runners.v) implements the (impredicative) concurrent runner specification from Section 4;
* [parfib](parfib.v) demonstrates the usage of the concurrent runners library (Section 4).
