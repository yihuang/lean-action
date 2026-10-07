/-
Aggregator for the regression-test modules (see the header comments of each):

* `Tests.Enabled`  — the `Enabled` predicate + `enabled_*` simp set.
* `Tests.WF1`      — the WF1 leads-to rule, proved from `WeakFair`.
* `Tests.Commute`  — compositional `Disjoint` theorems + the function-update
  (array-like) boundary.
* `Tests.Relies`   — frame-relies are one `action_simp; grind` each;
  constraint-relies are user knowledge.
* `Tests.DisjointUnder` — conditional disjointness: one abstraction that is
  simultaneously the footprint layer's conditional frame, the RG layer's
  rely special case, and the temporal layer's static region shadow.
-/

import Tests.Enabled
import Tests.WF1
import Tests.Commute
import Tests.Relies
import Tests.DisjointUnder
import Tests.RGAlgebra
import Tests.Certificates
