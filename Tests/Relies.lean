/-
Tests.Relies
==========

Test: where can a rely candidate come from, and what does it cost to
check? Two shapes emerge on the two existing examples:

* **Frame-relies** (footprints mostly disjoint): the rely says "the partner
  preserves the fields it does not write". For mutex process 1, the write
  set of `steps2` is `{pc2, turn}`, so the candidate rely for process 1 is
  `R₁ s s' := s'.pc1 = s.pc1`. Checking it is *one* `action_simp; grind`
  per field — the existing pipeline already discharges it.
* **Constraint-relies** (footprints fully overlap, as in
  `Examples/RelyGuarantee`): the rely is a value constraint (`v` does not
  increase) that cannot be derived from write sets — it is user knowledge.
  Automation can only *check*, never *guess*, this shape.

So "automatic discovery of relies" should mean: derive the frame part
mechanically, leave the constraint part to the user, and fail loudly when a
guard-free partner step breaks the invariant (the §11.9 infeasibility case).
-/

import LeanAction
import Examples.Mutex
import Examples.MutexLiveness

open LeanAction

namespace Tests.Relies

open Examples.Mutex (St M next steps1 steps2 req1 enter1 exit1 req2 enter2 exit2)

/-! ## Frame-relies: preservation of non-written fields -/

/-- `steps2`'s write set is `{pc2, turn}`; hence, automatically checkable,
`steps2` preserves `pc1`. One `action_simp; grind` — no manual cases. -/
theorem steps2_preserves_pc1 {s s' : St} (h : rel steps2 s s') : s'.pc1 = s.pc1 := by
  simp only [steps2, req2, enter2, exit2] at h
  action_simp
  grind

/-- Symmetrically for process 2. Note both proofs are *generated* in the same
shape: unfold the partner, `action_simp`, `grind`. A metaprogram can emit
one lemma per field outside the partner's write set. -/
theorem steps1_preserves_pc2 {s s' : St} (h : rel steps1 s s') : s'.pc2 = s.pc2 := by
  simp only [steps1, req1, enter1, exit1] at h
  action_simp
  grind

/-- `steps2` also preserves the *bounds* it doesn't touch: `pc1` range. This
is the shape the region's rely obligation needs. -/
theorem steps2_preserves_pc1_range {s s' : St} (h : rel steps2 s s')
    (hb : s.pc1 ≤ 2) : s'.pc1 ≤ 2 := by
  rw [steps2_preserves_pc1 h]
  exact hb

/-- The candidate frame-rely for process 1, as a relation. -/
def R_frame : Rel St St := fun s s' => s'.pc1 = s.pc1

/-- Checking `steps2 ⊆ R_frame` is literally the generated lemma above. -/
theorem steps2_respects_frame_rely {s s' : St} (h : rel steps2 s s') : R_frame s s' :=
  steps2_preserves_pc1 h

/-! ## What the frame-rely buys in the region proof -/

open Examples.MutexLiveness (Region)

/-- The environment's obligation in `relyGuarantee_until` for the region.
The `pc1` conjunct of `Region` is preserved by the *generated* frame lemma
`steps2_preserves_pc1`; the `pc2 ≤ 1` bound is what genuinely needs the
protocol argument (`region_steps2`). The proof splits exactly along the
"derivable vs. user knowledge" line. -/
theorem region_env_via_frame {s s' : St} (hs : Region s) (h : rel steps2 s s') :
    Region s' := by
  have hp1 : s'.pc1 = s.pc1 := steps2_preserves_pc1 h
  exact Examples.MutexLiveness.region_steps2 hs h

/-! ## The constraint-rely shape (from Examples/RelyGuarantee) -/

/- For comparison: in the Cell example the two components have the *same*
footprint, so no frame-rely exists (`not_disjoint_self`). The rely there is
`R₂ s s' := s'.v ≤ s.v` — a value constraint about *how much* the partner
may change, which no write-set analysis can derive. The honest automation
boundary: generate and check frame-relies; ask the user for constraint-relies;
and prove `¬ Disjoint` (as the library already does) to justify the upgrade
from the frame layer to R/G. -/

end Tests.Relies
