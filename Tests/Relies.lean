/-
Tests.Relies
==========

Test: where can a rely candidate come from, and what does it cost to
check? Two shapes emerge on the two existing examples:

* **Frame-relies** (footprints mostly disjoint): the rely says "the partner
  preserves the fields it does not write". For mutex node `i`, a step of node
  `j ≠ i` writes only `pc j` and `turn`, so the candidate rely is
  `Rᵢ s s' := s'.pc i = s.pc i`. Checking it is *one* `action_simp; …` per node —
  the existing pipeline already discharges it.
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

open Examples.Mutex (Pc St M next req enter exit steps setPc)
open Examples.MutexLiveness (Region others)

/-! ## Frame-relies: preservation of non-written fields -/

/-- A step of node `j` writes only `pc j` and `turn`; hence, for `i ≠ j`, it
preserves `pc i`. One `action_simp` + close — no manual cases. -/
theorem steps_preserves_other_pc {n : Nat} {i j : Fin n} (h : i ≠ j) {s s' : St n}
    (hstep : rel (steps j) s s') : s'.pc i = s.pc i := by
  simp only [steps, req, enter, exit] at hstep
  action_simp
  grind

/-- The candidate frame-rely for node `i`, as a relation. -/
def R_frame {n : Nat} (i : Fin n) : Rel (St n) (St n) := fun s s' => s'.pc i = s.pc i
/-- Checking a single node step `j ≠ i` against `R_frame i` is literally the
generated lemma above. Note the shape is *generated*: unfold the partner,
`action_simp`, close — one lemma per view outside the partner's write set. -/
theorem steps_respects_frame_rely {n : Nat} {i j : Fin n} (h : i ≠ j) {s s' : St n}
    (hstep : rel (steps j) s s') : R_frame i s s' :=
  steps_preserves_other_pc h hstep

/-! ## What the frame-rely buys in the region proof -/

/-- The environment's obligation in `relyGuarantee_until` for the region.
The `pc i` conjunct of `Region i` is preserved by the *generated* frame lemma
`steps_preserves_other_pc`; the rest is what genuinely needs the protocol
argument (`region_steps_others`). The proof splits exactly along the
"derivable vs. user knowledge" line. -/
theorem region_env_via_frame {n : Nat} {i j : Fin n} (h : j ≠ i) {s s' : St n}
    (hs : Region i s) (hstep : rel (steps j) s s') : Region i s' := by
  have hp : s'.pc i = s.pc i := steps_preserves_other_pc (Ne.symm h) hstep
  exact Examples.MutexLiveness.region_steps_others i hs (by
    simp only [others, rel_choiceAll]
    exact ⟨⟨j, h⟩, hstep⟩)
/-! ## The constraint-rely shape (from Examples/RelyGuarantee) -/

/- For comparison: in the Cell example the two components have the *same*
footprint, so no frame-rely exists (`not_disjoint_self`). The rely there is
`R₂ s s' := s'.v ≤ s.v` — a value constraint about *how much* the partner
may change, which no write-set analysis can derive. The honest automation
boundary: generate and check frame-relies; ask the user for constraint-relies;
and prove `¬ Disjoint` (as the library already does) to justify the upgrade
from the frame layer to R/G. -/

end Tests.Relies
