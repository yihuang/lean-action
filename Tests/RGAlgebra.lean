/-
Tests.RGAlgebra
=============

Regression tests for "rely as output, not input"
(`derivedRely` / `preserves_of_guarantees`, now in `LeanAction.Frame`).

Tests:
* mutex safety recomposed *without* writing any rely: the two guarantee
  lemmas (each one `action_simp; grind`) are both the obligations and the
  interfaces;
* the recomposed `Preserves` is genuinely the same one the example proves.
-/
import LeanAction
import Examples.Mutex

open LeanAction

namespace Tests.RGAlgebra

open Examples.Mutex (St next steps1 steps2 req1 enter1 exit1 req2 enter2 exit2 inv)

theorem steps1_guarantee : ∀ s s' : St, inv s → rel steps1 s s' → inv s' := by
  intro s s' hi h
  simp only [steps1, req1, enter1, exit1, inv] at *
  action_simp
  grind

theorem steps2_guarantee : ∀ s s' : St, inv s → rel steps2 s s' → inv s' := by
  intro s s' hi h
  simp only [steps2, req2, enter2, exit2, inv] at *
  action_simp
  grind

/-- Mutex safety, recomposed *without* writing any rely: the two guarantee
lemmas above are both the obligations and the interfaces. Compare with
`Examples.Mutex.inv_step`, which goes through `inv_induct`. -/
theorem mutex_safe_recomposed : Preserves next inv := by
  simpa [next] using preserves_of_guarantees steps1_guarantee steps2_guarantee

/-- Sanity: this is genuinely the same `Preserves` the example proves. -/
theorem mutex_safe_agrees : Preserves next inv := Examples.Mutex.inv_step

end Tests.RGAlgebra
