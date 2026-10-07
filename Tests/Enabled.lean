/-
Tests.Enabled
===========

Regression tests for the `Enabled` predicate and its `enabled_*` unfolding
set, now in `LeanAction.Action` / `LeanAction.Lens` (the "other half" of the
`rel_*` set, in the style of TLAPS's ENABLED rewrite rules).

Tests:
* a real liveness obligation (the `henabled` hypothesis shape of the rank
  theorems) collapses to the same `refine witness; action_simp; grind`
  pattern the library already uses;
* a disabledness fact (`¬ Enabled enter1` when the turn is held by the other
  process) is a pure `action_simp; grind` one-liner — no case analysis.
-/
import LeanAction
import Examples.Mutex

open LeanAction

namespace Tests.Enabled

/-! ## Test 1: the mutex liveness `henabled` obligation shape -/

open Examples.Mutex (St M next steps1 steps2 req1 enter1 exit1 req2 enter2 exit2)

/-- The `henabled` hypothesis of `eventually_zero_of_weakFair_inv`, for `enter1`
inside the region. Same pattern as the library's `MutexLiveness` proof
(exhibit a successor, `action_simp`, `grind`), but the *statement* now has the
`Enabled` shape that WF1-style rules can consume. -/
theorem enter1_enabled_of_region (s : St) (hs : s.pc1 = 1 ∧ s.turn = 1 ∧ s.pc2 ≤ 1) :
    Enabled enter1 s := by
  show ∃ s', rel enter1 s s'
  refine ⟨{ s with pc1 := 2 }, ?_⟩
  simp only [enter1]
  action_simp
  grind

/-! ## Test 2: disabledness by pure rewriting -/

/-- When process 2 holds the turn, `enter1` is disabled. Negated `Enabled`
goals need no witness, so this is a one-liner — compare with the manual
`not_rel_guard_seq` + case analysis in `Examples.Mutex`. -/
theorem enter1_disabled_when_turn2 {s : St} (ht : s.turn = 2) :
    ¬ Enabled enter1 s := by
  simp only [Enabled, enter1]
  action_simp
  grind

/-- Inside the region, `enter1`'s enabledness *is* the region's guard: after
unfolding, `enabled_guard` + `enabled_seq` + `enabled_update` close it. -/
theorem enter1_enabled_iff_region (s : St) :
    Enabled enter1 s ↔ s.pc1 = 1 ∧ s.turn = 1 := by
  simp only [enter1, Enabled]
  action_simp
  grind

end Tests.Enabled
