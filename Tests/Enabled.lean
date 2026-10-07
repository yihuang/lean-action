/-
Tests.Enabled
===========

Regression tests for the `Enabled` predicate and its `enabled_*` unfolding
set, now in `LeanAction.Action` / `LeanAction.Lens` (the "other half" of the
`rel_*` set, in the style of TLAPS's ENABLED rewrite rules).

The mutex example is now the N-node one, so the tests are stated for an
arbitrary node index `i : Fin n`; the `enter i` guard is the node's two region
conjuncts, and "disabled" now has an explicit `j ≠ i` side condition.

Tests:
* a real liveness obligation (the `henabled` hypothesis shape of the rank
  theorems) collapses to the same `refine witness; action_simp; …` pattern the
  library already uses;
* a disabledness fact (`¬ Enabled (enter i)` when another node holds the token)
  is a pure `action_simp; …` one-liner — no case analysis.
-/
import LeanAction
import Examples.Mutex
import Examples.MutexLiveness

open LeanAction

namespace Tests.Enabled

open Examples.Mutex (Pc St M next req enter exit steps setPc release)
open Examples.MutexLiveness (Region)

/-! ## Test 1: the mutex liveness `henabled` obligation shape -/

/-- The `henabled` hypothesis of the rank rules, for `enter i` inside the
region. Same pattern as the library's `MutexLiveness` proof (exhibit a
successor, `action_simp`, close), but the *statement* has the `Enabled` shape
that WF1-style rules consume. -/
theorem enter_enabled_of_region {n : Nat} {i : Fin n} (s : St n) (hs : Region i s) :
    Enabled (enter i) s := by
  simp only [Region] at hs
  show ∃ s', rel (enter i) s s'
  refine ⟨setPc s i Pc.cs, ?_⟩
  simp only [enter]
  action_simp
  exact ⟨s, ⟨⟨hs.1, hs.2.1⟩, rfl⟩, rfl⟩

/-! ## Test 2: disabledness by pure rewriting -/

/-- When another node `j ≠ i` holds the token, `enter i` is disabled. Negated
`Enabled` goals need no witness, so this is a one-liner — compare with the manual
`not_rel_guard_seq` + case analysis in `Examples.Mutex`. -/
theorem enter_disabled_when_other_holds {n : Nat} {i j : Fin n} {s : St n}
    (h : j ≠ i) (ht : s.turn = j) : ¬ Enabled (enter i) s := by
  simp only [Enabled, enter]
  action_simp
  rintro ⟨s'', t, ⟨⟨⟨-, hturn⟩, -⟩, -⟩⟩
  exact h (ht.symm.trans hturn)

/-- Inside the region, `enter i`'s enabledness *is* its guard: after unfolding,
`enabled_guard` + `enabled_seq` + `enabled_update` close it. -/
theorem enter_enabled_iff_guard {n : Nat} (i : Fin n) (s : St n) :
    Enabled (enter i) s ↔ s.pc i = Pc.wait ∧ s.turn = i := by
  simp [enter]

end Tests.Enabled
