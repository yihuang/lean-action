/-
Tests.WF1
=======

Regression tests for the WF1-style leads-to rule (`leadsTo_of_wf1`, now in
`LeanAction.Liveness`), put to work on the mutex protocol.

Claim under test: WF1 turns "P eventually leads to Q via action A under weak
fairness" into three one-step obligations that the existing
`action_simp; grind` pipeline discharges. On the mutex, the whole
`eventually_enter1` + rank argument + `LeadsTo` repackaging collapses into
three small lemmas.
-/
import LeanAction
import Examples.Mutex
import Examples.MutexLiveness

open LeanAction

namespace Tests.WF1

/-! ## WF1 on the mutex: `LeadsTo Region (pc1 = 2)` with no rank

Compare with `Examples/MutexLiveness.lean`: `eventually_enter1` needed a
by-contradiction wrapper, a rank, region bookkeeping, and a separate
`leadsTo_enter1` repackaging step. Here the LeadsTo form comes out directly. -/

open Examples.Mutex (St M next steps1 steps2 req1 enter1 exit1 req2 enter2 exit2)
open Examples.MutexLiveness (Region)

/-- Progress: an `enter1` step from the region reaches the goal. -/
theorem wf1_prog : ∀ (s s' : St), Region s → ¬ s.pc1 = 2 → rel enter1 s s' → s'.pc1 = 2 := by
  intro s s' hs hq h
  simp only [Region] at hs
  simp only [enter1] at h
  action_simp
  grind

/-- Environment: from the region, every module step either reaches the goal or
stays in `Region ∧ ¬goal`. Reuses the two interface lemmas the R/G example
already had (`region_steps1`/`region_steps2`). -/
theorem wf1_env : ∀ (s s' : St), Region s → ¬ s.pc1 = 2 → rel M.next s s' →
    (Region s' ∧ ¬ s'.pc1 = 2) ∨ s'.pc1 = 2 := by
  intro s s' hs _ h
  have hbeh : rel (steps1 <|> steps2) s s' := by
    simpa [M, next] using h
  rw [rel_orElse] at hbeh
  rcases hbeh with h1 | h2
  · rcases Examples.MutexLiveness.region_steps1 hs h1 with hreg | hgoal
    · exact Or.inl ⟨hreg, fun hc => by have h1' := hreg.1; omega⟩
    · exact Or.inr hgoal
  · have hreg := Examples.MutexLiveness.region_steps2 hs h2
    exact Or.inl ⟨hreg, fun hc => by have h1' := hreg.1; omega⟩

/-- Enabledness: inside the region, `enter1` is enabled (its guard is `Region`'s
first two conjuncts). -/
theorem wf1_enabled : ∀ (s : St), Region s → ¬ s.pc1 = 2 → Enabled enter1 s := by
  intro s hs _
  simp only [Region] at hs
  show ∃ s', rel enter1 s s'
  refine ⟨{ s with pc1 := 2 }, ?_⟩
  simp only [enter1]
  action_simp
  grind

/-- **The WF1 route to mutex liveness.** Same conclusion as
`Examples.MutexLiveness.leadsTo_enter1`, but the proof is three interface
lemmas plus the rule — no rank, no prefix induction, no contradiction wrapper. -/
theorem leadsTo_enter1_wf1 (b : Behavior St) (hbeh : IsBehavior M b)
    (hfair : WeakFair enter1 b) : LeadsTo Region (fun s => s.pc1 = 2) b :=
  leadsTo_of_wf1 (M := M) (A := enter1) (P := Region) (Q := fun s => s.pc1 = 2)
    hbeh hfair wf1_prog wf1_env wf1_enabled

end Tests.WF1
