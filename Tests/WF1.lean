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

/-! ## `⟨A⟩`-WF1 for a stuttering progress action

Plain WF1 requires *every* `A`-step to reach `Q`; if `A` may stutter (here:
bump **or** skip) that obligation is false on the `skip` branch.
`leadsTo_of_wf1_nonStutter` takes fairness for `nonStutter A` instead. -/

def bumpOrSkip : Action Nat := update (· + 1) <|> skip

def CountM : Module Nat := ⟨fun _ => true, bumpOrSkip⟩

theorem count_prog : ∀ s s', s = 2 → ¬ s ≥ 3 → rel bumpOrSkip s s' → s' ≠ s → s' ≥ 3 := by
  intro s s' hs hq h hne
  subst hs
  simp only [bumpOrSkip] at h
  rw [rel_orElse] at h
  rcases h with h | h
  · simp only [rel_update] at h; rw [h]; omega
  · simp only [rel_skip] at h; exact absurd h hne

theorem count_env : ∀ s s', s = 2 → ¬ s ≥ 3 → rel CountM.next s s' →
    (s' = 2 ∧ ¬ s' ≥ 3) ∨ s' ≥ 3 := by
  intro s s' hs hq h
  subst hs
  simp only [CountM, bumpOrSkip] at h
  rw [rel_orElse] at h
  rcases h with h | h
  · simp only [rel_update] at h; rw [h]; exact Or.inr (by omega)
  · simp only [rel_skip] at h; exact Or.inl ⟨h, by omega⟩

theorem count_enabled : ∀ s, s = 2 → ¬ s ≥ 3 → Enabled (nonStutter bumpOrSkip) s := by
  intro s hs hq
  subst hs
  refine ⟨3, ?_, by omega⟩
  simp only [bumpOrSkip]
  exact Or.inl rfl

theorem count_wf1 (b : Behavior Nat) (hbeh : IsBehavior CountM b)
    (hfair : WeakFair (nonStutter bumpOrSkip) b) :
    LeadsTo (fun n => n = 2) (fun n => n ≥ 3) b :=
  leadsTo_of_wf1_nonStutter (M := CountM) (A := bumpOrSkip) hbeh hfair
    count_prog count_env count_enabled

/-! ## `leadsTo_of_wf1_seq`: an arbitrary step relation

The sequence-level rule mentions no `Module`; `T` is just a relation, which is
the shape a *projected* interleaved behavior has. -/

theorem count_wf1_seq (b : Behavior Nat)
    (hstep : ∀ n, b (n + 1) = b n ∨ b (n + 1) = b n + 1)
    (hfair : WeakFair (update (· + 1)) b) :
    LeadsTo (fun n => n = 2) (fun n => n ≥ 3) b :=
  leadsTo_of_wf1_seq (T := ofRel fun s s' => s' = s ∨ s' = s + 1)
    (A := update (· + 1))
    (fun n => by simpa [rel_ofRel] using hstep n) hfair
    (by intro s s' hs hq h; subst hs; simp only [rel_update] at h; rw [h]; omega)
    (by
      intro s s' hs hq h
      subst hs
      simp only [rel_ofRel] at h
      rcases h with h | h
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr (by omega))
    (by intro s hs hq; subst hs; exact ⟨3, rfl⟩)

/-! ## `LeadsTo.cancel` -/

/-- Cancellation: with a disjunctive target, once the second branch is reachable
the goal collapses. (This is a different split from the `by_cases` inside the
fairness rules — see the docstring of `LeadsTo.cancel`.) -/
theorem cancel_demo (b : Behavior Nat)
    (h : LeadsTo (fun _ => True) (fun n => n = 0 ∨ n = 2) b)
    (h' : LeadsTo (fun n => n = 2) (fun n => n = 0) b) :
    LeadsTo (fun _ => True) (fun n => n = 0) b :=
  LeadsTo.cancel h h'

/-! ## `leadsTo_of_rank_region`: the fused rank rule, no call-site `by_cases` -/

/-- A stuttering-free one-step system: `n ↦ n + 1`. -/
def Tick : Action Nat := update (· + 1)
def TickM : Module Nat := ⟨fun _ => true, Tick⟩
def tickRank (n : Nat) : Nat := 2 - n

/-- The fused rule on a *stuttering-free* system (the companion of `count_wf1`,
which is about a progress action that may stutter): the goal-or-stay split is
carried by the stepwise stability `hstab`, and the `by_cases` stays inside the
library rule. -/
theorem tick_reaches (b : Behavior Nat) (hbeh : IsBehavior TickM b)
    (hfair : WeakFair Tick b) : LeadsTo (fun _ => True) (fun n => n ≥ 2) b :=
  leadsTo_of_rank_region (T := TickM.next) (A := Tick) (P := fun _ => True)
    (Q := fun n => n ≥ 2) (I := fun _ => True) (μ := tickRank) hbeh hfair
    (by
      intro s s' _ hq h
      simp only [TickM, Tick, rel_update] at h
      rw [h]; simp only [true_and]; omega)
    (by intro s _ _ _; trivial)
    (by
      intro s s' _ hpos h
      simp only [TickM, Tick, rel_update] at h
      rw [h]; simp only [tickRank] at hpos ⊢; omega)
    (by
      intro s _ hpos s' h
      simp only [Tick, rel_update] at h
      rw [h]; simp only [tickRank] at hpos ⊢; omega)
    (by intro s _ _; exact ⟨s + 1, rfl⟩)
    (by intro s hz; simp only [tickRank] at hz; omega)

end Tests.WF1
