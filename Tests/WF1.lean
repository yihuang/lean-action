/-
Tests.WF1
=======

Regression tests for the WF1-style leads-to rule (`leadsTo_of_wf1`, now in
`LeanAction.Liveness`), put to work on the mutex protocol.

Claim under test: WF1 turns "P eventually leads to Q via action A under weak
fairness" into three one-step obligations that the existing `action_simp; …`
pipeline discharges. On the mutex, the whole `eventually` + rank argument +
`LeadsTo` repackaging collapses into three small lemmas, stated for an arbitrary
node `i`.
-/
import LeanAction
import Examples.Mutex
import Examples.MutexLiveness

open LeanAction

namespace Tests.WF1

/-! ## WF1 on the mutex: `LeadsTo (Region i) (pc i = cs)` with no rank

Compare with `Examples/MutexLiveness.lean`: `eventually_enter` needed a rank, a
region bookkeeping, and a separate `LeadsTo` repackaging step. Here the `LeadsTo`
form comes out directly from the three obligations. -/

open Examples.Mutex (Pc St M next req enter exit steps setPc release)
open Examples.MutexLiveness (Region others rel_next_iff)

/-- Progress: an `enter i` step from the region reaches the goal. -/
theorem wf1_prog {n : Nat} (i : Fin n) :
    ∀ s s', Region i s → ¬ s.pc i = Pc.cs → rel (enter i) s s' → s'.pc i = Pc.cs := by
  intro s s' hs _ h
  simp only [Region] at hs
  simp only [enter] at h
  action_simp
  simp_all [setPc, upd.eq_1]

/-- Environment: from the region, every module step either reaches the goal or
stays in `Region i ∧ ¬goal`. Reuses the two interface lemmas the R/G example
already had. -/
theorem wf1_env {n : Nat} (i : Fin n) :
    ∀ s s', Region i s → ¬ s.pc i = Pc.cs → rel (next (n := n)) s s' →
      (Region i s' ∧ ¬ s'.pc i = Pc.cs) ∨ s'.pc i = Pc.cs := by
  intro s s' hs _ h
  rcases (rel_next_iff i).mp h with h | h
  · rcases Examples.MutexLiveness.region_steps_own i hs h with hreg | hgoal
    · exact Or.inl ⟨hreg, fun hc => by simp only [Region] at hreg; grind⟩
    · exact Or.inr hgoal
  · have hreg := Examples.MutexLiveness.region_steps_others i hs h
    exact Or.inl ⟨hreg, fun hc => by simp only [Region] at hreg; grind⟩

/-- Enabledness: inside the region, `enter i` is enabled (its guard is `Region
i`'s first two conjuncts). -/
theorem wf1_enabled {n : Nat} (i : Fin n) :
    ∀ s, Region i s → ¬ s.pc i = Pc.cs → Enabled (enter i) s := by
  intro s hs _
  simp only [Region] at hs
  simpa [enter] using And.intro hs.1 hs.2.1

/-- **The WF1 route to mutex liveness.** Same conclusion as
`Examples/MutexLiveness.leadsTo_enter`, but the proof is three interface lemmas
plus the rule — no rank, no prefix induction. -/
theorem leadsTo_enter_wf1 {n : Nat} (i : Fin n) (b : Behavior (St n))
    (hbeh : IsBehavior (M n) b) (hfair : WeakFair (enter i) b) :
    LeadsTo (Region i) (fun s => s.pc i = Pc.cs) b :=
  leadsTo_of_wf1 (M := M n) (A := enter i) (P := Region i) (Q := fun s => s.pc i = Pc.cs)
    hbeh hfair (wf1_prog i) (wf1_env i) (wf1_enabled i)

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
  leadsTo_of_rank_region (T := TickM.next) (A := Tick) (r := (· < ·))
    Nat.lt_wfRel.wf (fun _ _ _ => Nat.lt_trans)
    (P := fun _ => True) (Q := fun n => n ≥ 2) (I := fun _ => True) (μ := tickRank)
    hbeh hfair
    (by
      intro s s' _ _ h
      simp only [TickM, Tick, rel_update] at h
      rw [h]; simp only [true_and]; omega)
    (by intro s _ _; trivial)
    (by
      intro s s' _ hq h
      simp only [TickM, Tick, rel_update] at h
      rw [h]; simp only [tickRank] at hq ⊢; omega)
    (by
      intro s _ hq s' h
      simp only [Tick, rel_update] at h
      rw [h]; simp only [tickRank] at hq ⊢; omega)
    (by intro s _ _; exact ⟨s + 1, rfl⟩)

end Tests.WF1
