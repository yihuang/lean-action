/-
Examples.MutexLiveness
======================

Liveness for the shared-memory protocol of `Examples.Mutex`: if process 1 is
waiting and holds the turn, then under weak fairness for `enter1` it eventually
enters the critical section.

The interesting part is that the natural variant (`1` until process 1 is in the
critical section, `0` afterwards) is **not** globally non-increasing: leaving the
critical section sends `pc1` back to `0` and the variant back up to `1`. What
makes the argument go through is that the variant is only required to behave
while it is positive — `eventually_zero_of_weakFair_inv` takes an invariant
region for exactly that purpose, and the region here is stable until the goal is
reached.

This is also where the guard on `req1`/`req2` matters: without it a process could
"re-request" from inside the critical section, which safety does not notice but
which destroys the stability of the region.
-/
import LeanAction
import Examples.Mutex

open LeanAction

namespace Examples.MutexLiveness

open Examples.Mutex (St M next req1 enter1 exit1 req2 enter2 exit2)

/-- Process 1 is waiting and holds the turn, and process 2 is not in the critical
section. -/
def Region (s : St) : Prop := s.pc1 = 1 ∧ s.turn = 1 ∧ s.pc2 ≤ 1

/-- Variant: `1` until process 1 is in the critical section, `0` afterwards. -/
def rank (s : St) : Nat := if s.pc1 = 2 then 0 else 1

theorem rank_le_one (s : St) : rank s ≤ 1 := by
  by_cases h : s.pc1 = 2 <;> simp [rank, h]

theorem rank_eq_zero_iff {s : St} : rank s = 0 ↔ s.pc1 = 2 := by
  by_cases h : s.pc1 = 2 <;> simp [rank, h]

theorem rank_pos_iff {s : St} : rank s > 0 ↔ s.pc1 ≠ 2 := by
  by_cases h : s.pc1 = 2 <;> simp [rank, h]

/-! ## The region is stable until the goal is reached -/

/-- As long as process 1 has not entered the critical section, it stays in the
region. The only enabled steps from the region are `req2` (which keeps the
region) and `enter1` (which is exactly the goal). -/
theorem region_until_goal (b : Behavior St) (hbeh : IsBehavior M b) (h0 : Region (b 0)) :
    ∀ n, (∀ j, j ≤ n → (b j).pc1 ≠ 2) → Region (b n) := by
  intro n
  induction n with
  | zero => intro _; exact h0
  | succ n ih =>
    intro hpre
    have hRn : Region (b n) := ih fun j hj => hpre j (Nat.le_trans hj (Nat.le_succ n))
    have hne : (b (n + 1)).pc1 ≠ 2 := hpre (n + 1) (Nat.le_refl _)
    have hstep := hbeh n
    simp only [M, next, req1, enter1, exit1, req2, enter2, exit2, Region] at hRn hstep ⊢
    action_simp
    grind

/-! ## Liveness of process 1 -/

/-- **Liveness.** From the region, weak fairness for `enter1` makes process 1
enter the critical section. -/
theorem eventually_enter1 (b : Behavior St) (hbeh : IsBehavior M b) (h0 : Region (b 0))
    (hfair : WeakFair enter1 b) : ∃ N, (b N).pc1 = 2 := by
  by_cases hgoal : ∃ N, (b N).pc1 = 2
  · exact hgoal
  · -- the critical section is never entered, so the region is maintained forever
    have hne : ∀ j, (b j).pc1 ≠ 2 := fun j hj => hgoal ⟨j, hj⟩
    have hI : ∀ n, rank (b n) > 0 → Region (b n) := fun n _ =>
      region_until_goal b hbeh h0 n fun j _ => hne j
    -- no step increases the rank (the rank is at most one)
    have hdec : ∀ s s', Region s → rank s > 0 → rel M.next s s' → rank s' ≤ rank s := by
      intro s s' _ hpos _
      have hs : rank s = 1 := by have := rank_le_one s; omega
      have hs' : rank s' ≤ 1 := rank_le_one s'
      omega
    -- `enter1` strictly decreases the rank inside the region
    have hA : ∀ s, Region s → rank s > 0 → ∀ s', rel enter1 s s' → rank s' < rank s := by
      intro s hs hpos s' hstep
      have hs1 : rank s = 1 := by have := rank_le_one s; omega
      have hpc : s'.pc1 = 2 := by
        simp only [Region] at hs
        simp only [enter1] at hstep
        action_simp
        grind
      rw [rank_eq_zero_iff.mpr hpc, hs1]
      omega
    -- and it is enabled inside the region
    have henabled : ∀ s, Region s → rank s > 0 → ∃ s', rel enter1 s s' := by
      intro s hs _
      refine ⟨{ s with pc1 := 2 }, ?_⟩
      simp only [Region] at hs
      simp only [enter1]
      action_simp
      grind
    obtain ⟨N, -, hz⟩ := eventually_zero_of_weakFair_inv (M := M) (A := enter1)
      (μ := rank) (I := Region) hbeh hI hdec hA henabled hfair 0
    exact absurd (rank_eq_zero_iff.mp hz) (hne N)

/-- The `LeadsTo` form: at any time at which process 1 is waiting with the turn,
it eventually enters the critical section. -/
theorem leadsTo_enter1 (b : Behavior St) (hbeh : IsBehavior M b)
    (hfair : WeakFair enter1 b) : LeadsTo Region (fun s => s.pc1 = 2) b := by
  intro n hn
  have hbeh' : IsBehavior M fun k => b (n + k) := fun k => hbeh (n + k)
  have hfair' : WeakFair enter1 fun k => b (n + k) := by
    intro k hen
    have hen' : ∀ m, n + k ≤ m → ∃ s', rel enter1 (b m) s' := by
      intro m hm
      have hn_le : n ≤ m := by omega
      simpa [Nat.add_sub_of_le hn_le] using hen (m - n) (by omega)
    obtain ⟨M, hM, hstep⟩ := hfair (n + k) hen'
    have h1 : n + (M - n) = M := by omega
    have h2 : n + (M - n + 1) = M + 1 := by omega
    exact ⟨M - n, by omega, by simpa [TakesStep, h1, h2] using hstep⟩
  obtain ⟨N, hN⟩ := eventually_enter1 (fun k => b (n + k)) hbeh' (by simpa using hn) hfair'
  exact ⟨n + N, Nat.le_add_right n N, hN⟩

/-! ## The complementary direction: leaving the critical section

This one consumes the *safety* layer: the invariant "in the critical section
implies holding the turn" comes from `Mutex.inv_step` through
`always_of_preserves`, and it is what makes the variant behave (without it, the
other process could not be ruled out). -/

/-- Variant: `1` while process 1 is in the critical section, `0` otherwise. -/
def csRank (s : St) : Nat := if s.pc1 = 2 then 1 else 0

/-- Being in the critical section is part of the safety invariant: it implies
holding the turn. -/
def InCS (s : St) : Prop := s.pc1 = 2 ∧ s.turn = 1

theorem csRank_le_one (s : St) : csRank s ≤ 1 := by
  by_cases h : s.pc1 = 2 <;> simp [csRank, h]

theorem csRank_pos_iff {s : St} : csRank s > 0 ↔ s.pc1 = 2 := by
  by_cases h : s.pc1 = 2 <;> simp [csRank, h]

/-- **Liveness of leaving.** From any state in which process 1 is in the critical
section, weak fairness for `exit1` eventually takes it out. -/
theorem leadsTo_exit1 (b : Behavior St) (hbeh : IsBehavior M b)
    (hinit : Mutex.init (b 0)) (hfair : WeakFair exit1 b) :
    LeadsTo (fun s => s.pc1 = 2) (fun s => s.pc1 ≠ 2) b := by
  -- the safety invariant holds at every time, and it gives `InCS` on request
  have hAlways : Always Mutex.inv b :=
    always_of_preserves hbeh Mutex.inv_step (Mutex.inv_init (b 0) hinit)
  have hI : ∀ n, csRank (b n) > 0 → InCS (b n) := by
    intro n hpos
    have hpc : (b n).pc1 = 2 := csRank_pos_iff.mp hpos
    exact ⟨hpc, (hAlways n).1 hpc⟩
  have hdec : ∀ s s', InCS s → csRank s > 0 → rel M.next s s' → csRank s' ≤ csRank s := by
    intro s s' _ hpos _
    have hs : csRank s = 1 := by have := csRank_le_one s; omega
    have hs' : csRank s' ≤ 1 := csRank_le_one s'
    omega
  have hA : ∀ s, InCS s → csRank s > 0 → ∀ s', rel exit1 s s' → csRank s' < csRank s := by
    intro s hs hpos s' hstep
    have hs1 : csRank s = 1 := by have := csRank_le_one s; omega
    have hpc : s'.pc1 ≠ 2 := by
      obtain ⟨hpc1, -⟩ := hs
      simp only [exit1] at hstep
      action_simp
      grind
    have hs' : csRank s' = 0 := by
      by_cases h : s'.pc1 = 2
      · exact absurd h hpc
      · simp [csRank, h]
    omega
  have henabled : ∀ s, InCS s → csRank s > 0 → ∃ s', rel exit1 s s' := by
    intro s hs _
    refine ⟨{ s with pc1 := 0, turn := 2 }, ?_⟩
    obtain ⟨hpc1, -⟩ := hs
    simp only [exit1]
    action_simp
    grind
  refine (leadsTo_zero_of_weakFair_inv (M := M) (A := exit1) (μ := csRank) (I := InCS)
    hbeh hI hdec hA henabled hfair).mono (fun _ _ => trivial) ?_
  intro s hs
  by_cases h : s.pc1 = 2
  · have : csRank s = 1 := by simp [csRank, h]
    omega
  · exact h

end Examples.MutexLiveness
