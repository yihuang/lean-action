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

The enter direction is proved twice: once with the rank theorem
(`eventually_enter1`/`leadsTo_enter1`) and once with the rank-free `WF1` rule
(`leadsTo_enter1_wf1`). The leave direction genuinely needs the rank + safety
pair, which is why the rank machinery stays.
-/
import LeanAction
import Examples.Mutex

open LeanAction

namespace Examples.MutexLiveness

open Examples.Mutex (St M next steps1 steps2 req1 enter1 exit1 req2 enter2 exit2)

/-- Process 1 is waiting and holds the turn, and process 2 is not in the critical
section. -/
def Region (s : St) : Prop := s.pc1 = 1 ∧ s.turn = 1 ∧ s.pc2 ≤ 1

/-- Variant: `1` until process 1 is in the critical section, `0` afterwards. -/
def rank (s : St) : Nat := if s.pc1 = 2 then 0 else 1

theorem rank_le_one (s : St) : rank s ≤ 1 := by
  unfold rank; split <;> omega

theorem rank_eq_zero_iff {s : St} : rank s = 0 ↔ s.pc1 = 2 := by
  unfold rank; split <;> simp_all

theorem rank_pos_iff {s : St} : rank s > 0 ↔ s.pc1 ≠ 2 := by
  unfold rank; split <;> simp_all

/-! ## The region is stable until the goal is reached -/

/-- Process 1's **own** contribution: from the region its steps stay in the region
or take the critical section (its guarantee). -/
theorem region_steps1 {s s' : St} (hs : Region s) (h : rel steps1 s s') :
    Region s' ∨ s'.pc1 = 2 := by
  simp only [steps1, req1, enter1, exit1, Region] at hs h ⊢
  action_simp
  grind

/-- The **environment interface** process 1 is allowed to assume: process 2's
steps never leave the region. This is the rely/guarantee obligation for the
environment, stated without any reference to `steps1`. -/
theorem region_steps2 {s s' : St} (hs : Region s) (h : rel steps2 s s') : Region s' := by
  simp only [steps2, req2, enter2, exit2, Region] at hs h ⊢
  action_simp
  grind

/-- As long as process 1 has not entered the critical section, it stays in the
region. Same statement as a hand-rolled prefix induction would give, but the
six-way case analysis is replaced by the two interface lemmas above — process 1's
own guarantee (`region_steps1`) and the environment's rely (`region_steps2`) — with
`relyGuarantee_until` doing the induction. -/
theorem region_until_goal (b : Behavior St) (hbeh : IsBehavior M b) (h0 : Region (b 0)) :
    ∀ n, (∀ j, j ≤ n → (b j).pc1 ≠ 2) → Region (b n) := by
  have hbeh' : ∀ n, rel (steps1 <|> steps2) (b n) (b (n + 1)) := by
    intro n
    have := hbeh n
    rwa [M, Module.next] at this
  exact relyGuarantee_until hbeh'
    (fun s s' hs h => region_steps1 hs h)
    (fun s s' hs h => region_steps2 hs h)
    h0

/-! ## The stepwise region obligations (shared by both liveness routes)

`region_steps1`/`region_steps2` are one-step facts. WF1's shape packages them as
"every `M.next` step either reaches the goal or keeps `Region ∧ ¬goal`", which is
exactly the hypothesis the fused rank rule `leadsTo_of_rank_region` also needs. -/

/-- Progress: an `enter1` step from the region reaches the goal. -/
theorem wf1_prog : ∀ (s s' : St), Region s → ¬ s.pc1 = 2 → rel enter1 s s' → s'.pc1 = 2 := by
  intro s s' hs hq h
  simp only [Region] at hs
  simp only [enter1] at h
  action_simp
  grind

/-- Environment: from the region, every module step either reaches the goal or
stays in `Region ∧ ¬goal`. Reuses the two interface lemmas the R/G proof already
had (`region_steps1`/`region_steps2`). -/
theorem wf1_env : ∀ (s s' : St), Region s → ¬ s.pc1 = 2 → rel M.next s s' →
    (Region s' ∧ ¬ s'.pc1 = 2) ∨ s'.pc1 = 2 := by
  intro s s' hs _ h
  have hbeh : rel (steps1 <|> steps2) s s' := by
    simpa [M, next] using h
  rw [rel_orElse] at hbeh
  rcases hbeh with h1 | h2
  · rcases region_steps1 hs h1 with hreg | hgoal
    · exact Or.inl ⟨hreg, fun hc => by have h1' := hreg.1; omega⟩
    · exact Or.inr hgoal
  · have hreg := region_steps2 hs h2
    exact Or.inl ⟨hreg, fun hc => by have h1' := hreg.1; omega⟩

/-- Enabledness, now stated with `Enabled` and closed by the `enabled_*` simp
set (the guard of `enter1` *is* the first two conjuncts of `Region`). -/
theorem wf1_enabled : ∀ (s : St), Region s → ¬ s.pc1 = 2 → Enabled enter1 s := by
  intro s hs _
  simp only [Region] at hs
  simpa [enter1] using And.intro hs.1 hs.2.1

/-! ## Liveness of process 1 -/

/-- **Liveness, rank route.** A direct instance of the library's fused rule
`leadsTo_of_rank_region`: `wf1_env` — the *stepwise* stability of
`Region ∧ ¬goal` — is shared with the WF1 route below, and the manual
`by_cases`/contradiction wrapper is gone (the library discharges the prefix
induction once). `region_until_goal` above is the explicit
`relyGuarantee_until` form of the same prefix fact. -/
theorem leadsTo_enter1 (b : Behavior St) (hbeh : IsBehavior M b)
    (hfair : WeakFair enter1 b) : LeadsTo Region (fun s => s.pc1 = 2) b :=
  leadsTo_of_rank_region (T := M.next) (r := (· < ·)) Nat.lt_wfRel.wf
    (fun _ _ _ => Nat.lt_trans) (μ := rank) hbeh hfair wf1_env
    (hreg := fun s hs _ => hs)
    (hdec := by
      intro s s' _ hq _
      have hpos : rank s > 0 := rank_pos_iff.mpr hq
      have hs : rank s = 1 := by have := rank_le_one s; omega
      have hs' : rank s' ≤ 1 := rank_le_one s'
      omega)
    (hprog := by
      intro s hs hq s' hstep
      have hs1 : rank s = 1 := by
        have := rank_le_one s
        have := rank_pos_iff.mpr hq
        omega
      have hpc : s'.pc1 = 2 := by
        simp only [Region] at hs
        simp only [enter1] at hstep
        action_simp
        grind
      rw [rank_eq_zero_iff.mpr hpc, hs1]
      omega)
    (henab := by
      intro s hs _
      simp only [Region] at hs
      simpa [enter1] using And.intro hs.1 hs.2.1)

/-- The `Eventually` form: from the region, process 1 reaches the critical
section. -/
theorem eventually_enter1 (b : Behavior St) (hbeh : IsBehavior M b) (h0 : Region (b 0))
    (hfair : WeakFair enter1 b) : ∃ N, (b N).pc1 = 2 :=
  eventually_of_leadsTo (leadsTo_enter1 b hbeh hfair) h0

/-! ## The same `LeadsTo`, via the WF1 rule

The same three obligations go straight into `leadsTo_of_wf1` — no measure, no
region machinery. The rank route above additionally needed `rank`/`hdec`/`hprog`;
this one needs none. -/

/-- **The WF1 route to mutex liveness.** Same conclusion as `leadsTo_enter1`, but
the proof is three interface lemmas plus the rule — no rank, no prefix induction,
no contradiction wrapper. -/
theorem leadsTo_enter1_wf1 (b : Behavior St) (hbeh : IsBehavior M b)
    (hfair : WeakFair enter1 b) : LeadsTo Region (fun s => s.pc1 = 2) b :=
  leadsTo_of_wf1 (M := M) (A := enter1) (P := Region) (Q := fun s => s.pc1 = 2)
    hbeh hfair wf1_prog wf1_env wf1_enabled

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
  unfold csRank; split <;> omega

theorem csRank_pos_iff {s : St} : csRank s > 0 ↔ s.pc1 = 2 := by
  unfold csRank; split <;> simp_all

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
    have hs' : csRank s' = 0 := by simp [csRank, hpc]
    omega
  have henabled : ∀ s, InCS s → csRank s > 0 → Enabled exit1 s := by
    intro s hs _
    simpa [exit1] using hs.1
  refine (leadsTo_zero_of_weakFair_inv (M := M) (A := exit1) (μ := csRank) (I := InCS)
    hbeh hI hdec hA henabled hfair).mono (fun _ _ => trivial) ?_
  intro s hs
  by_cases h : s.pc1 = 2
  · have : csRank s = 1 := by simp [csRank, h]
    omega
  · exact h

end Examples.MutexLiveness
