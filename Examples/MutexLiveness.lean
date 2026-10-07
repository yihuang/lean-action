/-
Examples.MutexLiveness
======================

Liveness for the N-node token protocol of `Examples.Mutex`: if node `i` is
waiting and holds the token, then under weak fairness for `enter i` it
eventually enters the critical section.

The two-process argument generalizes verbatim; what changes is the split of a
step into "node `i`'s own step" (`steps i`) and "a step of some other node"
(`others i`). `rel_next_iff` is that split, and it is exactly what
`relyGuarantee_until` consumes — the environment interface for node `i` is
"every `j ≠ i` respects the region".

As before:
* the natural rank (`1` until entering, `0` afterwards) is **not** globally
  non-increasing — leaving the critical section sends it back up — so the
  region-restricted rule is needed;
* the `enter` direction is proved twice: with the fused rank rule
  `leadsTo_of_rank_wf`/`leadsTo_of_rank_region` and with the rank-free
  `leadsTo_of_wf1`, sharing the
  same three one-step interface lemmas;
* the `leave` direction consumes safety (`Mutex.inv`), and the `guarded` `req`
  is what makes the region stable.
-/
import LeanAction
import Examples.Mutex

open LeanAction

namespace Examples.MutexLiveness

open Examples.Mutex (Pc St M next init inv inv_step inv_init req enter exit steps setPc release)

/-! ## The environment interface: own steps vs. the other nodes -/

/-- The steps of every node other than `i` (the environment of node `i`). -/
def others {n : Nat} (i : Fin n) : Action (St n) :=
  choiceAll (fun j : {j : Fin n // j ≠ i} => steps j.1)

/-- `next` splits into node `i`'s own step and the environment's steps. -/
theorem rel_next_iff {n : Nat} (i : Fin n) {s s' : St n} :
    rel (next (n := n)) s s' ↔ rel (steps i) s s' ∨ rel (others i) s s' := by
  simp only [next, others, rel_choiceAll]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst hji; exact Or.inl hj
    · exact Or.inr ⟨⟨j, hji⟩, hj⟩
  · rintro (h | ⟨⟨j, _⟩, hj⟩)
    · exact ⟨i, h⟩
    · exact ⟨j, hj⟩

/-- **The region**: node `i` is waiting, holds the token, and no *other* node is
in the critical section. -/
def Region {n : Nat} (i : Fin n) (s : St n) : Prop :=
  s.pc i = Pc.wait ∧ s.turn = i ∧ ∀ j, j ≠ i → s.pc j ≠ Pc.cs

/-- Node `i`'s own contribution: from the region, its steps stay in the region or
take the critical section. This is its *guarantee*. -/
theorem region_steps_own {n : Nat} (i : Fin n) {s s' : St n}
    (hs : Region i s) (h : rel (steps i) s s') :
    Region i s' ∨ s'.pc i = Pc.cs := by
  simp only [steps, req, enter, exit, Region] at hs h ⊢
  action_simp
  simp_all [setPc, upd.eq_1]

/-- The **environment interface** node `i` is allowed to assume: a step of any
other node never leaves the region. This is the rely/guarantee obligation for the
environment, stated without reference to `steps i`. -/
theorem region_steps_others {n : Nat} (i : Fin n) {s s' : St n}
    (hs : Region i s) (h : rel (others i) s s') : Region i s' := by
  simp only [Region] at hs ⊢
  simp only [others, rel_choiceAll] at h
  obtain ⟨⟨j, hji⟩, hj⟩ := h
  simp only [steps, req, enter, exit] at hj
  action_simp
  rcases hj with h | h | h
  all_goals
    rcases h with ⟨t, ⟨hp, ht⟩, hs'⟩
    subst t
    subst s'
    simp_all [setPc, upd.eq_1]
    try grind

/-- As long as node `i` has not entered the critical section, it stays in the
region. The six-way case analysis of the `Nat` version is replaced by the two
interface lemmas above — node `i`'s guarantee (`region_steps_own`) and the
environment's rely (`region_steps_others`) — with `relyGuarantee_until` doing the
prefix induction. -/
theorem region_until_goal {n : Nat} (i : Fin n) (b : Behavior (St n))
    (hbeh : IsBehavior (M n) b) (h0 : Region i (b 0)) :
    ∀ m, (∀ j, j ≤ m → (b j).pc i ≠ Pc.cs) → Region i (b m) := by
  have hbeh' : ∀ m, rel (steps i <|> others i) (b m) (b (m + 1)) := by
    intro m
    exact (rel_next_iff i).mp (hbeh m)
  exact relyGuarantee_until hbeh'
    (fun s s' hs h => region_steps_own i hs h)
    (fun s s' hs h => region_steps_others i hs h)
    h0

/-! ## The stepwise obligations, shared by both liveness routes -/

/-- Progress: an `enter i` step from the region reaches the goal. -/
theorem wf1_prog {n : Nat} (i : Fin n) :
    ∀ s s', Region i s → ¬ s.pc i = Pc.cs → rel (enter i) s s' → s'.pc i = Pc.cs := by
  intro s s' hs _ h
  simp only [Region] at hs
  simp only [enter] at h
  action_simp
  simp_all [setPc, upd.eq_1]

/-- Environment: from the region, every module step either reaches the goal or
stays in `Region i ∧ ¬goal`. Reuses the two interface lemmas. -/
theorem wf1_env {n : Nat} (i : Fin n) :
    ∀ s s', Region i s → ¬ s.pc i = Pc.cs → rel (next (n := n)) s s' →
      (Region i s' ∧ ¬ s'.pc i = Pc.cs) ∨ s'.pc i = Pc.cs := by
  intro s s' hs _ h
  rcases (rel_next_iff i).mp h with h | h
  · rcases region_steps_own i hs h with hreg | hgoal
    · exact Or.inl ⟨hreg, fun hc => by simp only [Region] at hreg; grind⟩
    · exact Or.inr hgoal
  · have hreg := region_steps_others i hs h
    exact Or.inl ⟨hreg, fun hc => by simp only [Region] at hreg; grind⟩

/-- Enabledness: inside the region, `enter i`'s guard is exactly the first two
conjuncts of `Region i`. -/
theorem wf1_enabled {n : Nat} (i : Fin n) :
    ∀ s, Region i s → ¬ s.pc i = Pc.cs → Enabled (enter i) s := by
  intro s hs _
  simp only [Region] at hs
  simpa [enter] using And.intro hs.1 hs.2.1

/-! ## Liveness of node `i` (enter direction) -/

/-- Rank: `1` until node `i` is in the critical section, `0` afterwards. -/
def rank {n : Nat} (i : Fin n) (s : St n) : Nat := if s.pc i = Pc.cs then 0 else 1

theorem rank_le_one {n : Nat} (i : Fin n) (s : St n) : rank i s ≤ 1 := by
  unfold rank; split <;> omega

theorem rank_eq_zero_iff {n : Nat} {i : Fin n} {s : St n} :
    rank i s = 0 ↔ s.pc i = Pc.cs := by
  unfold rank; split <;> simp_all

theorem rank_pos_iff {n : Nat} {i : Fin n} {s : St n} :
    rank i s > 0 ↔ s.pc i ≠ Pc.cs := by
  unfold rank; split <;> simp_all

/-- **Liveness, rank route.** A direct instance of the library's fused rule
`leadsTo_of_rank_wf` (the `Nat`/`<` case of `leadsTo_of_rank_region`): the
*stepwise* stability `wf1_env` is shared with the
WF1 route below, and the `by_cases`/prefix bookkeeping is discharged once inside
the rule. -/
theorem leadsTo_enter {n : Nat} (i : Fin n) (b : Behavior (St n))
    (hbeh : IsBehavior (M n) b) (hfair : WeakFair (enter i) b) :
    LeadsTo (Region i) (fun s => s.pc i = Pc.cs) b :=
  leadsTo_of_rank_wf (T := next (n := n)) (A := enter i)
    (P := Region i) (Q := fun s => s.pc i = Pc.cs) (I := Region i) (μ := rank i)
    hbeh hfair (wf1_env i)
    (hreg := fun s hs _ => hs)
    (hdec := by
      intro s s' _ hq _
      have hpos : rank i s > 0 := rank_pos_iff.mpr hq
      have hs : rank i s = 1 := by have := rank_le_one i s; omega
      have hs' : rank i s' ≤ 1 := rank_le_one i s'
      omega)
    (hprog := by
      intro s hs hq s' hstep
      have hs1 : rank i s = 1 := by
        have := rank_le_one i s
        have := rank_pos_iff.mpr hq
        omega
      have hpc : s'.pc i = Pc.cs := wf1_prog i s s' hs hq hstep
      rw [rank_eq_zero_iff.mpr hpc, hs1]
      omega)
    (henab := by
      intro s hs hq
      exact wf1_enabled i s hs hq)

/-- The `Eventually` form: from the region, node `i` reaches the critical
section. -/
theorem eventually_enter {n : Nat} (i : Fin n) (b : Behavior (St n))
    (hbeh : IsBehavior (M n) b) (h0 : Region i (b 0))
    (hfair : WeakFair (enter i) b) : ∃ N, (b N).pc i = Pc.cs :=
  eventually_of_leadsTo (leadsTo_enter i b hbeh hfair) h0

/-- **The WF1 route to the same `LeadsTo`.** No measure, no region machinery:
three interface lemmas plus the rule. -/
theorem leadsTo_enter_wf1 {n : Nat} (i : Fin n) (b : Behavior (St n))
    (hbeh : IsBehavior (M n) b) (hfair : WeakFair (enter i) b) :
    LeadsTo (Region i) (fun s => s.pc i = Pc.cs) b :=
  leadsTo_of_wf1 (M := M n) (A := enter i) (P := Region i) (Q := fun s => s.pc i = Pc.cs)
    hbeh hfair (wf1_prog i) (wf1_env i) (wf1_enabled i)

/-! ## The complementary direction: leaving the critical section

The safety layer is what makes this go through: "in the critical section implies
holding the token" comes from `Mutex.inv_step` through `always_of_preserves`, and
without it the other nodes' steps cannot be ruled out. -/

/-- Variant: `1` while node `i` is in the critical section, `0` otherwise. -/
def csRank {n : Nat} (i : Fin n) (s : St n) : Nat := if s.pc i = Pc.cs then 1 else 0

/-- Being in the critical section, together with holding the token. -/
def InCS {n : Nat} (i : Fin n) (s : St n) : Prop := s.pc i = Pc.cs ∧ s.turn = i

theorem csRank_le_one {n : Nat} (i : Fin n) (s : St n) : csRank i s ≤ 1 := by
  unfold csRank; split <;> omega

theorem csRank_pos_iff {n : Nat} {i : Fin n} {s : St n} :
    csRank i s > 0 ↔ s.pc i = Pc.cs := by
  unfold csRank; split <;> simp_all

/-- **Liveness of leaving.** From any state in which node `i` is in the critical
section, weak fairness for `exit i` eventually takes it out. -/
theorem leadsTo_exit {n : Nat} (i : Fin n) (b : Behavior (St n))
    (hbeh : IsBehavior (M n) b) (hinit : (init (n := n)) (b 0))
    (hfair : WeakFair (exit i) b) :
    LeadsTo (fun s => s.pc i = Pc.cs) (fun s => s.pc i ≠ Pc.cs) b := by
  -- the safety invariant holds at every time, and gives `InCS` on request
  have hAlways : Always (inv (n := n)) b :=
    always_of_preserves (M := M n) hbeh (inv_step (n := n)) (inv_init (b 0) hinit)
  have hI : ∀ m, csRank i (b m) > 0 → InCS i (b m) := by
    intro m hpos
    have hpc : (b m).pc i = Pc.cs := csRank_pos_iff.mp hpos
    exact ⟨hpc, hAlways m i hpc⟩
  have hdec : ∀ s s', InCS i s → csRank i s > 0 →
      rel (next (n := n)) s s' → csRank i s' ≤ csRank i s := by
    intro s s' _ hpos _
    have hs : csRank i s = 1 := by have := csRank_le_one i s; omega
    have hs' : csRank i s' ≤ 1 := csRank_le_one i s'
    omega
  have hA : ∀ s, InCS i s → csRank i s > 0 → ∀ s', rel (exit i) s s' →
      csRank i s' < csRank i s := by
    intro s hs hpos s' hstep
    have hs1 : csRank i s = 1 := by have := csRank_le_one i s; omega
    have hpc : s'.pc i = Pc.out := by
      simp only [exit] at hstep
      action_simp
      obtain ⟨t, ⟨hp, ht⟩, hs'⟩ := hstep
      subst t
      subst s'
      simp [release, upd.eq_1]
    have hs' : csRank i s' = 0 := by
      unfold csRank; rw [hpc]; rfl
    omega
  have henabled : ∀ s, InCS i s → csRank i s > 0 → Enabled (exit i) s := by
    intro s hs _
    simpa [exit] using hs.1
  refine (leadsTo_zero_of_weakFair_inv (M := M n) (A := exit i) (μ := csRank i)
    (I := InCS i) hbeh hI hdec hA henabled hfair).mono (fun _ _ => trivial) ?_
  intro s hs
  by_cases h : s.pc i = Pc.cs
  · have : csRank i s = 1 := by unfold csRank; rw [if_pos h]
    omega
  · exact h

end Examples.MutexLiveness
