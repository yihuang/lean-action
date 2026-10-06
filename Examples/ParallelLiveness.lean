/-
Examples.ParallelLiveness
=========================

Liveness of an interleaved system, by composition:

* each component is a counter whose environment may stutter, so it only makes
  progress under fairness;
* fairness for the *lifted* action transfers to the projected component;
* a projected step is either a component step or a stutter, which is exactly why
  the sequence-level rank theorem (`eventually_zero_of_seq`) is the right engine
  rather than the module-level one;
* the two component liveness results are combined by `interleave_leadsTo`, whose
  stability side conditions hold because both targets are monotone.
-/
import LeanAction

open LeanAction

namespace Examples.ParallelLiveness

/-- Increment. -/
def incr : Action Nat := update (· + 1)

/-- A counter whose environment may stutter. -/
def counter (init : Nat) : Module Nat := ⟨(fun n => n = init), incr <|> skip⟩

/-- Two independent counters running asynchronously. -/
def twoCounters : Module (Nat × Nat) := (counter 0).interleave (counter 1)

/-- Rank of the left component: distance to 3. -/
def μ3 (n : Nat) : Nat := 3 - n

/-- Rank of the right component: distance to 4. -/
def μ4 (n : Nat) : Nat := 4 - n

/-- A step of a counter either increments or stutters. -/
theorem counter_step {init : Nat} {s s' : Nat} (h : rel (counter init).next s s') :
    s' = s + 1 ∨ s' = s := by
  simp only [counter, incr] at h
  rw [rel_orElse] at h
  rcases h with h | h
  · exact Or.inl (by rw [rel_update] at h; exact h)
  · exact Or.inr (by rw [rel_skip] at h; exact h)

/-! ## Component liveness -/

/-- The left component eventually reaches 3, given weak fairness for the lifted
increment. -/
theorem left_live (b : Behavior (Nat × Nat)) (hbeh : IsBehavior twoCounters b)
    (hfair : WeakFair (liftLeft incr) b) :
    LeadsTo (fun _ : Nat => True) (fun n => n ≥ 3) (fun k => (b k).1) := by
  intro n _
  have hwf : WeakFair incr (fun k => (b k).1) := weakFair_fst_of_weakFair hfair
  have hdec : ∀ m, μ3 ((b m).1) > 0 → μ3 ((b (m + 1)).1) ≤ μ3 ((b m).1) := by
    intro m _
    rcases proj_fst_step hbeh m with hstut | hstep
    · rw [hstut]; exact Nat.le_refl _
    · rcases counter_step hstep with h | h
      · rw [h]; simp only [μ3]; omega
      · rw [h]; exact Nat.le_refl _
  have hA : ∀ m, μ3 ((b m).1) > 0 → rel incr ((b m).1) ((b (m + 1)).1) →
      μ3 ((b (m + 1)).1) < μ3 ((b m).1) := by
    intro m hpos hstep
    simp only [incr] at hstep
    rw [rel_update] at hstep
    rw [hstep]
    simp only [μ3] at hpos ⊢
    omega
  have henabled : ∀ m, μ3 ((b m).1) > 0 → ∃ s', rel incr ((b m).1) s' :=
    fun m _ => ⟨(b m).1 + 1, by simp only [incr, rel_update]⟩
  obtain ⟨N, hN, hz⟩ := eventually_zero_of_seq (A := incr) (I := fun _ : Nat => True)
    (μ := μ3) (b := fun k => (b k).1) (fun _ _ => trivial)
    (fun m _ h => hdec m h) (fun m _ hpos h => hA m hpos h) (fun m _ hpos => henabled m hpos) hwf n
  have hz' : 3 - (b N).1 = 0 := hz
  refine ⟨N, hN, ?_⟩
  show (b N).1 ≥ 3
  omega

/-- The right component eventually reaches 4. -/
theorem right_live (b : Behavior (Nat × Nat)) (hbeh : IsBehavior twoCounters b)
    (hfair : WeakFair (liftRight incr) b) :
    LeadsTo (fun _ : Nat => True) (fun n => n ≥ 4) (fun k => (b k).2) := by
  intro n _
  have hwf : WeakFair incr (fun k => (b k).2) := weakFair_snd_of_weakFair hfair
  have hdec : ∀ m, μ4 ((b m).2) > 0 → μ4 ((b (m + 1)).2) ≤ μ4 ((b m).2) := by
    intro m _
    rcases proj_snd_step hbeh m with hstut | hstep
    · rw [hstut]; exact Nat.le_refl _
    · rcases counter_step hstep with h | h
      · rw [h]; simp only [μ4]; omega
      · rw [h]; exact Nat.le_refl _
  have hA : ∀ m, μ4 ((b m).2) > 0 → rel incr ((b m).2) ((b (m + 1)).2) →
      μ4 ((b (m + 1)).2) < μ4 ((b m).2) := by
    intro m hpos hstep
    simp only [incr] at hstep
    rw [rel_update] at hstep
    rw [hstep]
    simp only [μ4] at hpos ⊢
    omega
  have henabled : ∀ m, μ4 ((b m).2) > 0 → ∃ s', rel incr ((b m).2) s' :=
    fun m _ => ⟨(b m).2 + 1, by simp only [incr, rel_update]⟩
  obtain ⟨N, hN, hz⟩ := eventually_zero_of_seq (A := incr) (I := fun _ : Nat => True)
    (μ := μ4) (b := fun k => (b k).2) (fun _ _ => trivial)
    (fun m _ h => hdec m h) (fun m _ hpos h => hA m hpos h) (fun m _ hpos => henabled m hpos) hwf n
  have hz' : 4 - (b N).2 = 0 := hz
  refine ⟨N, hN, ?_⟩
  show (b N).2 ≥ 4
  omega

/-! ## The composed system -/

/-- The targets are stable: the counters only grow. -/
theorem ge3_preserves : Preserves (counter 0).next (fun n => n ≥ 3) := by
  inv_induct
  simp only [counter, incr] at *
  action_simp
  grind

theorem ge4_preserves : Preserves (counter 1).next (fun n => n ≥ 4) := by
  inv_induct
  simp only [counter, incr] at *
  action_simp
  grind

/-- **Composed liveness.** Under weak fairness for both lifted increments, the
product eventually reaches `n ≥ 3 ∧ m ≥ 4`. -/
theorem twoCounters_live (b : Behavior (Nat × Nat)) (hbeh : IsBehavior twoCounters b)
    (hfL : WeakFair (liftLeft incr) b) (hfR : WeakFair (liftRight incr) b) :
    LeadsTo (fun _ : Nat × Nat => True) (fun p => p.1 ≥ 3 ∧ p.2 ≥ 4) b :=
  interleave_leadsTo (M := counter 0) (N := counter 1) hbeh
    ge3_preserves ge4_preserves (left_live b hbeh hfL) (right_live b hbeh hfR)

/-- A behavior that only ever moves the left component. It is a behavior of the
product, it is even weakly fair for the left increment — and it never reaches the
composed target, so the fairness hypothesis for the *right* component is not
decoration. -/
def leftOnly : Behavior (Nat × Nat) := fun k => (k, 0)

theorem leftOnly_isBehavior : IsBehavior twoCounters leftOnly := by
  intro k
  simp only [leftOnly, twoCounters, Module.interleave, counter, incr]
  action_simp
  grind

theorem leftOnly_not_live : ¬ LeadsTo (fun _ : Nat × Nat => True)
    (fun p => p.1 ≥ 3 ∧ p.2 ≥ 4) leftOnly := by
  intro h
  obtain ⟨N, -, hN⟩ := h 0 trivial
  simp only [leftOnly] at hN
  omega

end Examples.ParallelLiveness
