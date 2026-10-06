/-
Examples.Parallel
=================

Interleaving (asynchronous) composition of two transition systems, plus a data
refinement proof with stuttering.
-/
import LeanAction

open LeanAction

namespace Examples.Parallel

/-- A counter that starts at `init` and increments forever. -/
def counter (init : Nat) : Module Nat :=
  ⟨(fun n => n = init), update (· + 1)⟩

/-- Two counters running asynchronously: each step advances one of them. -/
def twoCounters : Module (Nat × Nat) := (counter 0).interleave (counter 1)

/-- Invariant: at least one unit of "work" has been done. -/
def inv : Nondet (Nat × Nat) := fun p => p.1 + p.2 ≥ 1

/-- One interleaved step preserves `inv`. The library's `action_simp` splits the
interleaving into its two components and the view lemmas into their effects. -/
theorem twoCounters_inv_step : Preserves twoCounters.next inv := by
  inv_induct
  simp only [twoCounters, Module.interleave, counter, inv] at *
  action_simp
  grind

/-- Safety of the interleaved system. -/
theorem twoCounters_safe : twoCounters.Safe inv := by
  unfold Module.Safe
  intro p hp p' hr
  have hinit : inv p := by
    simp only [twoCounters, Module.interleave, counter, inv] at hp ⊢
    omega
  exact Preserves.reach twoCounters_inv_step p hinit p' hr

/-- The same invariant holds at every reachable state, spelled out. -/
theorem twoCounters_reachable {p : Nat × Nat}
    (h : ∃ p₀, (twoCounters.init p₀) ∧ Reach twoCounters.next p₀ p) : inv p := by
  obtain ⟨p₀, hinit, hr⟩ := h
  exact twoCounters_safe p₀ hinit p hr

end Examples.Parallel

namespace Examples.Refinement

/-- Abstract specification: count from 0. -/
def Spec : Module Nat := ⟨(fun n => n = 0), update (· + 1)⟩

/-- Concrete implementation: the same counter, but allowed to stutter. -/
def Conc : Module Nat := ⟨(fun n => n = 0), update (· + 1) <|> skip⟩

/-- `Conc` refines `Spec` through the identity abstraction map. -/
theorem conc_refines_spec : Refines id Spec Conc := by
  constructor
  · intro c hc
    exact ⟨c, hc, rfl⟩
  · intro a c hac c' hstep
    change rel (update (· + 1) <|> skip) c c' at hstep
    rw [rel_orElse] at hstep
    rcases hstep with h | h
    · rw [rel_update] at h
      refine ⟨c', Reach.single ?_, rfl⟩
      change rel (update (· + 1)) a c'
      rw [rel_update, h, hac]
      simp
    · rw [rel_skip] at h
      exact ⟨a, Reach.refl _ a, by rw [h]; exact hac⟩

/-- Safety of the specification. -/
theorem spec_safe : Spec.Safe (fun n => n ≥ 0) := by
  apply Module.safe_of_preserves
  · intro s hs
    change s = 0 at hs
    omega
  · unfold Preserves
    intro s _ s' hstep
    change rel (update (· + 1)) s s' at hstep
    rw [rel_update] at hstep
    rw [hstep]
    omega

/-- Safety transfers from the specification to the implementation. -/
theorem conc_safe : Conc.Safe (fun n => n ≥ 0) := by
  have := conc_refines_spec.safe spec_safe
  simpa using this

end Examples.Refinement
