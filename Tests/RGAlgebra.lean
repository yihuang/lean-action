/-
Tests.RGAlgebra
=============

Regression tests for "rely as output, not input"
(`derivedRely` / `preserves_of_guarantees`, now in `LeanAction.Frame`).

With the N-node mutex, the binary composition is exercised through the split
`next = steps i <|> others i` (`MutexLiveness.rel_next_iff`): node `i`'s own
guarantee on one side, every other node on the other.

Tests:
* mutex safety recomposed *without* writing any rely: the two guarantee lemmas
  (each one `action_simp; …`) are both the obligations and the interfaces;
* the recomposed `Preserves` is genuinely the same one the example proves.
-/
import LeanAction
import Examples.Mutex
import Examples.MutexLiveness

open LeanAction

namespace Tests.RGAlgebra

open Examples.Mutex (Pc St M next inv req enter exit steps setPc release)
open Examples.MutexLiveness (others rel_next_iff)

/-- Node `i`'s own steps preserve the invariant. -/
theorem steps_guarantee {n : Nat} (i : Fin n) :
    ∀ s s' : St n, inv s → rel (steps i) s s' → inv s' := by
  intro s s' hi h
  simp only [steps, req, enter, exit, inv] at hi h ⊢
  action_simp
  rcases h with h | h | h
  all_goals
    rcases h with ⟨t, ⟨hp, ht⟩, hs'⟩
    subst t
    subst s'
    intro k hk
    simp_all [setPc, release, upd.eq_1]
    try grind

/-- A step of every node other than `i` preserves the invariant too. -/
theorem others_guarantee {n : Nat} (i : Fin n) :
    ∀ s s' : St n, inv s → rel (others i) s s' → inv s' := by
  intro s s' hi h
  simp only [inv] at hi ⊢
  simp only [others, rel_choiceAll] at h
  obtain ⟨⟨j, hji⟩, hj⟩ := h
  simp only [steps, req, enter, exit] at hj
  action_simp
  rcases hj with h | h | h
  all_goals
    rcases h with ⟨t, ⟨hp, ht⟩, hs'⟩
    subst t
    subst s'
    intro k hk
    simp_all [setPc, release, upd.eq_1]
    try grind

/-- Mutex safety, recomposed *without* writing any rely: the two guarantee
lemmas above are both the obligations and the interfaces. Compare with
`Examples.Mutex.inv_step`, which performs the case analysis directly. -/
theorem mutex_safe_recomposed {n : Nat} (i : Fin n) :
    Preserves (next (n := n)) (inv (n := n)) := by
  have h : Preserves (steps i <|> others i) (inv (n := n)) :=
    preserves_of_guarantees (steps_guarantee i) (others_guarantee i)
  intro s hs s' hstep
  exact h s hs s' ((rel_next_iff i).mp hstep)

/-- Sanity: this is genuinely the same `Preserves` the example proves. -/
theorem mutex_safe_agrees (n : Nat) : Preserves (next (n := n)) (inv (n := n)) :=
  Examples.Mutex.inv_step (n := n)

end Tests.RGAlgebra
