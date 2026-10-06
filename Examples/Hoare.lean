/-
Examples.Hoare
==============

Partial correctness (`Hoare` triples) as opposed to safety (`Preserves`):

* `iterate`: unbounded iteration with an arithmetic post-condition;
* `loop` (`while`): the loop rule `Hoare.loop` and its "exit condition" use;
* `nondet`: a relation-based action;
* `focusView`: a triple for an action focused on a nested field.
-/
import LeanAction
import LeanAction.Derive

open LeanAction

namespace Examples.Hoare

/-- Increment on `Nat`. -/
def incr : Action Nat := update (· + 1)

/-- Repeating `incr` exactly `k` times adds `k`.
Note the `∀ n` *inside* the theorem: the induction has to be general in the
starting value, since the `succ` case instantiates it at `n + 1`. -/
theorem iterate_incr (k : Nat) :
    ∀ n : Nat, Hoare (fun s => s = n) (iterate incr k) (fun s => s = n + k) := by
  induction k with
  | zero =>
    intro n s hs s' h
    simp only [rel_iterate_zero] at h
    rw [h]
    simpa using hs
  | succ k ih =>
    intro n s hs s' h
    simp only [rel_iterate_succ] at h
    obtain ⟨t, h1, h2⟩ := h
    have ht : t = n + 1 := by
      simp only [incr, rel_update] at h1
      rw [h1, hs]
    have hk : n + 1 + k = n + (k + 1) := by omega
    have hres := ih (n + 1) t (by rw [ht]) s' h2
    rwa [hk] at hres

/-- Same statement through the library rule `Hoare.iterate` plus `Preserves`. -/
theorem iterate_incr' (k n : Nat) :
    Hoare (fun s => s = n) (iterate incr k) (fun s => s ≥ n) := by
  have hpres : Preserves incr (fun s => s ≥ n) := by
    unfold Preserves
    intro s hs s' h
    simp only [incr, rel_update] at h
    rw [h]
    omega
  exact Hoare.conseq (fun s hs => by rw [hs]; exact Nat.le_refl n)
    (Hoare.iterate hpres k) (fun s hs => hs)

/-! ## `while` loops: partial correctness from the exit condition -/

/-- Count up to 3. -/
def countTo3 : Action Nat := while[fun n => n < 3] (update (· + 1))

/-- If the loop terminates, it terminates at 3 — without assuming it *does*
terminate (this is partial correctness, not liveness). -/
theorem countTo3_correct : Hoare (fun n => n ≤ 3) countTo3 (fun n => n = 3) := by
  apply Hoare.loop (I := fun n => n ≤ 3) (Q := fun n => n = 3)
  · intro s hs hlt s' h
    simp only [rel_update] at h
    rw [h]
    omega
  · intro s hs hnlt
    omega

/-- A loop over a nondeterministic body, keeping a lower bound. -/
def bumpOrSkip : Action Nat := update (· + 1) <|> skip

theorem loop_keeps_lower_bound (n : Nat) :
    Hoare (fun s => s ≥ n) (while[fun _ => True] bumpOrSkip) (fun s => s ≥ n) := by
  apply Hoare.loop (I := fun s => s ≥ n) (Q := fun s => s ≥ n)
  · intro s hs _ s' h
    simp only [bumpOrSkip] at h
    rw [rel_orElse] at h
    rcases h with h | h
    · rw [rel_update] at h; rw [h]; omega
    · rw [rel_skip] at h; rw [h]; exact hs
  · intro s hs hntrue
    exact absurd trivial hntrue

/-! ## Nondeterministic actions -/

/-- Any transition that does not decrease the value keeps it above the bound. -/
theorem nondet_keeps_bound (n : Nat) :
    Hoare (fun s => s ≥ n) (nondet (fun a b => a ≤ b)) (fun s => s ≥ n) := by
  apply Hoare.nondet
  intro s hs s' h
  omega

/-! ## Focused Hoare triples -/

structure Inner where
  n : Nat
  deriving ViewFields, LensFields

structure Outer where
  inner : Inner
  flag : Bool
  deriving ViewFields, LensFields

/-- The nested field `Outer.inner.n`. -/
def outerN : View Outer Nat := View.comp Outer.innerView Inner.nView

/-- A Hoare triple for the *focused* increment: the inner pre/post-conditions
are transported through the view by `Hoare.focusView`. -/
theorem focused_incr_hoare (k : Nat) :
    Hoare (fun s : Outer => s.inner.n = k) (focusView outerN (update (· + 1)))
      (fun s : Outer => s.inner.n = k + 1) := by
  refine Hoare.focusView (v := outerN) (A := update (· + 1))
    (P' := fun n => n = k) (Q' := fun n => n = k + 1) ?_ ?_ ?_
  · intro s hs
    simpa only [outerN, Outer.innerView, Inner.nView, View.comp] using hs
  · apply Hoare.update
    intro n hn
    omega
  · intro s a hs hq
    simpa only [outerN, Outer.innerView, Inner.nView, View.comp] using hq

end Examples.Hoare
