/-
Examples.Basic
==============

Counter with a log (the running example of the design), nested structures via
`View.comp`/`focusView`, and a `while` loop.
-/
import LeanAction

open LeanAction

namespace Examples.Counter

structure Ctr where
  n : Nat
  log : List Nat

/-- Read the current state, bump the counter, and log the *old* value. Written in
the `do`-DSL of the library. -/
def incr : Action Ctr := do
  let s ← (ActionM.get : ActionM Ctr Ctr)
  ActionM.modify fun t => { t with n := t.n + 1, log := s.n :: t.log }

/-- Reset to the initial state. -/
def reset : Action Ctr := set { n := 0, log := [] }

def init : Nondet Ctr := fun s => s.n = 0 ∧ s.log = []
def inv : Nondet Ctr := fun s => s.n = s.log.length

/-- The transition system: nondeterministically increment or reset. -/
def M : Module Ctr := ⟨init, incr <|> reset⟩

/-- The initial condition establishes the invariant. -/
theorem inv_init : init ⊆ₙ inv := by
  intro s hs
  simp only [init, inv] at hs ⊢
  grind

/-- One step preserves the invariant. Note how `action_simp` turns the composite
action into a first-order statement; the only remaining work is arithmetic. -/
theorem inv_step : Preserves (incr <|> reset) inv := by
  inv_induct
  simp only [inv, incr, reset] at *
  action_simp
  grind

/-- Safety, assembled by hand from the two lemmas. -/
theorem safe : M.Safe inv :=
  Module.safe_of_preserves inv_init inv_step

/-- The same proof, driven by the `safe_induct` tactic. -/
theorem safe_tactic : M.Safe inv := by
  safe_induct
  · intro s hs
    unfold M at hs
    simp only [init, inv] at hs ⊢
    grind
  · inv_induct
    simp only [M, incr, reset, inv] at *
    action_simp
    grind

/-- A `while` loop: `loop P A` runs `A` while `P` holds. -/
def countdown (_n : Nat) : Action Nat := while[fun k => k > 0] (update (· - 1))

/-- The loop can only stop in a state where the guard fails. -/
theorem countdown_stops {n m : Nat} (h : rel (countdown n) n m) : m = 0 := by
  rw [countdown, rel_loop] at h
  have : ¬ m > 0 := h.2
  omega

end Examples.Counter

namespace Examples.Nested

/-- Nested state: an inner record plus a flag. -/
structure Inner where
  n : Nat

structure Outer where
  inner : Inner
  flag : Bool

/-- Proof-free focus points: composition of `View`s selects `Outer.inner.n`. -/
def innerView : View Outer Inner := ⟨(·.inner), fun s v => { s with inner := v }⟩
def nView : View Inner Nat := ⟨(·.n), fun s v => { s with n := v }⟩
def outerN : View Outer Nat := View.comp innerView nView

/-- Increment only the nested counter; `flag` and everything else is untouched. -/
def incrN : Action Outer := focusView outerN (update (· + 1))

/-- The focused action really only touches the selected component. -/
theorem incrN_rel {s s' : Outer} :
    rel incrN s s' ↔ s' = { s with inner := { n := s.inner.n + 1 } } := by
  simp only [incrN, rel_focusView, rel_update]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨s.inner.n + 1, rfl, rfl⟩

/-- Componentwise monotonicity of the nested counter. -/
theorem incrN_preserves : Preserves incrN (fun s : Outer => s.inner.n ≥ 0) := by
  unfold Preserves
  intro s hs s' hstep
  simp only [incrN, outerN, innerView, nView, View.comp, rel_focusView, rel_update] at hstep
  obtain ⟨a, -, rfl⟩ := hstep
  grind

end Examples.Nested
