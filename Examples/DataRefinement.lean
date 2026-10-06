/-
Examples.DataRefinement
=======================

Data refinement with a *non-identity* abstraction map, plus the two styles of
reasoning side by side:

* `Refines abs' Spec Conc` — the concrete module (a counter with an audit log)
  implements the abstract counter;
* safety transfers along the refinement (`Refines.safe`);
* an implementation-only invariant (`count = log.length`) that the abstraction
  cannot even express, proved directly with `Preserves`;
* a concrete run transported to an abstract run through `Refines.reach`.
-/
import LeanAction

open LeanAction

namespace Examples.DataRefinement

/-- Concrete state: the counter plus an audit log of the previous values. -/
structure Conc where
  count : Nat
  log : List Nat

/-- Abstract specification: count from 0. -/
def Spec : Module Nat := ⟨(fun n => n = 0), update (· + 1)⟩

/-- Concrete implementation: count and log. -/
def ConcM : Module Conc :=
  ⟨(fun c => c.count = 0 ∧ c.log = []),
   update (fun c => { c with count := c.count + 1, log := c.count :: c.log })⟩

/-- The abstraction map: keep the count, forget the log. -/
def abs' (c : Conc) : Nat := c.count

theorem conc_refines_spec : Refines abs' Spec ConcM := by
  constructor
  · intro c hc
    simp only [ConcM] at hc
    exact ⟨c.count, hc.1, rfl⟩
  · intro a c hac c' hstep
    simp only [ConcM, rel_update] at hstep
    have hac' : a = c.count := hac
    refine ⟨abs' c', Reach.single ?_, rfl⟩
    change rel (update (· + 1)) a (abs' c')
    rw [rel_update, hstep]
    simp [abs', hac']

/-! ## Safety transfers from the specification -/

theorem spec_safe : Spec.Safe (fun n => n ≥ 0) := by
  apply Module.safe_of_preserves
  · intro s hs
    omega
  · inv_induct
    simp only [Spec] at *
    action_simp
    grind

/-- The abstract safety property, transported to the concrete state. -/
theorem conc_safe : ConcM.Safe (fun c => c.count ≥ 0) := by
  have h := conc_refines_spec.safe spec_safe
  simpa only [abs'] using h

/-! ## An implementation-only invariant

`count = log.length` mentions the log, so it is invisible to the abstract
specification; it is proved directly on the concrete module. -/
theorem conc_log_length : ConcM.Safe (fun c => c.count = c.log.length) := by
  apply Module.safe_of_preserves
  · intro c hc
    obtain ⟨h1, h2⟩ := hc
    simp [h1, h2]
  · inv_induct
    simp only [ConcM] at *
    action_simp
    grind

/-! ## Runs: concrete steps are matched by abstract steps -/

/-- Two concrete steps reach `⟨2, [1, 0]⟩`. -/
theorem conc_run : Reach ConcM.next ⟨0, []⟩ ⟨2, [1, 0]⟩ := by
  have h1 : rel ConcM.next ⟨0, []⟩ ⟨1, [0]⟩ := by
    simp only [ConcM, rel_update] <;> first | rfl | grind
  have h2 : rel ConcM.next ⟨1, [0]⟩ ⟨2, [1, 0]⟩ := by
    simp only [ConcM, rel_update] <;> first | rfl | grind
  exact Reach.step (Reach.single h1) h2

/-- `Refines.reach` transports the concrete run to an abstract run. -/
theorem conc_run_matched {c' : Conc} (h : Reach ConcM.next ⟨0, []⟩ c') :
    ∃ a, Reach Spec.next 0 a ∧ a = abs' c' :=
  conc_refines_spec.reach (a := 0) (c := ⟨0, []⟩) rfl h

/-- Consequently the abstract counter reaches 2 whenever the concrete module
reaches a state whose count is 2. -/
theorem conc_run_reaches_two :
    ∃ a, Reach Spec.next 0 a ∧ a = 2 := by
  have h := conc_run_matched conc_run
  simpa only [abs'] using h

end Examples.DataRefinement
