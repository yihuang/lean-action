/-
Examples.Liveness
=================

Liveness and termination on top of the safety layer:

* a counter that must reach 3 — proved with the fairness-based rank theorem;
* the *same* module with a stuttering behavior: liveness genuinely fails without
  fairness, and that failure is a theorem, not a remark;
* the safety → temporal bridge on the mutex example (`Always` of mutual
  exclusion along any behavior);
* termination of a `while` loop, and total correctness of the loop obtained by
  combining the termination with the partial-correctness Hoare triple from
  `Examples.Hoare`.
-/
import LeanAction
import Examples.Hoare
import Examples.Mutex

open LeanAction

namespace Examples.Liveness

/-! ## A counter that must reach 3

`next` is `incr` or `stutter`; the environment may stutter forever, so reaching
the goal needs a fairness assumption on `incr`. The variant is the distance to
the goal, `μ n = 3 - n`. -/

def incr : Action Nat := update (· + 1)

def stutter : Action Nat := skip

def M : Module Nat := ⟨(fun _ => true), incr <|> stutter⟩

/-- The variant: distance to the goal. -/
def μ (n : Nat) : Nat := 3 - n

theorem incr_decreases {s s' : Nat} (hs : μ s > 0) (h : rel incr s s') : μ s' < μ s := by
  simp only [incr, rel_update] at h
  rw [h]
  simp only [μ] at hs ⊢
  omega

theorem incr_enabled {s : Nat} (_hs : μ s > 0) : ∃ s', rel incr s s' :=
  ⟨s + 1, by simp only [incr, rel_update]⟩

theorem next_nonincreasing : ∀ s s' : Nat, rel M.next s s' → μ s' ≤ μ s := by
  intro s s' h
  simp only [M, incr, stutter] at h
  rw [rel_orElse] at h
  rcases h with h | h
  · rw [rel_update] at h; rw [h]; simp only [μ]; omega
  · rw [rel_skip] at h; rw [h]; exact Nat.le_refl _

/-- **Liveness.** Under weak fairness for `incr`, every behavior of the module
reaches `n ≥ 3` — from any starting time, because `LeadsTo` is quantified over
all times. -/
theorem eventually_three (b : Behavior Nat) (hbeh : IsBehavior M b)
    (hfair : WeakFair incr b) : LeadsTo (fun _ => true) (fun n => n ≥ 3) b := by
  refine LeadsTo.mono (fun _ _ => trivial)
    (leadsTo_zero_of_weakFair (M := M) (A := incr) (μ := μ) hbeh
      (fun s hs s' h => incr_decreases hs h)
      (fun s s' _ h => next_nonincreasing s s' h)
      (fun s hs => incr_enabled hs) hfair) ?_
  intro s hs
  simp only [μ] at hs
  omega

/-! ## The same module without fairness

`stuck` stutters forever. It is a legitimate behavior of `M`, it is not fair for
`incr`, and it never reaches the goal — so the fairness hypothesis above is not
decoration. -/

def stuck : Behavior Nat := fun _ => 1

theorem stuck_is_behavior : IsBehavior M stuck := by
  intro n
  simp only [stuck, M]
  rw [rel_orElse]
  exact Or.inr (by simp only [stutter, rel_skip])

theorem stuck_not_fair : ¬ WeakFair incr stuck := by
  intro h
  obtain ⟨m, -, hm⟩ := h 3 fun m _ => ⟨stuck m + 1, by simp only [stuck, incr, rel_update]⟩
  simp only [TakesStep, stuck, incr, rel_update] at hm
  omega

theorem stuck_never_reaches : ∀ N, stuck N < 3 := by
  intro N
  simp only [stuck]
  omega

/-- Liveness fails for `M` without fairness: a fair-looking statement is false. -/
theorem liveness_needs_fairness :
    ∃ b : Behavior Nat, IsBehavior M b ∧ ¬ WeakFair incr b ∧ ∀ N, b N < 3 :=
  ⟨stuck, stuck_is_behavior, stuck_not_fair, stuck_never_reaches⟩

/-! ## Safety as an always-property -/

/-- Safety of the counter as a temporal statement: every behavior keeps the
counter non-negative. -/
theorem counter_always_nonneg (b : Behavior Nat) (hbeh : IsBehavior M b) :
    Always (fun n => n ≥ 0) b :=
  always_of_preserves hbeh (by
    inv_induct
    simp only [M, incr, stutter] at *
    action_simp
    grind) (Nat.zero_le (b 0))

/-- Mutual exclusion of the protocol example holds at *every time* along any
behavior, not just at reachable states. -/
theorem mutex_always (b : Behavior Mutex.St) (hrun : IsRun Mutex.M b) :
    Always (fun s => ¬ (s.pc1 = 2 ∧ s.pc2 = 2)) b :=
  always_of_safe hrun Mutex.mutex_safe

/-! ## Termination of a `while` loop -/

/-- The countdown loop `while n < 3 do n := n + 1` has a terminating run. -/
theorem countTo3_can_exit : ∀ n, ∃ s', rel Hoare.countTo3 n s' :=
  loop_can_exit (P := fun k => k < 3) (A := update (· + 1)) (μ := fun k => 3 - k)
    (by
      intro s s' hP hstep
      simp only [rel_update] at hstep
      rw [hstep]
      omega)
    (by
      intro s _
      exact ⟨s + 1, by simp only [rel_update]⟩)

/-- **Total correctness** of the loop: it terminates (the termination proof
above) and every terminating run ends at 3 (the Hoare triple from
`Examples.Hoare`). -/
theorem countTo3_total : ∃ s', rel Hoare.countTo3 0 s' ∧ s' = 3 := by
  obtain ⟨s', hs'⟩ := countTo3_can_exit 0
  exact ⟨s', hs', Hoare.countTo3_correct 0 (Nat.zero_le 3) s' hs'⟩

end Examples.Liveness
