/-
LeanAction.Liveness
===================

Temporal reasoning on top of the transition relation: `Always`, `Eventually`,
`LeadsTo`, behaviors of a module, and the fairness hypotheses that make
liveness provable.

Two layers, matching the two ways liveness is actually obtained:

1. **Rank / variant arguments** (`eventually_zero_of_nat_progress_from`,
   `eventually_zero_of_weakFair`): a `Nat`-valued measure that never increases
   along a behavior and strictly decreases whenever the progress action is taken.
   With weak fairness for that action the measure reaches zero. The engine is
   well-founded recursion on the rank (`Nat.strongRecOn`), not a search for the
   minimum — that keeps the library free of non-core dependencies.

2. **Termination of a `while` loop** (`loop_can_exit`): with a variant that
   strictly decreases on every body step, the loop *can* exit, i.e. the
   existential half of termination. Combined with `Hoare.loop` (partial
   correctness) this yields total correctness of the loop.

Safety connects to the temporal layer through `always_of_safe`: every behavior
that starts in an initial state satisfies all reachable-state invariants at all
times.

Note that fairness is not a technicality: `Examples/Liveness.lean` proves that
the very same module admits a stuttering behavior that never reaches the goal.
-/
import Std
import LeanAction.Proof
import LeanAction.Tactic

universe u

namespace LeanAction

open Nondet

variable {σ : Type u}

/-! ## Behaviors and temporal predicates -/

/-- A behavior: an infinite sequence of states. -/
abbrev Behavior (σ : Type u) := Nat → σ

/-- `Always P b`: `P` holds at every time. -/
def Always (P : Nondet σ) (b : Behavior σ) : Prop := ∀ n, P (b n)

/-- `Eventually P b`: `P` holds at some time. -/
def Eventually (P : Nondet σ) (b : Behavior σ) : Prop := ∃ n, P (b n)

/-- `LeadsTo P Q b`: whenever `P` holds, `Q` holds at that time or later. -/
def LeadsTo (P Q : Nondet σ) (b : Behavior σ) : Prop :=
  ∀ n, P (b n) → ∃ m, n ≤ m ∧ Q (b m)

/-- Consecutive states are related by the module's next-state action. -/
def IsBehavior (M : Module σ) (b : Behavior σ) : Prop :=
  ∀ n, rel M.next (b n) (b (n + 1))

/-- A behavior that starts in an initial state of the module. -/
def IsRun (M : Module σ) (b : Behavior σ) : Prop := M.init (b 0) ∧ IsBehavior M b

theorem Always.elim {P : Nondet σ} {b : Behavior σ} (h : Always P b) (n : Nat) : P (b n) :=
  h n

theorem Always.mp {P Q : Nondet σ} {b : Behavior σ} (h : Always P b)
    (hPQ : ∀ s, P s → Q s) : Always Q b :=
  fun n => hPQ _ (h n)

theorem Always.and {P Q : Nondet σ} {b : Behavior σ} (hp : Always P b) (hq : Always Q b) :
    Always (fun s => P s ∧ Q s) b :=
  fun n => ⟨hp n, hq n⟩

theorem Always.eventually {P : Nondet σ} {b : Behavior σ} (h : Always P b) :
    Eventually P b :=
  ⟨0, h 0⟩

theorem Eventually.mono {P Q : Nondet σ} {b : Behavior σ} (hPQ : ∀ s, P s → Q s)
    (h : Eventually P b) : Eventually Q b := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hPQ _ hn⟩

/-- `Eventually` is the dual of `Always` (classical logic). -/
theorem eventually_iff_not_always_not {P : Nondet σ} {b : Behavior σ} :
    Eventually P b ↔ ¬ Always (fun s => ¬ P s) b := by
  constructor
  · rintro ⟨n, hn⟩ h
    exact h n hn
  · intro h
    by_cases hex : ∃ n, P (b n)
    · exact hex
    · exact absurd (fun n hn => hex ⟨n, hn⟩) h

theorem LeadsTo.refl {P : Nondet σ} {b : Behavior σ} : LeadsTo P P b :=
  fun n hn => ⟨n, Nat.le_refl n, hn⟩

theorem LeadsTo.mono {P P' Q Q' : Nondet σ} {b : Behavior σ} (hPP' : ∀ s, P' s → P s)
    (h : LeadsTo P Q b) (hQQ' : ∀ s, Q s → Q' s) : LeadsTo P' Q' b := by
  intro n hn
  obtain ⟨m, hnm, hm⟩ := h n (hPP' _ hn)
  exact ⟨m, hnm, hQQ' _ hm⟩

theorem LeadsTo.trans {P Q R : Nondet σ} {b : Behavior σ} (hpq : LeadsTo P Q b)
    (hqr : LeadsTo Q R b) : LeadsTo P R b := by
  intro n hn
  obtain ⟨m, hnm, hm⟩ := hpq n hn
  obtain ⟨k, hmk, hk⟩ := hqr m hm
  exact ⟨k, Nat.le_trans hnm hmk, hk⟩

theorem eventually_of_leadsTo {P Q : Nondet σ} {b : Behavior σ} (h : LeadsTo P Q b)
    (hP : P (b 0)) : Eventually Q b := by
  obtain ⟨m, -, hm⟩ := h 0 hP
  exact ⟨m, hm⟩

/-! ## Safety as a temporal property -/

/-- Every behavior of a module satisfies every preserved predicate at all times. -/
theorem always_of_preserves {M : Module σ} {P : Nondet σ} {b : Behavior σ}
    (hbeh : IsBehavior M b) (hpres : Preserves M.next P) (h0 : P (b 0)) : Always P b := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hpres _ ih _ (hbeh n)

/-- Every behavior from an initial state always satisfies the module's safety
properties. -/
theorem always_of_safe {M : Module σ} {P : Nondet σ} {b : Behavior σ} (hrun : IsRun M b)
    (hsafe : M.Safe P) : Always P b := by
  have hreach : ∀ n, Reach M.next (b 0) (b n) := by
    intro n
    induction n with
    | zero => exact Reach.refl _ _
    | succ n ih => exact Reach.step ih (hrun.2 n)
  intro n
  exact hsafe (b 0) hrun.1 (b n) (hreach n)

/-! ## Fairness -/

/-- The step taken at time `n` satisfies the action `A`. -/
def TakesStep (A : Action σ) (b : Behavior σ) (n : Nat) : Prop := rel A (b n) (b (n + 1))

/-- Weak fairness for `A`: if `A` is continuously enabled from some time on, then
a step satisfying `A` is taken eventually after that time. -/
def WeakFair (A : Action σ) (b : Behavior σ) : Prop :=
  ∀ n, (∀ m, n ≤ m → ∃ s', rel A (b m) s') → ∃ m, n ≤ m ∧ TakesStep A b m

/-- Strong fairness for `A`: if `A` is enabled infinitely often, then a step
satisfying `A` is taken eventually after any time. -/
def StrongFair (A : Action σ) (b : Behavior σ) : Prop :=
  ∀ n, (∀ k, ∃ m, k ≤ m ∧ ∃ s', rel A (b m) s') → ∃ m, n ≤ m ∧ TakesStep A b m

/-- Strong fairness implies weak fairness. -/
theorem StrongFair.toWeakFair {A : Action σ} {b : Behavior σ} (h : StrongFair A b) :
    WeakFair A b :=
  fun n hen => h n fun k => ⟨max k n, Nat.le_max_left _ _, hen _ (Nat.le_max_right _ _)⟩

/-! ## Rank arguments -/

/-- Monotonicity of a non-increasing sequence, used by both rank theorems. -/
theorem nat_le_of_nonincr {f : Nat → Nat} (hmono : ∀ n, f (n + 1) ≤ f n) :
    ∀ {a c : Nat}, a ≤ c → f c ≤ f a := by
  intro a c hac
  induction hac with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans (hmono _) ih

/-- **Rank progress along a behavior.** If the rank never increases and strictly
decreases arbitrarily late whenever it is positive, then it reaches zero
eventually — in fact eventually after *any* time. The proof is well-founded
recursion on the rank. -/
theorem eventually_zero_of_nat_progress_from {μ : σ → Nat} {b : Behavior σ}
    (hmono : ∀ n, μ (b (n + 1)) ≤ μ (b n))
    (hfair : ∀ n, μ (b n) > 0 → ∃ m, n ≤ m ∧ μ (b (m + 1)) < μ (b m)) :
    ∀ n, ∃ N, n ≤ N ∧ μ (b N) = 0 := by
  have hmono' : ∀ {a c : Nat}, a ≤ c → μ (b c) ≤ μ (b a) :=
    nat_le_of_nonincr (f := fun k => μ (b k)) hmono
  have key : ∀ k, ∀ n, μ (b n) = k → ∃ N, n ≤ N ∧ μ (b N) = 0 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n hn
      by_cases hzero : μ (b n) = 0
      · exact ⟨n, Nat.le_refl n, hzero⟩
      · obtain ⟨m, hnm, hlt⟩ := hfair n (Nat.pos_of_ne_zero hzero)
        have hle : μ (b m) ≤ μ (b n) := hmono' hnm
        have hltk : μ (b (m + 1)) < k := by omega
        obtain ⟨N, hN, hz⟩ := ih (μ (b (m + 1))) hltk (m + 1) rfl
        exact ⟨N, Nat.le_trans (Nat.le_trans hnm (Nat.le_succ m)) hN, hz⟩
  intro n
  exact key (μ (b n)) n rfl

theorem eventually_zero_of_nat_progress {μ : σ → Nat} {b : Behavior σ}
    (hmono : ∀ n, μ (b (n + 1)) ≤ μ (b n))
    (hfair : ∀ n, μ (b n) > 0 → ∃ m, n ≤ m ∧ μ (b (m + 1)) < μ (b m)) :
    ∃ N, μ (b N) = 0 := by
  obtain ⟨N, -, hN⟩ := eventually_zero_of_nat_progress_from hmono hfair 0
  exact ⟨N, hN⟩

/-- A monotone bound for `A <|> B` from component-wise bounds. -/
theorem nonincreasing_orElse {A B : Action σ} {μ : σ → Nat}
    (hA : ∀ s s', rel A s s' → μ s' ≤ μ s) (hB : ∀ s s', rel B s s' → μ s' ≤ μ s) :
    ∀ s s', rel (A <|> B) s s' → μ s' ≤ μ s := by
  intro s s' h
  rw [rel_orElse] at h
  exact h.elim (hA s s') (hB s s')

/-- **Fairness-based inevitability.** If the progress action `A` strictly
decreases the rank while the goal is not reached, every module step keeps the
rank from increasing, `A` stays enabled as long as the rank is positive, and the
behavior is weakly fair for `A`, then the rank reaches zero eventually after any
time. -/
theorem eventually_zero_of_weakFair {M : Module σ} {A : Action σ} {μ : σ → Nat}
    {b : Behavior σ} (hbeh : IsBehavior M b)
    (hA : ∀ s, μ s > 0 → ∀ s', rel A s s' → μ s' < μ s)
    (henv : ∀ s s', rel M.next s s' → μ s' ≤ μ s)
    (henabled : ∀ s, μ s > 0 → ∃ s', rel A s s')
    (hfair : WeakFair A b) : ∀ n, ∃ N, n ≤ N ∧ μ (b N) = 0 := by
  have hmono : ∀ k, μ (b (k + 1)) ≤ μ (b k) := fun k => henv _ _ (hbeh k)
  have hmono' : ∀ {a c : Nat}, a ≤ c → μ (b c) ≤ μ (b a) :=
    nat_le_of_nonincr (f := fun k => μ (b k)) hmono
  have key : ∀ k, ∀ n, μ (b n) = k → ∃ N, n ≤ N ∧ μ (b N) = 0 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n hn
      by_cases hzero : μ (b n) = 0
      · exact ⟨n, Nat.le_refl n, hzero⟩
      · -- either the goal is reached later, or the rank stays positive and `A`
        -- is continuously enabled, so fairness produces a decreasing step
        by_cases hreached : ∃ N, n ≤ N ∧ μ (b N) = 0
        · exact hreached
        · have hen : ∀ m, n ≤ m → ∃ s', rel A (b m) s' := by
            intro m hm
            refine henabled _ (Nat.pos_of_ne_zero ?_)
            intro hz
            exact hreached ⟨m, hm, hz⟩
          obtain ⟨m, hnm, htaken⟩ := hfair n hen
          have hposm : μ (b m) > 0 := by
            refine Nat.pos_of_ne_zero ?_
            intro hz
            exact hreached ⟨m, hnm, hz⟩
          have hlt : μ (b (m + 1)) < μ (b m) := hA _ hposm _ htaken
          have hle : μ (b m) ≤ μ (b n) := hmono' hnm
          have hltk : μ (b (m + 1)) < k := by omega
          obtain ⟨N, hN, hz⟩ := ih (μ (b (m + 1))) hltk (m + 1) rfl
          exact ⟨N, Nat.le_trans (Nat.le_trans hnm (Nat.le_succ m)) hN, hz⟩
  intro n
  exact key (μ (b n)) n rfl

/-- `LeadsTo` form of `eventually_zero_of_weakFair`. -/
theorem leadsTo_zero_of_weakFair {M : Module σ} {A : Action σ} {μ : σ → Nat}
    {b : Behavior σ} (hbeh : IsBehavior M b)
    (hA : ∀ s, μ s > 0 → ∀ s', rel A s s' → μ s' < μ s)
    (henv : ∀ s s', rel M.next s s' → μ s' ≤ μ s)
    (henabled : ∀ s, μ s > 0 → ∃ s', rel A s s')
    (hfair : WeakFair A b) : LeadsTo (fun _ : σ => True) (fun s => μ s = 0) b :=
  fun n _ => eventually_zero_of_weakFair hbeh hA henv henabled hfair n

/-! ## Termination of `while` loops -/

/-- **The loop can exit.** If the body strictly decreases a variant on every
enabled step and is always enabled while the guard holds, then the `while` loop
has a terminating run. -/
theorem loop_can_exit {P : σ → Prop} {A : Action σ} {μ : σ → Nat}
    (hdec : ∀ s s', P s → rel A s s' → μ s' < μ s)
    (hen : ∀ s, P s → ∃ s', rel A s s') : ∀ s, ∃ s', rel (loop P A) s s' := by
  suffices h : ∀ k, ∀ s, μ s = k → ∃ s', rel (loop P A) s s' from
    fun s => h (μ s) s rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro s hs
    by_cases hP : P s
    · obtain ⟨t, hstep⟩ := hen s hP
      obtain ⟨u, htail⟩ := ih (μ t) (by rw [← hs]; exact hdec s t hP hstep) t rfl
      rw [rel_loop] at htail
      refine ⟨u, ?_⟩
      rw [rel_loop]
      exact ⟨Rel.reflTransGen_trans
        (Rel.ReflTransGen.tail (Rel.ReflTransGen.refl s) ⟨hP, hstep⟩) htail.1, htail.2⟩
    · refine ⟨s, ?_⟩
      rw [rel_loop]
      exact ⟨Rel.ReflTransGen.refl s, hP⟩

end LeanAction
