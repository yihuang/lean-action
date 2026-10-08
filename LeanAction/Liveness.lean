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

/-- Case split: if both disjuncts lead to `R`, so does the disjunction. -/
theorem LeadsTo.or {P Q R : Nondet σ} {b : Behavior σ}
    (hP : LeadsTo P R b) (hQ : LeadsTo Q R b) :
    LeadsTo (fun s => P s ∨ Q s) R b := by
  intro n hn
  rcases hn with hn | hn
  · exact hP n hn
  · exact hQ n hn

/-- **Cancellation.** If from `P` we reach `Q ∨ R`, and from `R` we reach `Q`,
then from `P` we already reach `Q`. This is the lemma behind the manual
`by_cases` in fairness proofs: split on whether the goal is reached, and let the
fairness argument handle the other branch. -/
theorem LeadsTo.cancel {P Q R : Nondet σ} {b : Behavior σ}
    (h₁ : LeadsTo P (fun s => Q s ∨ R s) b) (h₂ : LeadsTo R Q b) : LeadsTo P Q b := by
  intro n hn
  obtain ⟨m, hnm, hm | hm⟩ := h₁ n hn
  · exact ⟨m, hnm, hm⟩
  · obtain ⟨k, hmk, hk⟩ := h₂ m hm
    exact ⟨k, Nat.le_trans hnm hmk, hk⟩

/-- `LeadsTo` is unchanged by shifting the behavior in time. -/
theorem LeadsTo.shift {P Q : Nondet σ} {b : Behavior σ} (h : LeadsTo P Q b) (n : Nat) :
    LeadsTo P Q (fun k => b (n + k)) := by
  intro m hm
  obtain ⟨k, hmk, hk⟩ := h (n + m) hm
  refine ⟨k - n, by omega, ?_⟩
  have : n + (k - n) = k := by omega
  simpa [this] using hk

/-- Introduction principle: `LeadsTo` only has to be proved on the shifted
behavior, where `Eventually` replaces the `∃ m, n ≤ m` quantifier shape. -/
theorem LeadsTo.of_shift {P Q : Nondet σ} {b : Behavior σ}
    (h : ∀ n, P (b n) → Eventually Q (fun k => b (n + k))) : LeadsTo P Q b := by
  intro n hn
  obtain ⟨m, hm⟩ := h n hn
  exact ⟨n + m, Nat.le_add_right n m, hm⟩

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

/-- Fairness stated through `Enabled`: the antecedent of `WeakFair` is
literally "`Enabled A` holds at every time from `n` on". -/
theorem weakFair_enabled {A : Action σ} {b : Behavior σ} :
    WeakFair A b ↔
    ∀ n, (∀ m, n ≤ m → Enabled A (b m)) → ∃ m, n ≤ m ∧ TakesStep A b m := Iff.rfl

/-- Shifting a behavior in time preserves being a behavior. -/
theorem isBehavior_add {M : Module σ} {b : Behavior σ} (h : IsBehavior M b) (n : Nat) :
    IsBehavior M (fun k => b (n + k)) := fun k => by
  simpa [Nat.add_assoc] using h (n + k)

/-- Shifting a behavior in time preserves weak fairness. Together with
`isBehavior_add` this removes the boilerplate every `LeadsTo` packaging proof
otherwise repeats. -/
theorem weakFair_add {A : Action σ} {b : Behavior σ} (h : WeakFair A b) (n : Nat) :
    WeakFair A (fun k => b (n + k)) := by
  intro m hen
  have hen' : ∀ j, n + m ≤ j → ∃ s', rel A (b j) s' := by
    intro j hj
    have hmn : m ≤ j - n := by omega
    have hj' : n + (j - n) = j := by omega
    simpa [hj'] using hen (j - n) hmn
  obtain ⟨j, hj, hstep⟩ := h (n + m) hen'
  refine ⟨j - n, by omega, ?_⟩
  have h1 : n + (j - n) = j := by omega
  have h2 : n + (j - n + 1) = j + 1 := by omega
  simpa [TakesStep, h1, h2] using hstep

/-- Shifting a behavior in time preserves strong fairness. -/
theorem strongFair_add {A : Action σ} {b : Behavior σ} (h : StrongFair A b) (n : Nat) :
    StrongFair A (fun k => b (n + k)) := by
  intro m hen
  have hen' : ∀ k, ∃ i, k ≤ i ∧ ∃ s', rel A (b i) s' := by
    intro k
    obtain ⟨j, hj, hs⟩ := hen (max m (k - n))
    exact ⟨n + j, by omega, hs⟩
  obtain ⟨i, hi, hstep⟩ := h (n + m) hen'
  refine ⟨i - n, by omega, ?_⟩
  have h1 : n + (i - n) = i := by omega
  have h2 : n + (i - n + 1) = i + 1 := by omega
  simpa [TakesStep, h1, h2] using hstep

/-- **WF1, with an arbitrary step relation.** `T` is the environment's step
relation; the rule touches the environment only through `henv`, so nothing forces
`T = M.next`. Keeping `T` abstract is what makes WF1 applicable to the
*projection* of an interleaved behavior, whose steps are not the component's
`M.next` (`leadsTo_of_wf1` below is the `T = M.next` case, exactly as
`eventually_zero_of_weakFair_inv` is derived from `eventually_zero_of_seq`). -/
theorem leadsTo_of_wf1_seq {T A : Action σ} {P Q : Nondet σ} {b : Behavior σ}
    (hbeh : ∀ n, rel T (b n) (b (n + 1))) (hfair : WeakFair A b)
    (hprog : ∀ s s', P s → ¬ Q s → rel A s s' → Q s')
    (henv : ∀ s s', P s → ¬ Q s → rel T s s' → (P s' ∧ ¬ Q s') ∨ Q s')
    (henabled : ∀ s, P s → ¬ Q s → Enabled A s) :
    LeadsTo P Q b := by
  intro n hn
  by_cases hgoal : ∃ m, n ≤ m ∧ Q (b m)
  · obtain ⟨m, hnm, hm⟩ := hgoal
    exact ⟨m, hnm, hm⟩
  · have hno : ∀ m, n ≤ m → ¬ Q (b m) := fun m hnm hm => hgoal ⟨m, hnm, hm⟩
    have hstable : ∀ m, n ≤ m → P (b m) ∧ ¬ Q (b m) := by
      intro m hnm
      induction hnm with
      | refl => exact ⟨hn, hno _ (Nat.le_refl n)⟩
      | step hnm ih =>
          obtain ⟨hPm, hQm⟩ := ih
          rcases henv _ _ hPm hQm (hbeh _) with h | h
          · exact h
          · exact absurd h (hno _ (Nat.le_succ_of_le hnm))
    have hen : ∀ m, n ≤ m → Enabled A (b m) :=
      fun m hm => henabled _ (hstable m hm).1 (hstable m hm).2
    obtain ⟨m, hnm, htaken⟩ := hfair n hen
    have hQ := hprog _ _ (hstable m hnm).1 (hstable m hnm).2 htaken
    exact absurd hQ (hno _ (Nat.le_succ_of_le hnm))

/-- **WF1.** The module-level rule (`leadsTo_of_wf1_seq` at `T = M.next`). If,
from `P ∧ ¬Q`:
* every step of `A` reaches `Q` (`hprog`),
* every step of the module either reaches `Q` or keeps `P ∧ ¬Q` (`henv`),
* `A` stays enabled (`henabled`),
then weak fairness for `A` yields `LeadsTo P Q`. This is the TLA+ WF1 rule with
the invariant specialized to `P ∧ ¬Q` (no primed variables: `P s'`, `Q s'` play
the primed roles), and it needs no measure at all.

NB: `hprog` is on *all* `A`-steps, stuttering ones included. TLA instead uses
`⟨A⟩_v`, where stuttering steps do not count; `leadsTo_of_wf1_nonStutter` below
is that version (fairness of `nonStutter A`). -/
theorem leadsTo_of_wf1 {M : Module σ} {A : Action σ} {P Q : Nondet σ} {b : Behavior σ}
    (hbeh : IsBehavior M b) (hfair : WeakFair A b)
    (hprog : ∀ s s', P s → ¬ Q s → rel A s s' → Q s')
    (henv : ∀ s s', P s → ¬ Q s → rel M.next s s' → (P s' ∧ ¬ Q s') ∨ Q s')
    (henabled : ∀ s, P s → ¬ Q s → Enabled A s) :
    LeadsTo P Q b :=
  leadsTo_of_wf1_seq (T := M.next) hbeh hfair hprog henv henabled

/-- **WF1 with a stuttering progress action** — TLA's `⟨A⟩` / `⟨A⟩_v` version.
If `A` may stutter (e.g. `guard P <|> skip`), requiring *every* `A`-step to reach
`Q` is too strong. Here fairness is required for `nonStutter A`, and `hprog` only
has to reach `Q` when the state actually changes. -/
theorem leadsTo_of_wf1_seq_nonStutter {T A : Action σ} {P Q : Nondet σ} {b : Behavior σ}
    (hbeh : ∀ n, rel T (b n) (b (n + 1))) (hfair : WeakFair (nonStutter A) b)
    (hprog : ∀ s s', P s → ¬ Q s → rel A s s' → s' ≠ s → Q s')
    (henv : ∀ s s', P s → ¬ Q s → rel T s s' → (P s' ∧ ¬ Q s') ∨ Q s')
    (henabled : ∀ s, P s → ¬ Q s → Enabled (nonStutter A) s) :
    LeadsTo P Q b :=
  leadsTo_of_wf1_seq (T := T) (A := nonStutter A) hbeh hfair
    (fun s s' hP hQ h =>
      hprog s s' hP hQ (rel_nonStutter.mp h).1 (rel_nonStutter.mp h).2)
    henv henabled

/-- Module-level `⟨A⟩`-WF1 (`leadsTo_of_wf1_seq_nonStutter` at `T = M.next`). -/
theorem leadsTo_of_wf1_nonStutter {M : Module σ} {A : Action σ} {P Q : Nondet σ}
    {b : Behavior σ} (hbeh : IsBehavior M b) (hfair : WeakFair (nonStutter A) b)
    (hprog : ∀ s s', P s → ¬ Q s → rel A s s' → s' ≠ s → Q s')
    (henv : ∀ s s', P s → ¬ Q s → rel M.next s s' → (P s' ∧ ¬ Q s') ∨ Q s')
    (henabled : ∀ s, P s → ¬ Q s → Enabled (nonStutter A) s) :
    LeadsTo P Q b :=
  leadsTo_of_wf1_seq_nonStutter (T := M.next) hbeh hfair hprog henv henabled

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

/-- **Rank progress along a sequence, with stuttering steps allowed.**

The hypotheses are stated on the sequence itself rather than through a module, so
that the theorem applies to *projections* of product behaviors: projecting an
interleaving onto one component yields a sequence in which the other component's
steps appear as stuttering steps, and it is not a behavior of the component
module. This is the engine that the module-level versions below are derived
from.

This is the `Nat` counterpart of `wf_progress_false` (`r := (· < ·)`), with
every hypothesis conditioned on `μ > 0` rather than assumed globally; the
sequence-level statement is what stays applicable after a projection, so it is
kept rather than reduced to the module-level form. -/
theorem eventually_zero_of_seq {μ : σ → Nat} {b : Behavior σ} {A : Action σ} {I : Nondet σ}
    (hI : ∀ n, μ (b n) > 0 → I (b n))
    (hdec : ∀ n, I (b n) → μ (b n) > 0 → μ (b (n + 1)) ≤ μ (b n))
    (hA : ∀ n, I (b n) → μ (b n) > 0 → rel A (b n) (b (n + 1)) → μ (b (n + 1)) < μ (b n))
    (henabled : ∀ n, I (b n) → μ (b n) > 0 → ∃ s', rel A (b n) s')
    (hfair : WeakFair A b) : ∀ n, ∃ N, n ≤ N ∧ μ (b N) = 0 := by
  have key : ∀ k, ∀ n, μ (b n) = k → ∃ N, n ≤ N ∧ μ (b N) = 0 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n hn
      by_cases hzero : μ (b n) = 0
      · exact ⟨n, Nat.le_refl n, hzero⟩
      · by_cases hreached : ∃ N, n ≤ N ∧ μ (b N) = 0
        · exact hreached
        · have hpos : ∀ m, n ≤ m → μ (b m) > 0 := fun m hm =>
            Nat.pos_of_ne_zero fun hz => hreached ⟨m, hm, hz⟩
          have hmono_prefix : ∀ d : Nat, μ (b (n + d)) ≤ μ (b n) := by
            intro d
            induction d with
            | zero => exact Nat.le_refl _
            | succ d ihd =>
              have hd : μ (b (n + d)) > 0 := hpos _ (Nat.le_add_right n d)
              have hstep : μ (b (n + d + 1)) ≤ μ (b (n + d)) := by
                have := hdec (n + d) (hI _ hd) hd
                simpa [Nat.add_assoc] using this
              exact Nat.le_trans hstep ihd
          have hen : ∀ m, n ≤ m → ∃ s', rel A (b m) s' :=
            fun m hm => henabled m (hI _ (hpos m hm)) (hpos m hm)
          obtain ⟨m, hnm, htaken⟩ := hfair n hen
          have hposm : μ (b m) > 0 := hpos m hnm
          have hlt : μ (b (m + 1)) < μ (b m) := hA m (hI _ hposm) hposm htaken
          have hle : μ (b m) ≤ μ (b n) := by
            have hd : n + (m - n) = m := by omega
            simpa [hd] using hmono_prefix (m - n)
          have hltk : μ (b (m + 1)) < k := by omega
          obtain ⟨N, hN, hz⟩ := ih (μ (b (m + 1))) hltk (m + 1) rfl
          exact ⟨N, Nat.le_trans (Nat.le_trans hnm (Nat.le_succ m)) hN, hz⟩
  intro n
  exact key (μ (b n)) n rfl

/-- **Fairness-based inevitability, restricted to an invariant region.**

The hypotheses only have to hold on states satisfying `I`, and `I` only has to
hold while the rank is still positive (`hI`). This is the form needed for
shared-memory protocols, where the rank is not globally monotone: once a process
has left the region of interest the measure may go up again, but by then it has
already reached zero.

* `henabled` gives the progress action whenever the rank is positive,
* `hA` says a progress step strictly decreases the rank there,
* `hdec` says no step increases it there,
* `hfair` is weak fairness for the progress action. -/
theorem eventually_zero_of_weakFair_inv {M : Module σ} {A : Action σ} {μ : σ → Nat}
    {b : Behavior σ} {I : Nondet σ} (hbeh : IsBehavior M b)
    (hI : ∀ n, μ (b n) > 0 → I (b n))
    (hdec : ∀ s s', I s → μ s > 0 → rel M.next s s' → μ s' ≤ μ s)
    (hA : ∀ s, I s → μ s > 0 → ∀ s', rel A s s' → μ s' < μ s)
    (henabled : ∀ s, I s → μ s > 0 → ∃ s', rel A s s')
    (hfair : WeakFair A b) : ∀ n, ∃ N, n ≤ N ∧ μ (b N) = 0 :=
  eventually_zero_of_seq
    (hI := hI)
    (hdec := fun n hIn hpos => hdec (b n) (b (n + 1)) hIn hpos (hbeh n))
    (hA := fun _ hIn hpos hstep => hA _ hIn hpos _ hstep)
    (henabled := fun _ hIn hpos => henabled _ hIn hpos)
    hfair

/-- **Fairness-based inevitability.** If the progress action `A` strictly
decreases the rank while the goal is not reached, every module step keeps the
rank from increasing, `A` stays enabled as long as the rank is positive, and the
behavior is weakly fair for `A`, then the rank reaches zero eventually after any
time. -/
theorem eventually_zero_of_weakFair {M : Module σ} {A : Action σ} {μ : σ → Nat}
    {b : Behavior σ} (hbeh : IsBehavior M b)
    (hA : ∀ s, μ s > 0 → ∀ s', rel A s s' → μ s' < μ s)
    (henv : ∀ s s', μ s > 0 → rel M.next s s' → μ s' ≤ μ s)
    (henabled : ∀ s, μ s > 0 → ∃ s', rel A s s')
    (hfair : WeakFair A b) : ∀ n, ∃ N, n ≤ N ∧ μ (b N) = 0 :=
  eventually_zero_of_weakFair_inv (I := fun _ => True) hbeh
    (fun _ _ => trivial)
    (fun s s' _ hs h => henv s s' hs h)
    (fun s _ hs s' h => hA s hs s' h)
    (fun s _ hs => henabled s hs)
    hfair

/-- Strong-fairness version of `eventually_zero_of_weakFair_inv`
(strong fairness implies weak fairness). -/
theorem eventually_zero_of_strongFair_inv {M : Module σ} {A : Action σ} {μ : σ → Nat}
    {b : Behavior σ} {I : Nondet σ} (hbeh : IsBehavior M b)
    (hI : ∀ n, μ (b n) > 0 → I (b n))
    (hdec : ∀ s s', I s → μ s > 0 → rel M.next s s' → μ s' ≤ μ s)
    (hA : ∀ s, I s → μ s > 0 → ∀ s', rel A s s' → μ s' < μ s)
    (henabled : ∀ s, I s → μ s > 0 → ∃ s', rel A s s')
    (hfair : StrongFair A b) : ∀ n, ∃ N, n ≤ N ∧ μ (b N) = 0 :=
  eventually_zero_of_weakFair_inv hbeh hI hdec hA henabled hfair.toWeakFair

/-- `LeadsTo` form of `eventually_zero_of_weakFair_inv`. -/
theorem leadsTo_zero_of_weakFair_inv {M : Module σ} {A : Action σ} {μ : σ → Nat}
    {b : Behavior σ} {I : Nondet σ} (hbeh : IsBehavior M b)
    (hI : ∀ n, μ (b n) > 0 → I (b n))
    (hdec : ∀ s s', I s → μ s > 0 → rel M.next s s' → μ s' ≤ μ s)
    (hA : ∀ s, I s → μ s > 0 → ∀ s', rel A s s' → μ s' < μ s)
    (henabled : ∀ s, I s → μ s > 0 → ∃ s', rel A s s')
    (hfair : WeakFair A b) : LeadsTo (fun _ : σ => True) (fun s => μ s = 0) b :=
  fun n _ => eventually_zero_of_weakFair_inv hbeh hI hdec hA henabled hfair n

/-- `LeadsTo` form of `eventually_zero_of_weakFair`. -/
theorem leadsTo_zero_of_weakFair {M : Module σ} {A : Action σ} {μ : σ → Nat}
    {b : Behavior σ} (hbeh : IsBehavior M b)
    (hA : ∀ s, μ s > 0 → ∀ s', rel A s s' → μ s' < μ s)
    (henv : ∀ s s', μ s > 0 → rel M.next s s' → μ s' ≤ μ s)
    (henabled : ∀ s, μ s > 0 → ∃ s', rel A s s')
    (hfair : WeakFair A b) : LeadsTo (fun _ : σ => True) (fun s => μ s = 0) b :=
  fun n _ => eventually_zero_of_weakFair hbeh hA henv henabled hfair n

/-! ## WF1 meets the rank argument

The rank theorems above assume their invariant *globally* (`hI : ∀ n, μ (b n) > 0
→ I (b n)`). For a shared-memory protocol that is too strong: after an enter/exit
cycle the process is back outside the region with `μ > 0`. The usual workaround is
a `by_cases (∃ N, Q (b N))` around the rank argument; this rule packages that
split once, replacing the global invariant by the **stepwise** stability of
`P ∧ ¬Q` — exactly WF1's `henv`. -/

/-- **No infinite descent.** A sequence whose value never increases (`hdec`, in
the `=`-or-strictly-below sense) in a transitive well-founded order, which
strictly decreases (`hprog`) at a step that weak fairness guarantees (`hfair`,
with `A` always enabled), is impossible. This is the `by_cases`-free engine of
`leadsTo_of_rank_region` below.

The `Nat` sequence engines (`eventually_zero_of_seq` and the module-level
theorems derived from it) are the same argument at `r := (· < ·)` with the
hypotheses only required while `μ > 0`; they are stated at the sequence level
because projections of product behaviors are sequence-indexed and not behaviors
of the component module. -/
theorem wf_progress_false {W : Type} {r : W → W → Prop} (hwf : WellFounded r)
    (htrans : ∀ ⦃a b c : W⦄, r a b → r b c → r a c)
    {μ : σ → W} {A : Action σ} {b : Behavior σ}
    (hdec : ∀ n, μ (b (n + 1)) = μ (b n) ∨ r (μ (b (n + 1))) (μ (b n)))
    (hfair : WeakFair A b) (hen : ∀ n, Enabled A (b n))
    (hprog : ∀ n, rel A (b n) (b (n + 1)) → r (μ (b (n + 1))) (μ (b n))) :
    False := by
  let f : Nat → W := fun n => μ (b n)
  have hfdec : ∀ n, f (n + 1) = f n ∨ r (f (n + 1)) (f n) := hdec
  have hchain : ∀ n d, f (n + d) = f n ∨ r (f (n + d)) (f n) := by
    intro n d
    induction d with
    | zero => exact Or.inl (by rw [Nat.add_zero])
    | succ d ih =>
        have hs := hfdec (n + d)
        rw [Nat.add_succ] at hs ⊢
        rcases ih with heq | hlt
        · rcases hs with heq2 | hlt2
          · exact Or.inl (heq2.trans heq)
          · exact Or.inr (by rwa [heq] at hlt2)
        · rcases hs with heq2 | hlt2
          · exact Or.inr (by rwa [heq2])
          · exact Or.inr (htrans hlt2 hlt)
  let C : W → Prop := fun w => ∀ n, f n = w → ∀ j, n ≤ j → ¬ r (f (j + 1)) (f j)
  have hC : ∀ w, C w := fun w =>
    hwf.induction (C := C) w (fun x ih => by
      intro n hn j hj hAj
      have hd : f j = f n ∨ r (f j) (f n) := by
        have := hchain n (j - n)
        rwa [Nat.add_sub_of_le hj] at this
      have hdown : r (f (j + 1)) x := by
        rw [← hn]
        rcases hd with heq | hlt
        · simpa [heq] using hAj
        · exact htrans hAj hlt
      obtain ⟨j', hj', hAj'⟩ := hfair (j + 1) (fun m _ => hen m)
      exact ih (f (j + 1)) hdown (j + 1) rfl j' hj' (hprog j' hAj'))
  obtain ⟨j, -, hAj⟩ := hfair 0 (fun m _ => hen m)
  exact hC (f 0) 0 rfl j (Nat.zero_le j) (hprog j hAj)

/-- **`LeadsTo` from a stepwise-stable region plus a well-founded rank.** If,
from `P ∧ ¬Q`,
* every step either reaches `Q` or keeps `P ∧ ¬Q` (`hstab` — WF1's `henv`),
* `P ∧ ¬Q` implies the rank invariant `I` (`hreg`),
* no step increases `μ` on `I` (`hdec`, `μ s' = μ s` or `μ s' ≺ μ s`),
* the progress action `A` decreases `μ` strictly on `I` (`hprog`) and stays
  enabled there (`henab`),
then weak fairness for `A` gives `LeadsTo P Q`.

The `by_cases` that global-invariant rank proofs carry by hand is discharged here
once, by induction on the prefix: as long as `Q` has not occurred, `P ∧ ¬Q` is
stable, so `I` holds and `wf_progress_false` closes the contradiction. This is the
rule-of-thumb for RG liveness as well: with `T := A₁ <|> A₂`, `hstab`/`hdec` split
by component and the environment half is the "under the rely, the variant does not
increase" obligation.

The rank is general (`W` with a well-founded `r`) rather than `Nat`. Two order
facts are needed: well-foundedness, and *transitivity* (Lean's
`WellFoundedRelation` does not bundle the latter) — `hdec` is stated as
"equal or strictly below" rather than `¬ r (μ s) (μ s')` precisely so that the
hypothesis composes along the prefix without `r` being total. -/
theorem leadsTo_of_rank_region {T A : Action σ} {P Q I : Nondet σ} {W : Type}
    {r : W → W → Prop} (hwf : WellFounded r)
    (htrans : ∀ ⦃a b c : W⦄, r a b → r b c → r a c) {μ : σ → W} {b : Behavior σ}
    (hbeh : ∀ n, rel T (b n) (b (n + 1))) (hfair : WeakFair A b)
    (hstab : ∀ s s', P s → ¬ Q s → rel T s s' → (P s' ∧ ¬ Q s') ∨ Q s')
    (hreg : ∀ s, P s → ¬ Q s → I s)
    (hdec : ∀ s s', I s → ¬ Q s → rel T s s' → μ s' = μ s ∨ r (μ s') (μ s))
    (hprog : ∀ s, I s → ¬ Q s → ∀ s', rel A s s' → r (μ s') (μ s))
    (henab : ∀ s, I s → ¬ Q s → Enabled A s) :
    LeadsTo P Q b := by
  intro n hn
  by_cases hreached : ∃ m, n ≤ m ∧ Q (b m)
  · exact hreached
  · have hno : ∀ m, n ≤ m → ¬ Q (b m) := fun m hm hq => hreached ⟨m, hm, hq⟩
    -- shift to the time at which the region is known to hold, then run the rank
    -- argument with `I` derived from the prefix where `Q` is still unreached
    let b' : Behavior σ := fun k => b (n + k)
    have hbeh' : ∀ k, rel T (b' k) (b' (k + 1)) := fun k => by
      show rel T (b (n + k)) (b (n + k + 1))
      exact hbeh (n + k)
    have hstable' : ∀ k, P (b' k) ∧ ¬ Q (b' k) := by
      intro k
      induction k with
      | zero => exact ⟨hn, hno n (Nat.le_refl n)⟩
      | succ k ih =>
          rcases hstab _ _ ih.1 ih.2 (hbeh' k) with h | h
          · exact h
          · exact absurd h (hno (n + (k + 1)) (by omega))
    have hI' : ∀ k, I (b' k) := fun k => hreg _ (hstable' k).1 (hstable' k).2
    have hdec' : ∀ k, μ (b' (k + 1)) = μ (b' k) ∨ r (μ (b' (k + 1))) (μ (b' k)) :=
      fun k => hdec _ _ (hI' k) (hstable' k).2 (hbeh' k)
    have hprog' : ∀ k, rel A (b' k) (b' (k + 1)) → r (μ (b' (k + 1))) (μ (b' k)) :=
      fun k h => hprog _ (hI' k) (hstable' k).2 _ h
    have hen' : ∀ k, Enabled A (b' k) := fun k => henab _ (hI' k) (hstable' k).2
    have hfair' : WeakFair A b' := by simpa [b'] using weakFair_add hfair n
    exact (wf_progress_false hwf htrans hdec' hfair' hen' hprog').elim

/-- A `<` order that is **well-founded and transitive** — exactly the two order
facts `leadsTo_of_rank_region` takes as separate arguments. Register a new rank
order by providing an `LT` instance and a `WFTrans` instance; `Nat` is the
built-in case, and future rank types (lexicographic products, subtypes, …) only
need an instance here. -/
class WFTrans (α : Type u) [LT α] : Prop where
  wf : WellFounded (· < · : α → α → Prop)
  trans : ∀ ⦃a b c : α⦄, a < b → b < c → a < c

instance : WFTrans Nat where
  wf := Nat.lt_wfRel.wf
  trans := fun _ _ _ => Nat.lt_trans

/-- **`leadsTo_of_rank_region` on the registered order.** The common case: the
rank is valued in a type carrying a `WFTrans` instance (`Nat` out of the box), so
the call site no longer passes the well-foundedness/transitivity pair. The
general rule keeps its explicit `r` for orders that are not registered. -/
theorem leadsTo_of_rank_wf {T A : Action σ} {P Q I : Nondet σ}
    {W : Type} [LT W] [WFTrans W] {μ : σ → W} {b : Behavior σ}
    (hbeh : ∀ n, rel T (b n) (b (n + 1))) (hfair : WeakFair A b)
    (hstab : ∀ s s', P s → ¬ Q s → rel T s s' → (P s' ∧ ¬ Q s') ∨ Q s')
    (hreg : ∀ s, P s → ¬ Q s → I s)
    (hdec : ∀ s s', I s → ¬ Q s → rel T s s' → μ s' = μ s ∨ μ s' < μ s)
    (hprog : ∀ s, I s → ¬ Q s → ∀ s', rel A s s' → μ s' < μ s)
    (henab : ∀ s, I s → ¬ Q s → Enabled A s) :
    LeadsTo P Q b :=
  leadsTo_of_rank_region (r := (· < ·)) WFTrans.wf WFTrans.trans
    hbeh hfair hstab hreg hdec hprog henab

/-! ## Compositionality for interleaving

Liveness of an interleaved system from liveness of its components. The two
ingredients are the ones `interleave_safe` uses for safety, plus the fact that a
*liveness* property must be stable for the two eventualities to be combined.

Note that projecting a product behavior onto a component does **not** give a
behavior of the component module: the other component's steps appear as
stuttering steps. That is why `eventually_zero_of_seq` — the sequence-level rank
theorem — is the right engine here. -/

/-- A projected step of an interleaved behavior: the first component either
stutters or is related by the first component's next action. -/
theorem proj_fst_step {M : Module σ} {N : Module τ} {b : Behavior (σ × τ)}
    (hbeh : IsBehavior (M.interleave N) b) (n : Nat) :
    (b (n + 1)).1 = (b n).1 ∨ rel M.next (b n).1 (b (n + 1)).1 := by
  have hstep := hbeh n
  rw [Module.rel_interleave_next] at hstep
  rcases hstep with ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inr h
  · exact Or.inl h

/-- The same for the second component. -/
theorem proj_snd_step {M : Module σ} {N : Module τ} {b : Behavior (σ × τ)}
    (hbeh : IsBehavior (M.interleave N) b) (n : Nat) :
    (b (n + 1)).2 = (b n).2 ∨ rel N.next (b n).2 (b (n + 1)).2 := by
  have hstep := hbeh n
  rw [Module.rel_interleave_next] at hstep
  rcases hstep with ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Product fairness for a lifted action gives component fairness for the
projected behavior. -/
theorem weakFair_fst_of_weakFair {A : Action σ} {b : Behavior (σ × τ)}
    (h : WeakFair (liftLeft A) b) : WeakFair A (fun k => (b k).1) := by
  intro n hen
  have hen' : ∀ m, n ≤ m → ∃ q : σ × τ, rel (liftLeft A) (b m) q := by
    intro m hm
    obtain ⟨s', hs'⟩ := hen m hm
    exact ⟨(s', (b m).2), by simpa [liftLeft] using hs'⟩
  obtain ⟨m, hm, hstep⟩ := h n hen'
  exact ⟨m, hm, (rel_liftLeft.mp hstep).1⟩

/-- The same for the second component. -/
theorem weakFair_snd_of_weakFair {B : Action τ} {b : Behavior (σ × τ)}
    (h : WeakFair (liftRight B) b) : WeakFair B (fun k => (b k).2) := by
  intro n hen
  have hen' : ∀ m, n ≤ m → ∃ q : σ × τ, rel (liftRight B) (b m) q := by
    intro m hm
    obtain ⟨s', hs'⟩ := hen m hm
    exact ⟨((b m).1, s'), by simpa [liftRight] using hs'⟩
  obtain ⟨m, hm, hstep⟩ := h n hen'
  exact ⟨m, hm, (rel_liftRight.mp hstep).1⟩

/-- A preserved predicate is stable forward along a behavior. This is what makes
two eventualities combinable: once `P` holds it keeps holding. -/
theorem forward_stable_of_preserves {M : Module σ} {P : Nondet σ} {b : Behavior σ}
    (hbeh : IsBehavior M b) (hP : Preserves M.next P) :
    ∀ n m, n ≤ m → P (b n) → P (b m) := by
  intro n m hnm
  induction hnm with
  | refl => exact id
  | step _ ih => exact fun h => hP _ (ih h) _ (hbeh _)

/-- Component preservation lifts to the product (first component). -/
theorem interleave_preserves_fst {M : Module σ} {N : Module τ} {P : Nondet σ}
    (hP : Preserves M.next P) : Preserves (M.interleave N).next (fun p => P p.1) := by
  intro p hp q hstep
  rw [Module.rel_interleave_next] at hstep
  rcases hstep with ⟨h, -⟩ | ⟨-, h⟩
  · exact hP _ hp _ h
  · rw [h]; exact hp

/-- Component preservation lifts to the product (second component). -/
theorem interleave_preserves_snd {M : Module σ} {N : Module τ} {Q : Nondet τ}
    (hQ : Preserves N.next Q) : Preserves (M.interleave N).next (fun p => Q p.2) := by
  intro p hp q hstep
  rw [Module.rel_interleave_next] at hstep
  rcases hstep with ⟨-, h⟩ | ⟨h, -⟩
  · rw [h]; exact hp
  · exact hQ _ hp _ h

/-- **Liveness of an interleaving composes.** If the first component eventually
reaches `P` (along the projected behavior) and `P` is preserved by its module,
and likewise for `Q`, then the product eventually reaches `P ∧ Q`: the
preservation hypotheses are what let the two eventualities be combined (take the
later of the two times). -/
theorem interleave_leadsTo {M : Module σ} {N : Module τ} {P : Nondet σ} {Q : Nondet τ}
    {b : Behavior (σ × τ)} (hbeh : IsBehavior (M.interleave N) b)
    (hPpres : Preserves M.next P) (hQpres : Preserves N.next Q)
    (hP : LeadsTo (fun _ : σ => True) P (fun k => (b k).1))
    (hQ : LeadsTo (fun _ : τ => True) Q (fun k => (b k).2)) :
    LeadsTo (fun _ : σ × τ => True) (fun p => P p.1 ∧ Q p.2) b := by
  have hPstab := forward_stable_of_preserves (M := M.interleave N) hbeh
    (interleave_preserves_fst (N := N) hPpres)
  have hQstab := forward_stable_of_preserves (M := M.interleave N) hbeh
    (interleave_preserves_snd (M := M) hQpres)
  intro n _
  obtain ⟨m, hnm, hm⟩ := hP n trivial
  obtain ⟨k, hnk, hk⟩ := hQ n trivial
  exact ⟨max m k, Nat.le_trans hnm (Nat.le_max_left m k),
    hPstab m (max m k) (Nat.le_max_left m k) hm,
    hQstab k (max m k) (Nat.le_max_right m k) hk⟩

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
