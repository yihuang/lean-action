/-
Examples.Frame
==============

Shared-state composition through **disjoint footprints** (the frame assumption
made explicit).

* The state is one record holding both components (`Two`), not a product: the
  footprint of each component is a *view* into it.
* `Disjoint fp₁ fp₂` is a proof obligation, discharged once by `cases s; rfl`.
* `ViewModule.parallel_safe` then gives the composed safety property, where each
  half is proved **only** about the component's own state (`n = log.length`) —
  no global case analysis over the interleavings.
* Liveness composes the same way, and the mutex processes are proved *not*
  disjoint, which is why that protocol still needs a hand-written invariant.
-/
import LeanAction
import Examples.Mutex

open LeanAction

namespace Examples.Frame

/-! ## A shared record with two footprints -/

/-- Shared state: two counters, each with its own audit log. -/
structure Two where
  n₁ : Nat
  n₂ : Nat
  l₁ : List Nat
  l₂ : List Nat

/-- Footprint of the first component: its counter and its log. -/
def fp₁ : View Two (Nat × List Nat) :=
  ⟨fun s => (s.n₁, s.l₁), fun s v => { s with n₁ := v.1, l₁ := v.2 }⟩

/-- Footprint of the second component. -/
def fp₂ : View Two (Nat × List Nat) :=
  ⟨fun s => (s.n₂, s.l₂), fun s v => { s with n₂ := v.1, l₂ := v.2 }⟩

/-- **The frame assumption**, as a proof obligation: the two footprints do not
interfere. -/
theorem disjoint_fp : Disjoint fp₁ fp₂ := by disjoint_auto

/-! ## The components, each described on its own state type -/

/-- Increment and log the previous value. -/
def step : Action (Nat × List Nat) := do
  let s ← (ActionM.get : ActionM (Nat × List Nat) (Nat × List Nat))
  ActionM.modify fun t => (t.1 + 1, s.1 :: t.2)

def C₁ : ViewModule Two (Nat × List Nat) where
  view := fp₁
  get_set := by intro s a; cases s; cases a; rfl
  init := fun s => s.n₁ = 0 ∧ s.l₁ = []
  next := step

def C₂ : ViewModule Two (Nat × List Nat) where
  view := fp₂
  get_set := by intro s a; cases s; cases a; rfl
  init := fun s => s.n₂ = 0 ∧ s.l₂ = []
  next := step

/-- The component's own invariant — proved on `Nat × List Nat` only. -/
theorem inv_step : Preserves step (fun t : Nat × List Nat => t.1 = t.2.length) := by
  inv_induct
  simp only [step] at *
  action_simp
  grind

theorem init_fp₁ : ∀ s, C₁.init s → (fun t : Nat × List Nat => t.1 = t.2.length) (C₁.view.get s) := by
  rintro s ⟨h1, h2⟩
  show s.n₁ = s.l₁.length
  simp [h1, h2]

theorem init_fp₂ : ∀ s, C₂.init s → (fun t : Nat × List Nat => t.1 = t.2.length) (C₂.view.get s) := by
  rintro s ⟨h1, h2⟩
  show s.n₂ = s.l₂.length
  simp [h1, h2]

/-- **The frame theorem in action.** The composed system satisfies both component
invariants, although each half was proved only about one component's state. -/
theorem two_safe : (C₁.parallel C₂).Safe
    (fun s : Two => s.n₁ = s.l₁.length ∧ s.n₂ = s.l₂.length) := by
  have h := ViewModule.parallel_safe (M₁ := C₁) (M₂ := C₂) disjoint_fp
    init_fp₁ init_fp₂ inv_step inv_step
  show (C₁.parallel C₂).Safe (fun s : Two => s.n₁ = s.l₁.length ∧ s.n₂ = s.l₂.length)
  exact h

/-! ## Liveness through the same frame

Targets: the first counter reaches 3, the second reaches 4. The rank lives on the
*component* state; the projection stutters when the other component moves, which
is exactly what `ViewModule.proj_step` and the sequence-level rank theorem
(`eventually_zero_of_seq`) handle. -/

def μ (k : Nat) (t : Nat × List Nat) : Nat := k - t.1

theorem step_increments {t t' : Nat × List Nat} (h : rel step t t') : t'.1 = t.1 + 1 := by
  simp only [step] at h
  action_simp
  grind

theorem step_enabled (t : Nat × List Nat) : ∃ q, rel step t q :=
  ⟨(t.1 + 1, t.1 :: t.2), by simp only [step]; action_simp; grind⟩

/-- Liveness of one component of the composition, at target `k`: it only uses the
component's *own* increment/enabledness facts and fairness for its lifted action,
plus disjointness to know that the other component's steps stutter. -/
theorem component_live (k : Nat) {M M' : ViewModule Two (Nat × List Nat)}
    (hd : Disjoint M.view M'.view) (hbeh : IsBehavior (M.parallel M') b)
    (hinc : ∀ t t', rel M.next t t' → t'.1 = t.1 + 1)
    (hen : ∀ t, ∃ q, rel M.next t q)
    (hfair : WeakFair (focusView M.view M.next) b) :
    LeadsTo (fun _ : Nat × List Nat => True) (fun t => t.1 ≥ k) (fun n => M.view.get (b n)) := by
  intro n _
  have hwf : WeakFair M.next (fun n => M.view.get (b n)) :=
    ViewModule.weakFair_of_lift M.get_set hfair
  have hdec : ∀ m, μ k (M.view.get (b m)) > 0 →
      μ k (M.view.get (b (m + 1))) ≤ μ k (M.view.get (b m)) := by
    intro m _
    rcases ViewModule.proj_step hd hbeh m with hstut | hstep
    · have h' : M.view.get (b (m + 1)) = M.view.get (b m) := hstut
      rw [h']
      exact Nat.le_refl _
    · simp only [μ]
      rw [hinc _ _ hstep]
      omega
  have hA : ∀ m, μ k (M.view.get (b m)) > 0 →
      rel M.next (M.view.get (b m)) (M.view.get (b (m + 1))) →
      μ k (M.view.get (b (m + 1))) < μ k (M.view.get (b m)) := by
    intro m hpos hstep
    simp only [μ] at hpos ⊢
    rw [hinc _ _ hstep]
    omega
  have henabled : ∀ m, μ k (M.view.get (b m)) > 0 → ∃ q, rel M.next (M.view.get (b m)) q :=
    fun m _ => hen _
  obtain ⟨N, hN, hz⟩ := eventually_zero_of_seq (A := M.next)
    (I := fun _ : Nat × List Nat => True) (μ := μ k) (b := fun n => M.view.get (b n))
    (fun _ _ => trivial) (fun m _ h => hdec m h) (fun m _ hpos h => hA m hpos h)
    (fun m _ hpos => henabled m hpos) hwf n
  have hz' : k - (M.view.get (b N)).1 = 0 := hz
  refine ⟨N, hN, ?_⟩
  show (M.view.get (b N)).1 ≥ k
  omega

theorem ge_preserves (k : Nat) : Preserves step (fun t : Nat × List Nat => t.1 ≥ k) := by
  inv_induct
  simp only [step] at *
  action_simp
  grind

/-- **Composed liveness on the shared state**, with each component's liveness
proved on its own projection. -/
theorem two_live (b : Behavior Two) (hbeh : IsBehavior (C₁.parallel C₂) b)
    (hf₁ : WeakFair (focusView C₁.view step) b) (hf₂ : WeakFair (focusView C₂.view step) b) :
    LeadsTo (fun _ : Two => True) (fun s => s.n₁ ≥ 3 ∧ s.n₂ ≥ 4) b := by
  have h := ViewModule.parallel_leadsTo (M₁ := C₁) (M₂ := C₂) disjoint_fp hbeh
    (ge_preserves 3) (ge_preserves 4)
    (component_live 3 (M := C₁) (M' := C₂) disjoint_fp hbeh
      (fun _ _ h => step_increments h) (fun _ => step_enabled _) hf₁)
    (component_live 4 (M := C₂) (M' := C₁) disjoint_fp.symm
      (ViewModule.isBehavior_parallel_swap hbeh)
      (fun _ _ h => step_increments h) (fun _ => step_enabled _) hf₂)
  show LeadsTo (fun _ : Two => True) (fun s : Two => s.n₁ ≥ 3 ∧ s.n₂ ≥ 4) b
  exact h

/-! ## Stepping together (synchronous composition)

`ViewModule.sync` runs both components in lock-step. `Disjoint.set_set` is what
makes the two updates order-independent, and — unlike the interleaving — a
simultaneous step advances *both* projections. -/

theorem sync_advances_both (s s' : Two) (h : rel (C₁.sync C₂) s s') :
    s'.n₁ = s.n₁ + 1 ∧ s'.n₂ = s.n₂ + 1 := by
  obtain ⟨a', b', ha', h₁, hb', h₂⟩ := ViewModule.sync_proj disjoint_fp h
  have h₁' : s'.n₁ = a'.1 := by simpa [C₁, fp₁] using congrArg Prod.fst h₁
  have h₂' : s'.n₂ = b'.1 := by simpa [C₂, fp₂] using congrArg Prod.fst h₂
  refine ⟨?_, ?_⟩
  · rw [h₁', step_increments ha']
    rfl
  · rw [h₂', step_increments hb']
    rfl

theorem two_sync_safe : (C₁.syncModule C₂).Safe
    (fun s : Two => s.n₁ = s.l₁.length ∧ s.n₂ = s.l₂.length) := by
  have h := ViewModule.syncModule_safe (M₁ := C₁) (M₂ := C₂) disjoint_fp
    init_fp₁ init_fp₂ inv_step inv_step
  show (C₁.syncModule C₂).Safe (fun s : Two => s.n₁ = s.l₁.length ∧ s.n₂ = s.l₂.length)
  exact h

/-! ## Where the frame assumption fails: the mutex protocol

Both processes of `Examples.Mutex` write `turn`, so no disjointness proof exists,
and the hand-written global invariant (with `action_simp; grind` over the six
process steps) is genuinely necessary there. -/

/-- Footprint of mutex process 1: its program counter and the shared turn. -/
def mutexP₁ : View Mutex.St (Nat × Nat) :=
  ⟨fun s => (s.pc1, s.turn), fun s v => { s with pc1 := v.1, turn := v.2 }⟩

/-- Footprint of mutex process 2: it also writes the shared turn. -/
def mutexP₂ : View Mutex.St (Nat × Nat) :=
  ⟨fun s => (s.pc2, s.turn), fun s v => { s with pc2 := v.1, turn := v.2 }⟩

theorem mutex_not_disjoint : ¬ Disjoint mutexP₁ mutexP₂ := by
  intro h
  have hh := h.set_set (⟨0, 0, 1⟩ : Mutex.St) (⟨1, 1⟩ : Nat × Nat) (⟨1, 2⟩ : Nat × Nat)
  have : (1 : Nat) = 2 := by
    simpa [mutexP₁, mutexP₂] using congrArg Mutex.St.turn hh
  omega

end Examples.Frame
