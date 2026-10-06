/-
LeanAction.Frame
================

Shared-state composition through **footprints**: what `Module.interleave` can
only do for a literal product state, this file does for an arbitrary state with
two *disjoint* views into it.

The missing ingredient for shared state is the **frame condition**: a component
touching one part of the state must provably leave the other parts alone. Here it
is spelled out as commutation of two views (`Disjoint`), and from it come

* `Disjoint.get_of_rel` — a focused action does not move the other projection;
* `Preserves.focus` — a component invariant lifts to the shared state;
* `ViewModule.parallel_preserves` — **the frame theorem**: an interleaved step
  preserves `P ∧ Q` where each component only proves its own half;
* `ViewModule.parallel_safe` and `ViewModule.parallel_leadsTo` — safety and
  liveness of the composed shared-state system.

Disjointness is not a technicality: `Examples/Frame.lean` proves that the two
processes of the mutex protocol are **not** disjoint (they share `turn`), which is
exactly why that example still needs a hand-written global invariant and why the
next step up is rely/guarantee.
-/
import LeanAction.Lens
import LeanAction.Proof
import LeanAction.Liveness

universe u

namespace LeanAction

open Nondet

variable {σ α β : Type u}

/-! ## Disjoint footprints -/

/-- Two views have disjoint footprints. Expressed as commutation (there are no
variable names at this level, so "disjoint" has to mean "each one's effect is
invisible to the other"). -/
structure Disjoint (v₁ : View σ α) (v₂ : View σ β) : Prop where
  /-- Writing through `v₁` does not change what `v₂` reads. -/
  get_set : ∀ s a, v₂.get (v₁.set s a) = v₂.get s
  /-- Writing through `v₂` does not change what `v₁` reads. -/
  set_get : ∀ s b, v₁.get (v₂.set s b) = v₁.get s
  /-- The two updates commute. -/
  set_set : ∀ s a b, v₁.set (v₂.set s b) a = v₂.set (v₁.set s a) b

theorem Disjoint.symm {v₁ : View σ α} {v₂ : View σ β} (h : Disjoint v₁ v₂) :
    Disjoint v₂ v₁ where
  get_set := h.set_get
  set_get := h.get_set
  set_set := fun s a b => (h.set_set s b a).symm

/-- The two projections of a product have disjoint footprints. -/
theorem disjoint_fst_snd :
    Disjoint (View.ofLens (Lens.fst : Lens (σ × β) σ))
      (View.ofLens (Lens.snd : Lens (σ × β) β)) where
  get_set := by intro p a; rfl
  set_get := by intro p b; rfl
  set_set := by intro p a b; rfl

/-! ## Frame lemmas -/

/-- **A focused action does not move the other projection.** This is the frame
condition in its most used form. -/
theorem Disjoint.get_of_rel {v₁ : View σ α} {v₂ : View σ β} (h : Disjoint v₁ v₂)
    {A : Action α} {s s' : σ} (hr : rel (focusView v₁ A) s s') : v₂.get s' = v₂.get s := by
  obtain ⟨a', -, hs'⟩ := rel_focusView.mp hr
  rw [hs']
  exact h.get_set s a'

/-- A property of one component is invariant under the other component's action. -/
theorem Disjoint.invariant {v₁ : View σ α} {v₂ : View σ β} (h : Disjoint v₁ v₂)
    (A : Action α) (P : Nondet β) : Preserves (focusView v₁ A) (fun s => P (v₂.get s)) := by
  intro s hs s' hr
  change P (v₂.get s) at hs
  change P (v₂.get s')
  rw [h.get_of_rel hr]
  exact hs

/-! ## Lifting component invariants

A component only ever has to reason about its own state type; the projection to
the shared state is handled by `get_set` (writing through a view and reading it
back) and disjointness. -/

theorem Preserves.focusView {v : View σ α} (hget : ∀ s a, v.get (v.set s a) = a)
    {A : Action α} {P : Nondet α} (h : Preserves A P) :
    Preserves (focusView v A) (fun s => P (v.get s)) := by
  intro s hs s' hr
  obtain ⟨a', ha', hs'⟩ := rel_focusView.mp hr
  rw [hs', hget s a']
  exact h _ hs _ ha'

/-- The same for a lawful lens. -/
theorem Preserves.focus {l : Lens σ α} {A : Action α} {P : Nondet α}
    (h : Preserves A P) : Preserves (focus l A) (fun s => P (l.get s)) := by
  intro s hs s' hr
  rw [rel_focus'] at hr
  obtain ⟨hrel, hs'⟩ := hr
  rw [hs', l.get_set]
  exact h _ hs _ hrel

/-! ## Modules with a footprint, and their parallel composition -/

/-- A module together with the **footprint** it writes through: its transition is
an action on its own state type, and it only ever touches the shared state
through `view`. Only `get_set` is required of the view — the other lens laws are
not needed for the frame theorems. -/
structure ViewModule (σ : Type u) (α : Type u) where
  view : View σ α
  get_set : ∀ s a, view.get (view.set s a) = a
  init : Nondet σ
  next : Action α

/-- Build a view module from a lawful lens. -/
def ViewModule.ofLens (l : Lens σ α) (init : Nondet σ) (next : Action α) : ViewModule σ α :=
  ⟨View.ofLens l, l.get_set, init, next⟩

namespace ViewModule

variable {M₁ : ViewModule σ α} {M₂ : ViewModule σ β}

/-- The component's transition, lifted to the shared state. -/
def lift (M : ViewModule σ α) : Action σ := focusView M.view M.next

@[simp] theorem rel_lift {M : ViewModule σ α} {s s' : σ} :
    rel M.lift s s' ↔ ∃ a', rel M.next (M.view.get s) a' ∧ s' = M.view.set s a' := by
  rw [lift]
  exact rel_focusView

/-- Asynchronous (interleaved) composition of two components on a shared state. -/
def parallel (M₁ : ViewModule σ α) (M₂ : ViewModule σ β) : Module σ where
  init := fun s => M₁.init s ∧ M₂.init s
  next := M₁.lift <|> M₂.lift

@[simp] theorem parallel_init {s : σ} :
    (M₁.parallel M₂).init s ↔ M₁.init s ∧ M₂.init s := Iff.rfl

@[simp] theorem rel_parallel_next {s s' : σ} :
    rel (M₁.parallel M₂).next s s' ↔ rel M₁.lift s s' ∨ rel M₂.lift s s' := Iff.rfl

/-- The composition is symmetric: a behavior of `M₁ ∥ M₂` is a behavior of
`M₂ ∥ M₁` (the interleaving is a disjunction, so only the order of the two
branches changes). -/
theorem isBehavior_parallel_swap {M₁ : ViewModule σ α} {M₂ : ViewModule σ β}
    {b : Behavior σ} (h : IsBehavior (M₁.parallel M₂) b) : IsBehavior (M₂.parallel M₁) b := by
  intro n
  have hstep := h n
  rw [rel_parallel_next] at hstep ⊢
  exact hstep.symm

/-- **The frame theorem.** An interleaved step preserves `P ∧ Q` where `P` lives
on the first footprint and `Q` on the second: each component proves only its own
half, and the other half survives by disjointness. -/
theorem parallel_preserves {P : Nondet α} {Q : Nondet β} (hd : Disjoint M₁.view M₂.view)
    (hP : Preserves M₁.next P) (hQ : Preserves M₂.next Q) :
    Preserves (M₁.parallel M₂).next
      (fun s => P (M₁.view.get s) ∧ Q (M₂.view.get s)) := by
  intro s hs s' hr
  rw [rel_parallel_next] at hr
  rcases hr with hr | hr
  · -- a step of the first component: `P` by its invariant, `Q` by the frame
    refine ⟨Preserves.focusView M₁.get_set hP s hs.1 s' hr, ?_⟩
    rw [hd.get_of_rel hr]
    exact hs.2
  · refine ⟨?_, Preserves.focusView M₂.get_set hQ s hs.2 s' hr⟩
    rw [hd.symm.get_of_rel hr]
    exact hs.1

/-- The one-sided form of the frame theorem: the first component's invariant
survives the whole composition. -/
theorem parallel_preserves_fst {P : Nondet α} (hd : Disjoint M₁.view M₂.view)
    (hP : Preserves M₁.next P) :
    Preserves (M₁.parallel M₂).next (fun s => P (M₁.view.get s)) := by
  intro s hs s' hr
  rw [rel_parallel_next] at hr
  rcases hr with hr | hr
  · exact Preserves.focusView M₁.get_set hP s hs s' hr
  · rw [hd.symm.get_of_rel hr]
    exact hs

/-- The other one-sided form. -/
theorem parallel_preserves_snd {Q : Nondet β} (hd : Disjoint M₁.view M₂.view)
    (hQ : Preserves M₂.next Q) :
    Preserves (M₁.parallel M₂).next (fun s => Q (M₂.view.get s)) := by
  intro s hs s' hr
  rw [rel_parallel_next] at hr
  rcases hr with hr | hr
  · rw [hd.get_of_rel hr]
    exact hs
  · exact Preserves.focusView M₂.get_set hQ s hs s' hr

/-- Safety of the composed shared-state system from component invariants. -/
theorem parallel_safe {P : Nondet α} {Q : Nondet β} (hd : Disjoint M₁.view M₂.view)
    (hinit₁ : ∀ s, M₁.init s → P (M₁.view.get s))
    (hinit₂ : ∀ s, M₂.init s → Q (M₂.view.get s))
    (hP : Preserves M₁.next P) (hQ : Preserves M₂.next Q) :
    (M₁.parallel M₂).Safe (fun s => P (M₁.view.get s) ∧ Q (M₂.view.get s)) := by
  apply Module.safe_of_preserves
  · intro s hs
    exact ⟨hinit₁ s hs.1, hinit₂ s hs.2⟩
  · exact parallel_preserves hd hP hQ

/-! ## Liveness -/

/-- A projected step of the composition: the component either stutters (the other
component moved) or takes a step of its own action. -/
theorem proj_step (hd : Disjoint M₁.view M₂.view) {b : Behavior σ}
    (hbeh : IsBehavior (M₁.parallel M₂) b) (n : Nat) :
    M₁.view.get (b (n + 1)) = M₁.view.get (b n) ∨
      rel M₁.next (M₁.view.get (b n)) (M₁.view.get (b (n + 1))) := by
  have hstep := hbeh n
  rw [rel_parallel_next, rel_lift, rel_lift] at hstep
  rcases hstep with ⟨a', hrel, hs'⟩ | ⟨b', hrel, hs'⟩
  · refine Or.inr ?_
    show rel M₁.next (M₁.view.get (b n)) (M₁.view.get (b (n + 1)))
    rw [hs', M₁.get_set]
    exact hrel
  · exact Or.inl (by rw [hs']; exact hd.set_get (b n) b')

/-- Component fairness from fairness of the lifted action. -/
theorem weakFair_of_lift {v : View σ α} (hget : ∀ s a, v.get (v.set s a) = a)
    {A : Action α} {b : Behavior σ}
    (h : WeakFair (focusView v A) b) : WeakFair A (fun k => v.get (b k)) := by
  intro n hen
  have hen' : ∀ m, n ≤ m → ∃ q : σ, rel (focusView v A) (b m) q := by
    intro m hm
    obtain ⟨a', ha'⟩ := hen m hm
    exact ⟨v.set (b m) a', by
      rw [rel_focusView]
      exact ⟨a', ha', rfl⟩⟩
  obtain ⟨m, hm, hstep⟩ := h n hen'
  obtain ⟨a', ha', hs'⟩ := rel_focusView.mp hstep
  refine ⟨m, hm, ?_⟩
  show rel A (v.get (b m)) (v.get (b (m + 1)))
  rw [hs', hget]
  exact ha'

/-- **Liveness of the composition.** From liveness of each component on its own
projection, plus stability of the two targets (their `Preserves`), the shared
state eventually satisfies both. -/
theorem parallel_leadsTo (hd : Disjoint M₁.view M₂.view) {P : Nondet α} {Q : Nondet β}
    {b : Behavior σ} (hbeh : IsBehavior (M₁.parallel M₂) b)
    (hPpres : Preserves M₁.next P) (hQpres : Preserves M₂.next Q)
    (hP : LeadsTo (fun _ : α => True) P (fun k => M₁.view.get (b k)))
    (hQ : LeadsTo (fun _ : β => True) Q (fun k => M₂.view.get (b k))) :
    LeadsTo (fun _ : σ => True) (fun s => P (M₁.view.get s) ∧ Q (M₂.view.get s)) b := by
  have hPstab : ∀ n m, n ≤ m → P (M₁.view.get (b n)) → P (M₁.view.get (b m)) :=
    forward_stable_of_preserves (M := M₁.parallel M₂) (P := fun s => P (M₁.view.get s))
      hbeh (parallel_preserves_fst hd hPpres)
  have hQstab : ∀ n m, n ≤ m → Q (M₂.view.get (b n)) → Q (M₂.view.get (b m)) :=
    forward_stable_of_preserves (M := M₁.parallel M₂) (P := fun s => Q (M₂.view.get s))
      hbeh (parallel_preserves_snd hd hQpres)
  intro n _
  obtain ⟨m, hnm, hm⟩ := hP n trivial
  obtain ⟨k, hnk, hk⟩ := hQ n trivial
  exact ⟨max m k, Nat.le_trans hnm (Nat.le_max_left m k),
    hPstab m (max m k) (Nat.le_max_left m k) hm,
    hQstab k (max m k) (Nat.le_max_right m k) hk⟩

end ViewModule

end LeanAction
