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

/-! ## Rely/guarantee interfaces

`Disjoint` says the environment cannot touch my footprint. Rely/guarantee weakens
this: instead of a footprint, a component declares a **rely** relation (what it
assumes about the environment's steps); the composition rule asks only that each
component's steps are permitted by the other's rely, relative to the invariant.
This is what lets components whose footprints genuinely overlap — the mutex
`turn` — still be composed, and it is also what a *prefix* stability proof
(the region that must hold "until the goal is reached") needs. -/

/-- Two components are compatible with a pair of relies, relative to `I`: each
one's steps are permitted by the other's rely. -/
structure Compatible (I : Nondet σ) (A₁ A₂ : Action σ) (R₁ R₂ : Rel σ σ) : Prop where
  left : ∀ s s', I s → rel A₁ s s' → R₂ s s'
  right : ∀ s s', I s → rel A₂ s s' → R₁ s s'

theorem Compatible.symm {I : Nondet σ} {A₁ A₂ : Action σ} {R₁ R₂ : Rel σ σ}
    (h : Compatible I A₁ A₂ R₁ R₂) : Compatible I A₂ A₁ R₂ R₁ :=
  ⟨h.right, h.left⟩

/-- **Rely/guarantee composition.** If `I` is stable under both relies and each
component's steps are allowed by the other's rely, then the interleaving preserves
`I`. The two stability obligations mention only the *interfaces* — never the other
component's code. -/
theorem Preserves.orElse_of_compatible {A₁ A₂ : Action σ} {I : Nondet σ} {R₁ R₂ : Rel σ σ}
    (hc : Compatible I A₁ A₂ R₁ R₂) (h₁ : ∀ s s', I s → R₁ s s' → I s')
    (h₂ : ∀ s s', I s → R₂ s s' → I s') : Preserves (A₁ <|> A₂) I := by
  intro s hs s' hstep
  rw [rel_orElse] at hstep
  rcases hstep with h | h
  · exact h₂ s s' hs (hc.left s s' hs h)
  · exact h₁ s s' hs (hc.right s s' hs h)

/-- **Prefix stability, relying on the environment.** `I` holds until `G` is
reached: the component's own steps keep `I` or reach `G`, and the environment's
steps keep `I` (its rely, i.e. `A₂ ⊆ (I → I)` here). This is the temporal
companion of `Preserves.orElse_of_compatible`, and it is what a "region that must
hold until the goal" proof needs. -/
theorem relyGuarantee_until {A₁ A₂ : Action σ} {I G : Nondet σ} {b : Behavior σ}
    (hbeh : ∀ n, rel (A₁ <|> A₂) (b n) (b (n + 1)))
    (h₁ : ∀ s s', I s → rel A₁ s s' → I s' ∨ G s')
    (h₂ : ∀ s s', I s → rel A₂ s s' → I s')
    (h₀ : I (b 0)) : ∀ n, (∀ j, j ≤ n → ¬ G (b j)) → I (b n) := by
  intro n
  induction n with
  | zero => intro _; exact h₀
  | succ n ih =>
    intro hG
    have hIn : I (b n) := ih fun j hj => hG j (Nat.le_trans hj (Nat.le_succ n))
    have hstep := hbeh n
    rw [rel_orElse] at hstep
    rcases hstep with h | h
    · rcases h₁ _ _ hIn h with h' | h'
      · exact h'
      · exact absurd h' (hG (n + 1) (Nat.le_refl _))
    · exact h₂ _ _ hIn h

/-! ## Synchronous composition

Both components step at once. `Disjoint.set_set` is what makes the result
independent of the order in which the two updates are applied. -/

namespace ViewModule

variable {M₁ : ViewModule σ α} {M₂ : ViewModule σ β}

/-- Simultaneous execution: both components take a step. An `abbrev` so that its
relation unfolds definitionally (the individual laws below are still `Iff.rfl`). -/
abbrev sync (M₁ : ViewModule σ α) (M₂ : ViewModule σ β) : Action σ :=
  fun s z => ∃ a' b', rel M₁.next (M₁.view.get s) a' ∧ rel M₂.next (M₂.view.get s) b' ∧
    z = (Done.mk, M₂.view.set (M₁.view.set s a') b')

theorem rel_sync {s s' : σ} :
    rel (M₁.sync M₂) s s' ↔ ∃ a' b', rel M₁.next (M₁.view.get s) a' ∧
      rel M₂.next (M₂.view.get s) b' ∧ s' = M₂.view.set (M₁.view.set s a') b' := by
  unfold rel sync
  constructor
  · rintro ⟨a', b', ha', hb', hz⟩
    exact ⟨a', b', ha', hb', congrArg Prod.snd hz⟩
  · rintro ⟨a', b', ha', hb', hs'⟩
    exact ⟨a', b', ha', hb', by rw [hs']⟩

/-- The order of the two updates is irrelevant, thanks to `Disjoint.set_set`. -/
theorem sync_set_comm (hd : Disjoint M₁.view M₂.view) (s : σ) (a' : α) (b' : β) :
    M₂.view.set (M₁.view.set s a') b' = M₁.view.set (M₂.view.set s b') a' :=
  (hd.set_set s a' b').symm

/-- **Synchronous frame theorem.** Both invariants are preserved, and each
component's projection after the step really is its own successor. -/
theorem sync_preserves {P : Nondet α} {Q : Nondet β} (hd : Disjoint M₁.view M₂.view)
    (hP : Preserves M₁.next P) (hQ : Preserves M₂.next Q) :
    Preserves (M₁.sync M₂) (fun s => P (M₁.view.get s) ∧ Q (M₂.view.get s)) := by
  intro s hs s' hr
  obtain ⟨a', b', ha', hb', hs'⟩ := rel_sync.mp hr
  refine ⟨?_, ?_⟩
  · rw [hs', hd.set_get, M₁.get_set]
    exact hP _ hs.1 _ ha'
  · rw [hs', sync_set_comm hd s a' b', hd.get_set, M₂.get_set]
    exact hQ _ hs.2 _ hb'

/-- After a simultaneous step each projection is *exactly* its own successor
(this is what `sync` is for, as opposed to the interleaving where a projected step
may stutter). -/
theorem sync_proj (hd : Disjoint M₁.view M₂.view) {s s' : σ} (hr : rel (M₁.sync M₂) s s') :
    ∃ a' b', rel M₁.next (M₁.view.get s) a' ∧ M₁.view.get s' = a' ∧
      rel M₂.next (M₂.view.get s) b' ∧ M₂.view.get s' = b' := by
  obtain ⟨a', b', ha', hb', hs'⟩ := rel_sync.mp hr
  refine ⟨a', b', ha', ?_, hb', ?_⟩
  · rw [hs', hd.set_get, M₁.get_set]
  · rw [hs', sync_set_comm (M₁ := M₁) (M₂ := M₂) hd, hd.get_set, M₂.get_set]

/-- The lock-step composition as a module. Note that both components must be able
to move: `sync` has no step when one of them is stuck. -/
def syncModule (M₁ : ViewModule σ α) (M₂ : ViewModule σ β) : Module σ where
  init := fun s => M₁.init s ∧ M₂.init s
  next := M₁.sync M₂

theorem syncModule_safe {P : Nondet α} {Q : Nondet β} (hd : Disjoint M₁.view M₂.view)
    (hinit₁ : ∀ s, M₁.init s → P (M₁.view.get s))
    (hinit₂ : ∀ s, M₂.init s → Q (M₂.view.get s))
    (hP : Preserves M₁.next P) (hQ : Preserves M₂.next Q) :
    (M₁.syncModule M₂).Safe (fun s => P (M₁.view.get s) ∧ Q (M₂.view.get s)) := by
  apply Module.safe_of_preserves
  · intro s hs
    exact ⟨hinit₁ s hs.1, hinit₂ s hs.2⟩
  · exact sync_preserves hd hP hQ

end ViewModule

/-! ## Proving disjointness for structure views

Views for structure fields are definitionally pointwise, so their disjointness is
`cases` plus `rfl`. -/

/-- Prove a `Disjoint` goal for views written as structure updates. -/
macro "disjoint_auto" : tactic =>
  `(tactic| (refine ⟨?_, ?_, ?_⟩ <;>
    first
      | (intro s a b; try cases s; try cases a; try cases b; rfl)
      | (intro s a; try cases s; try cases a; rfl)))

end LeanAction