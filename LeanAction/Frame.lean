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
import Lean
import LeanAction.Lens
import LeanAction.Proof
import LeanAction.Liveness
import LeanAction.Derive

universe u

namespace LeanAction

open Nondet Lean Elab Tactic

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

/-! ## Composing disjointness

`Disjoint` is compositional: nested views reduce to base cases instead of
one big pointwise proof. These three theorems use only the lens laws and
`Disjoint` hypotheses. -/

variable {γ : Type u}

/-- Two views into the *same* component commute when the inner views do.
Assumptions: the three lens laws for the outer lens and `Disjoint` for the
inner views. -/
theorem Disjoint.comp_of_disjoint (l : Lens σ α) {w₁ : View α β} {w₂ : View α γ}
    (h : Disjoint w₁ w₂) :
    Disjoint (View.ofLens l ∘ᵥ w₁) (View.ofLens l ∘ᵥ w₂) where
  get_set s a := by
    show w₂.get (l.get (l.set s (w₁.set (l.get s) a))) = w₂.get (l.get s)
    rw [l.get_set]
    exact h.get_set _ _
  set_get s b := by
    show w₁.get (l.get (l.set s (w₂.set (l.get s) b))) = w₁.get (l.get s)
    rw [l.get_set]
    exact h.set_get _ _
  set_set s a b := by
    show l.set (l.set s (w₂.set (l.get s) b)) (w₁.set (l.get (l.set s (w₂.set (l.get s) b))) a) =
      l.set (l.set s (w₁.set (l.get s) a)) (w₂.set (l.get (l.set s (w₁.set (l.get s) a))) b)
    rw [l.get_set, l.get_set, l.set_set, l.set_set]
    exact congrArg (l.set s) (h.set_set _ _ _)

/-- A view into a component of a disjoint pair stays disjoint from the other
component. Only uses `Disjoint` hypotheses — no lens laws at all. -/
theorem Disjoint.comp_left {v₁ : View σ α} {v₂ : View σ β} (h : Disjoint v₁ v₂)
    (w : View α γ) :
    Disjoint (v₁ ∘ᵥ w) v₂ where
  get_set s a := by
    show v₂.get (v₁.set s (w.set (v₁.get s) a)) = v₂.get s
    exact h.get_set _ _
  set_get s b := by
    show w.get (v₁.get (v₂.set s b)) = w.get (v₁.get s)
    rw [h.set_get]
  set_set s a b := by
    show v₁.set (v₂.set s b) (w.set (v₁.get (v₂.set s b)) a) =
      v₂.set (v₁.set s (w.set (v₁.get s) a)) b
    rw [h.set_get, h.set_set]

/-- The symmetric version. -/
theorem Disjoint.comp_right {v₁ : View σ α} {v₂ : View σ β} (h : Disjoint v₁ v₂)
    (w : View β γ) :
    Disjoint v₁ (v₂ ∘ᵥ w) :=
  (h.symm.comp_left w).symm

/-! ## Function-update (array-like) footprints

The syntactic boundary of the pointwise (`cases; rfl`) disjointness fragment:
`upd` with a *variable* index does not reduce, so array-like views need
conditional lemmas with an `i ≠ j` side condition. -/

/-- Function update. -/
def upd [DecidableEq α] (f : α → β) (i : α) (v : β) : α → β :=
  fun j => if j = i then v else f j

theorem upd_same [DecidableEq α] (f : α → β) (i : α) (v : β) : upd f i v i = v :=
  if_pos rfl

theorem upd_noteq [DecidableEq α] {i j : α} (h : j ≠ i) (f : α → β) (v : β) :
    upd f i v j = f j :=
  if_neg h

/-- Commutation of two updates at distinct indices: the lemma that makes
array-like footprints work. -/
theorem upd_comm [DecidableEq α] {i j : α} (h : i ≠ j) (f : α → β) (a b : β) :
    upd (upd f i a) j b = upd (upd f j b) i a := by
  funext k
  show (if k = j then b else (if k = i then a else f k)) =
    (if k = i then a else (if k = j then b else f k))
  by_cases hki : k = i
  · subst hki
    rw [if_neg h, if_pos rfl, if_pos rfl]
  · by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl, if_neg (Ne.symm h), if_pos rfl]
    · rw [if_neg hkj, if_neg hki, if_neg hki, if_neg hkj]

/-! ## Conditional disjointness: `DisjointUnder`

The conditional frame ("if `i ≠ j`, writing `arr[i]` does not disturb
`arr[j]`") is *one* abstraction that is simultaneously:

* the footprint layer's conditional frame (`DisjointUnder` below);
* the RG layer's rely special case (`get_eq_of_write`, `rely`);
* the temporal layer's static shadow of a region (`get_const_of_steps`,
  `get_const_of_behavior`).

Flat-state frameworks neither have nor need this (footprint = variable
name); the `View` semantics expresses it directly. The asymmetric `set_set`
law — the condition guards only the `v₂`-intermediate — orients `v₂` as the
"environment" side, which is exactly what makes composition (below) free of
preservation side conditions. -/

/-- Conditional disjointness: the three commutation laws are required to
hold only at states satisfying `P`. `Disjoint` is the special case where
`P` is trivially true. -/
structure DisjointUnder (P : Nondet σ) (v₁ : View σ α) (v₂ : View σ β) : Prop where
  get_set : ∀ s a, P s → v₂.get (v₁.set s a) = v₂.get s
  set_get : ∀ s b, P s → v₁.get (v₂.set s b) = v₁.get s
  set_set : ∀ s a b, P s → P (v₂.set s b) →
    v₁.set (v₂.set s b) a = v₂.set (v₁.set s a) b

/-- Plain disjointness implies conditional disjointness at any condition. -/
theorem Disjoint.toUnder (h : Disjoint v₁ v₂) (P : Nondet σ) :
    DisjointUnder P v₁ v₂ where
  get_set s a _ := h.get_set s a
  set_get s b _ := h.set_get s b
  set_set s a b _ _ := h.set_set s a b

/-- At the trivial condition this is exactly `Disjoint`: the conditional
notion is a *conservative extension*, not a competing one. -/
theorem disjointUnder_top (v₁ : View σ α) (v₂ : View σ β) :
    DisjointUnder (fun _ : σ => True) v₁ v₂ ↔ Disjoint v₁ v₂ :=
  ⟨fun h => ⟨fun s a => h.get_set s a True.intro, fun s b => h.set_get s b True.intro,
      fun s a b => h.set_set s a b True.intro True.intro⟩,
   fun h => h.toUnder _⟩

/-- Monotonicity: if commutation holds at every `Q`-state and `P s` implies
`Q s`, then it holds at every `P`-state. -/
theorem DisjointUnder.mono {P Q : Nondet σ} (hPQ : ∀ s, P s → Q s)
    (h : DisjointUnder Q v₁ v₂) : DisjointUnder P v₁ v₂ where
  get_set s a hp := h.get_set s a (hPQ s hp)
  set_get s b hp := h.set_get s b (hPQ s hp)
  set_set s a b hp hp' := h.set_set s a b (hPQ s hp) (hPQ _ hp')

/-- The rely reading, pointwise: an environment step that keeps `P` and
writes only within `v₂`'s footprint (i.e. the step is fully determined by
its `v₂`-view) leaves `v₁`'s view unchanged. -/
theorem DisjointUnder.get_eq_of_write {P : Nondet σ} {v₁ : View σ α} {v₂ : View σ β}
    (h : DisjointUnder P v₁ v₂) {s s' : σ} (hp : P s)
    (hwrite : s' = v₂.set s (v₂.get s')) : v₁.get s' = v₁.get s :=
  calc v₁.get s' = v₁.get (v₂.set s (v₂.get s')) := congrArg v₁.get hwrite
    _ = v₁.get s := h.set_get s (v₂.get s') hp

/-- The frame reading for a *focused action*: an action taken through `v₁` leaves
`v₂`'s view unchanged while `P` holds. This is the conditional analogue of
`Disjoint.get_of_rel`, and the single-step ingredient of
`parallel_preserves_under` below. -/
theorem DisjointUnder.get_of_rel {P : Nondet σ} {v₁ : View σ α} {v₂ : View σ β}
    (h : DisjointUnder P v₁ v₂) {A : Action α} {s s' : σ}
    (hp : P s) (hr : rel (focusView v₁ A) s s') : v₂.get s' = v₂.get s := by
  obtain ⟨a', -, hs'⟩ := rel_focusView.mp hr
  rw [hs']
  exact h.get_set s a' hp

/-- Packaged as a rely relation: if every `R`-step preserves `P` and stays
inside `v₂`'s footprint, then `R` is a valid rely for any component reading
`v₁`. -/
theorem DisjointUnder.rely {P : Nondet σ} {v₁ : View σ α} {v₂ : View σ β}
    (h : DisjointUnder P v₁ v₂) {R : Rel σ σ}
    (hR : ∀ s s', R s s' → P s → P s' ∧ s' = v₂.set s (v₂.get s'))
    {s s' : σ} (hr : R s s') (hp : P s) : v₁.get s' = v₁.get s := by
  obtain ⟨_, hwrite⟩ := hR s s' hr hp
  exact h.get_eq_of_write hp hwrite

/-- Along any behavior whose states all satisfy `P` and whose every step
writes only within `v₂`'s footprint, `v₁`'s view is constant. -/
theorem DisjointUnder.get_const_of_steps {P : Nondet σ} {v₁ : View σ α} {v₂ : View σ β}
    (h : DisjointUnder P v₁ v₂) {b : Behavior σ}
    (hP : ∀ n, P (b n)) (hstep : ∀ n, ∃ v, b (n + 1) = v₂.set (b n) v) :
    ∀ n, v₁.get (b n) = v₁.get (b 0) := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
      obtain ⟨v, hv⟩ := hstep m
      calc v₁.get (b (m + 1)) = v₁.get (v₂.set (b m) v) := congrArg v₁.get hv
        _ = v₁.get (b m) := h.set_get (b m) v (hP m)
        _ = v₁.get (b 0) := ih

/-- Packaged over a module: if every `M`-step preserves `P` and writes only
within `v₂`'s footprint, then along any behavior of `M` the `v₁`-view is
frozen. -/
theorem DisjointUnder.get_const_of_behavior {P : Nondet σ} {v₁ : View σ α} {v₂ : View σ β}
    (h : DisjointUnder P v₁ v₂) {M : Module σ} {b : Behavior σ}
    (hbeh : IsBehavior M b) (hP : ∀ n, P (b n))
    (hnext : ∀ s s', rel M.next s s' → P s → P s' ∧ s' = v₂.set s (v₂.get s')) :
    ∀ n, v₁.get (b n) = v₁.get (b 0) := by
  apply h.get_const_of_steps hP
  intro n
  obtain ⟨_, hwrite⟩ := hnext (b n) (b (n + 1)) (hbeh n) (hP n)
  exact ⟨_, hwrite⟩

/-- Through a lens: the condition pulls back along `l.get`. -/
theorem DisjointUnder.comp_of_disjoint (l : Lens σ α) {Q : Nondet α}
    {w₁ : View α β} {w₂ : View α γ} (h : DisjointUnder Q w₁ w₂) :
    DisjointUnder (fun s => Q (l.get s)) (View.ofLens l ∘ᵥ w₁) (View.ofLens l ∘ᵥ w₂) where
  get_set s a hp := by
    show w₂.get (l.get (l.set s (w₁.set (l.get s) a))) = w₂.get (l.get s)
    rw [l.get_set]
    exact h.get_set _ _ hp
  set_get s b hp := by
    show w₁.get (l.get (l.set s (w₂.set (l.get s) b))) = w₁.get (l.get s)
    rw [l.get_set]
    exact h.set_get _ _ hp
  set_set s a b hp hp' := by
    show l.set (l.set s (w₂.set (l.get s) b))
        (w₁.set (l.get (l.set s (w₂.set (l.get s) b))) a) =
      l.set (l.set s (w₁.set (l.get s) a))
        (w₂.set (l.get (l.set s (w₁.set (l.get s) a))) b)
    rw [l.get_set, l.get_set, l.set_set, l.set_set]
    change Q (l.get (l.set s (w₂.set (l.get s) b))) at hp'
    rw [l.get_set] at hp'
    exact congrArg (l.set s) (h.set_set _ _ _ hp hp')

/-- Nested view against a sibling, under `P`. The asymmetric `set_set`
condition lands exactly on the nested view's intermediate state, so no
preservation side condition is needed. -/
theorem DisjointUnder.comp_left {P : Nondet σ} {v₁ : View σ α} {v₂ : View σ β}
    (h : DisjointUnder P v₁ v₂) (w : View α γ) :
    DisjointUnder P (v₁ ∘ᵥ w) v₂ where
  get_set s a hp := h.get_set s (w.set (v₁.get s) a) hp
  set_get s b hp := by
    show w.get (v₁.get (v₂.set s b)) = w.get (v₁.get s)
    rw [h.set_get s b hp]
  set_set s a b hp hp' := by
    show v₁.set (v₂.set s b) (w.set (v₁.get (v₂.set s b)) a) =
      v₂.set (v₁.set s (w.set (v₁.get s) a)) b
    rw [h.set_get s b hp, h.set_set s _ _ hp hp']

/-- Symmetric version: nesting a view on the *environment* side asks even
less, since the environment's intermediate condition is the one `set_set`
already guards. -/
theorem DisjointUnder.comp_right {P : Nondet σ} {v₁ : View σ α} {v₂ : View σ β}
    (h : DisjointUnder P v₁ v₂) (w : View β γ) :
    DisjointUnder P v₁ (v₂ ∘ᵥ w) where
  get_set s a hp := by
    show w.get (v₂.get (v₁.set s a)) = w.get (v₂.get s)
    rw [h.get_set s a hp]
  set_get s b hp := h.set_get s (w.set (v₂.get s) b) hp
  set_set s a b hp hp' := by
    show v₁.set (v₂.set s (w.set (v₂.get s) b)) a =
      v₂.set (v₁.set s a) (w.set (v₂.get (v₁.set s a)) b)
    rw [h.get_set s a hp]
    exact h.set_set s a (w.set (v₂.get s) b) hp hp'

/-- **Conditional parallel composition.** If the two footprints commute only
under a condition `P`, and both components preserve `P`, then the interleaving
preserves `P` together with the two component invariants. This is
`ViewModule.parallel_preserves` with `Disjoint` weakened to `DisjointUnder` — the
form the aliasing-freedom case needs to close its safety theorem.

The asymmetry of `DisjointUnder.set_set` (only the `v₂`-intermediate state is
guarded) is what keeps this free of preservation side conditions on the *other*
component's intermediate state. -/
theorem parallel_preserves_under {P : Nondet σ} {v₁ : View σ α} {v₂ : View σ β}
    (hd : DisjointUnder P v₁ v₂) (A₁ : Action α) (A₂ : Action β)
    (hget₁ : ∀ s a, v₁.get (v₁.set s a) = a) (hget₂ : ∀ s a, v₂.get (v₂.set s a) = a)
    (hP₁ : Preserves (focusView v₁ A₁) P) (hP₂ : Preserves (focusView v₂ A₂) P)
    {P₁ : Nondet α} {P₂ : Nondet β}
    (h₁ : Preserves A₁ P₁) (h₂ : Preserves A₂ P₂) :
    Preserves (focusView v₁ A₁ <|> focusView v₂ A₂)
      (fun s => P s ∧ P₁ (v₁.get s) ∧ P₂ (v₂.get s)) := by
  intro s hs s' hr
  rw [rel_orElse] at hr
  rcases hr with hr | hr
  · obtain ⟨a', ha', hs'⟩ := rel_focusView.mp hr
    refine ⟨hP₁ s hs.1 s' hr, ?_, ?_⟩
    · rw [hs', hget₁ s a']
      exact h₁ (v₁.get s) hs.2.1 a' ha'
    · rw [hs', hd.get_set s a' hs.1]
      exact hs.2.2
  · obtain ⟨b', hb', hs'⟩ := rel_focusView.mp hr
    refine ⟨hP₂ s hs.1 s' hr, ?_, ?_⟩
    · rw [hs', hd.set_get s b' hs.1]
      exact hs.2.1
    · rw [hs', hget₂ s b']
      exact h₂ (v₂.get s) hs.2.2 b' hb'

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

/-- The derived rely for the safety fragment: environment steps preserve the
invariant. Packaging as a relation — not a new concept. -/
def derivedRely (I : Nondet σ) : Rel σ σ := fun s s' => I s → I s'

/-- Against the *derived* relies, `Compatible` is definitional: the only content
is the two guarantee lemmas, since `derivedRely I s s'` unfolds to `I s → I s'`.
This is the packaging `preserves_of_guarantees` is built on. -/
theorem compatible_of_guarantees {I : Nondet σ} {A₁ A₂ : Action σ}
    (g₁ : ∀ s s', I s → rel A₁ s s' → I s')
    (g₂ : ∀ s s', I s → rel A₂ s s' → I s') :
    Compatible I A₁ A₂ (derivedRely I) (derivedRely I) where
  left s s' hi h := fun _ => g₁ s s' hi h
  right s s' hi h := fun _ => g₂ s s' hi h

/-- **Rely as output.** Given each component's guarantee lemma (stated in its
own vocabulary, locally checkable), `Compatible` with the derived relies is
definitional and the composition is immediate: no explicit `Rel` parameter
appears at the call site. The user chooses exactly what they already choose —
`I` and the guarantees; trial-and-error over `R₁ R₂` is eliminated, not
automated. The explicit `Rel` parameter remains available for the residual
tier: value-constraint interfaces (e.g. `s'.v ≤ s.v`) that are not of the
shape `I s → I s'` for any single-predicate `I`. -/
theorem preserves_of_guarantees {σ : Type u} {I : Nondet σ} {A₁ A₂ : Action σ}
    (g₁ : ∀ s s', I s → rel A₁ s s' → I s')
    (g₂ : ∀ s s', I s → rel A₂ s s' → I s') :
    Preserves (A₁ <|> A₂) I :=
  Preserves.orElse_of_compatible
    (compatible_of_guarantees g₁ g₂)
    (fun _ _ hi hr => hr hi) (fun _ _ hi hr => hr hi)

/-! In plain terms this is just `Preserves.orElse` (each component preserves `I`)
composed with the `derivedRely`/`Compatible` packaging: the two guarantee lemmas
are the whole proof. The packaging is what makes the rely *disappear from the
call site* rather than being guessed — the point of the rule. -/

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

Views for structure fields are definitionally pointwise, so their disjointness
is `cases` plus `rfl`. But `disjoint_auto` has **two channels**:

1. **Certificate lookup**: `deriving ViewFields/LensFields` (and `view_defs` /
   `lens_defs`) emit one `T.disjoint_f_g` theorem per pair of distinct fields at
   generation time; this channel is a pure lookup combined with `Disjoint.symm`.
   It covers the flat-structure fragment — everything a flat-state framework
   (Veil/IVy) can cover — fully automatically, including `Nat`-valued fields
   where the old search used to get stuck. Generated certificates are found by
   the naming convention; *hand-written* ones can be registered explicitly with
   the `@[field_disjoint]` attribute, and the tactic consults that registry
   too.
2. **Semantic fallback**: `cases; rfl`, first *without* casing the values
   (casing a `Nat` value splits it into `zero`/`succ` and the `succ` branch
   does not close), then with casing (needed for pair-valued views).

When neither channel produces a certificate the tactic emits a
`trace[LeanAction.disjoint_auto]` line before falling back, so the silent
degradation from "certificate" to "search" is observable.

Neither channel sees function-update (`upd`) footprints: those are
*conditional* and need `upd_noteq`/`upd_comm` or `DisjointUnder`, by design. -/

initialize registerTraceClass `LeanAction.disjoint_auto

/-- The two head constants of a `Disjoint v₁ v₂` proposition, after stripping
`forall` binders. This keys the certificate registry. -/
private def certHeadPair? : Expr → Option (Name × Name)
  | .forallE _ _ body _ => certHeadPair? body
  | e =>
    if e.isAppOfArity ``Disjoint 5 then
      match e.appFn!.appArg!.getAppFn, e.appArg!.getAppFn with
      | .const n₁ _, .const n₂ _ => some (n₁, n₂)
      | _, _ => none
    else none

/-- Registry of `Disjoint` certificates: `(v₁, v₂) ↦ theorem`, filled by the
`@[field_disjoint]` attribute. Persisted across modules. -/
initialize fieldDisjointExt :
    SimplePersistentEnvExtension (Name × Name × Name) (NameMap (NameMap Name)) ←
  registerSimplePersistentEnvExtension {
    name := `LeanAction.fieldDisjoint
    addEntryFn := fun s (n₁, n₂, thm) =>
      s.insert n₁ (((s.find? n₁).getD {}).insert n₂ thm)
    addImportedFn := mkStateFromImportedEntries
      (fun s (n₁, n₂, thm) => s.insert n₁ (((s.find? n₁).getD {}).insert n₂ thm)) {}
  }

/-- Register a theorem as a `Disjoint` certificate for `disjoint_auto`, instead
of relying on the `T.disjoint_f_g` naming convention. -/
initialize registerBuiltinAttribute {
  name := `field_disjoint
  descr := "Register a `Disjoint v₁ v₂` theorem for `disjoint_auto`."
  add := fun decl _ _ => do
    let some ci := (← getEnv).find? decl
      | throwError "field_disjoint: unknown declaration `{decl}`"
    match certHeadPair? ci.type with
    | some (n₁, n₂) =>
        modifyEnv fun env => fieldDisjointExt.addEntry env (n₁, n₂, decl)
    | none =>
        throwError "field_disjoint: `{decl}` does not prove `Disjoint v₁ v₂`"
}

/-- The certificate theorem name for two *sibling field views* `T.fView`,
`T.gView`: `T.disjoint_f_g`. Returns `none` unless both views are head
constants under the same structure prefix ending in `View`. -/
private def fieldDisjointCert? (n₁ n₂ : Name) : Option Name := do
  let .str t f₁ := n₁ | none
  let .str t' g₁ := n₂ | none
  let some f := (f₁.dropSuffix? "View") | none
  let some g := (g₁.dropSuffix? "View") | none
  if t == t' then some (t.str s!"disjoint_{f}_{g}") else none

/-- Prove a `Disjoint` goal: certificate lookup first (per-field-pair theorems
generated by the view/lens derivers, found *by naming convention*), then the
`cases; rfl` fallback. -/
elab "disjoint_auto" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  let env ← getEnv
  if ty.isAppOfArity ``Disjoint 5 then
    let v₁ := ty.appFn!.appArg!
    let v₂ := ty.appArg!
    let heads := (v₁.getAppFn, v₂.getAppFn)
    if let (.const n₁ _, .const n₂ _) := heads then
      let named := [fieldDisjointCert? n₁ n₂, fieldDisjointCert? n₂ n₁].reduceOption
      let registered : List Name :=
        let st := fieldDisjointExt.getState env
        ((st.find? n₁).bind (·.find? n₂)).toList ++
          ((st.find? n₂).bind (·.find? n₁)).toList
      let certs := named ++ registered
      if certs.isEmpty then
        trace[LeanAction.disjoint_auto]
          "no certificate for {n₁} / {n₂}; using the semantic channel"
      for cert in certs do
        if env.contains cert then
          for e in [mkConst cert, mkApp (mkConst ``Disjoint.symm) (mkConst cert)] do
            try
              let gs ← g.apply e
              if gs.isEmpty then
                replaceMainGoal []
                return
            catch _ => pure ()
  -- semantic fallback: `cases; rfl`, first without casing the values
  evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩ <;>
    first
      | (intro s a b; try cases s; rfl)
      | (intro s a; try cases s; rfl)
      | (intro s a b; try cases s; try cases a; try cases b; rfl)
      | (intro s a; try cases s; try cases a; rfl)))

end LeanAction