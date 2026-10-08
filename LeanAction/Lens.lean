/-
LeanAction.Lens
===============

Modularity for actions on nested `structure` states.

A `Lens σ α` is a field `α` of a state `σ` (get/set plus the three lens laws).
`focus l A` runs the action `A : Action α` on the sub-state selected by `l`,
leaving the rest of `σ` untouched. Composing lenses (`Lens.comp`) focuses on
nested fields, and product lenses (`Lens.fst`, `Lens.snd`) give the standard
"independent components" view used for interleaving/parallel composition.
-/
import Std
import LeanAction.Action

universe u

namespace LeanAction

/-- A lens on a state type `σ` selecting a component of type `α`.
The three laws say `set` and `get` are mutually inverse and `set` is idempotent,
i.e. `set` really only touches the selected component. -/
structure Lens (σ : Type u) (α : Type u) where
  /-- Read the selected component. -/
  get : σ → α
  /-- Write the selected component, leaving the rest alone. -/
  set : σ → α → σ
  get_set : ∀ s a, get (set s a) = a
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s a b, set (set s a) b = set s b

namespace Lens

variable {σ α β γ : Type u}

/-- The identity lens. -/
def id : Lens σ σ where
  get := fun s => s
  set := fun _ a => a
  get_set := by intro s a; rfl
  set_get := by intro s; rfl
  set_set := by intro s a b; rfl

/-- Lens composition: focus on the `β`-component inside the `α`-component. -/
def comp (l₁ : Lens σ α) (l₂ : Lens α β) : Lens σ β where
  get := fun s => l₂.get (l₁.get s)
  set := fun s b => l₁.set s (l₂.set (l₁.get s) b)
  get_set := by
    intro s b
    simp [l₁.get_set, l₂.get_set]
  set_get := by
    intro s
    simp [l₁.set_get, l₂.set_get]
  set_set := by
    intro s a b
    simp [l₁.get_set, l₁.set_set, l₂.set_set]

@[inherit_doc] infixr:80 " ∘ₗ " => comp

/-- First component of a product. -/
def fst : Lens (σ × α) σ where
  get := fun p => p.1
  set := fun p a => (a, p.2)
  get_set := by intro p a; rfl
  set_get := by intro p; cases p; rfl
  set_set := by intro p a b; rfl

/-- Second component of a product. -/
def snd : Lens (σ × α) α where
  get := fun p => p.2
  set := fun p a => (p.1, a)
  get_set := by intro p a; rfl
  set_get := by intro p; cases p; rfl
  set_set := by intro p a b; rfl

end Lens

/-! ## Focusing actions on sub-states -/

/-- Run `A : ActionM α β` on the component selected by `l`. -/
def focusM (l : Lens σ α) (A : ActionM α β) : ActionM σ β :=
  fun s z => ∃ p : β × α, A (l.get s) p ∧ z = (p.1, l.set s p.2)

/-- Run `A : Action α` on the component selected by `l`. -/
def focus (l : Lens σ α) (A : Action α) : Action σ := focusM l A

@[simp] theorem rel_focus {l : Lens σ α} {A : Action α} {s s' : σ} :
    rel (focus l A) s s' ↔ ∃ a', rel A (l.get s) a' ∧ s' = l.set s a' := by
  unfold rel focus focusM
  constructor
  · rintro ⟨⟨a, b⟩, ha, hz⟩
    cases a
    exact ⟨b, ha, congrArg Prod.snd hz⟩
  · rintro ⟨a', ha, hs'⟩
    exact ⟨(Done.mk, a'), ha, by rw [hs']⟩

/-- Lens form of `rel_focus`: the new value of the focused component is exactly
the success value of the inner action. -/
theorem rel_focus' {l : Lens σ α} {A : Action α} {s s' : σ} :
    rel (focus l A) s s' ↔ rel A (l.get s) (l.get s') ∧ s' = l.set s (l.get s') := by
  rw [rel_focus]
  constructor
  · rintro ⟨a', ha, hs'⟩
    exact ⟨by rw [hs']; simpa [l.get_set] using ha, by rw [hs']; simp [l.get_set]⟩
  · rintro ⟨ha, hs'⟩
    exact ⟨l.get s', ha, hs'⟩

/-- Action on the first component of a product state; the second component is
left untouched. (`Lens.fst` gives the same action up to definitional equality.) -/
def liftLeft (A : Action σ) : Action (σ × α) :=
  fun p z => ∃ s', rel A p.1 s' ∧ z = (Done.mk, (s', p.2))

/-- Action on the second component of a product state; the first component is
left untouched. -/
def liftRight (B : Action α) : Action (σ × α) :=
  fun p z => ∃ a', rel B p.2 a' ∧ z = (Done.mk, (p.1, a'))

@[simp] theorem rel_liftLeft {A : Action σ} {p q : σ × α} :
    rel (liftLeft A) p q ↔ rel A p.1 q.1 ∧ q.2 = p.2 := by
  unfold rel liftLeft
  constructor
  · rintro ⟨s', ha, hq⟩
    simp only [Prod.mk.injEq] at hq
    exact ⟨by rw [hq.2]; exact ha, by rw [hq.2]⟩
  · rintro ⟨ha, hq⟩
    exact ⟨q.1, ha, Prod.ext rfl (by cases q; simpa using hq)⟩

@[simp] theorem rel_liftRight {B : Action α} {p q : σ × α} :
    rel (liftRight B) p q ↔ rel B p.2 q.2 ∧ q.1 = p.1 := by
  unfold rel liftRight
  constructor
  · rintro ⟨a', ha, hq⟩
    simp only [Prod.mk.injEq] at hq
    exact ⟨by rw [hq.2]; exact ha, by rw [hq.2]⟩
  · rintro ⟨ha, hq⟩
    exact ⟨q.2, ha, Prod.ext rfl (by cases q; simpa using hq)⟩

/-! ## Proof-free focus points

Writing the three lens laws for every structure field is friction. A `View` is a
getter/setter pair without laws: it is enough to *define* a focused action, and
the law-carrying `Lens` is only needed for the nicest rewrite (`rel_focus'`) and
for reasoning about composition. `View` is therefore the recommended way to
attach actions to structure fields; `lens!`-style derivation is listed as future
work in `DESIGN.md`. -/

/-- A proof-free component selector: a getter and a setter for one field. -/
structure View (σ : Type u) (α : Type u) where
  get : σ → α
  set : σ → α → σ

namespace View

variable {σ α β : Type u}

/-- Forget the lens laws. -/
def ofLens (l : Lens σ α) : View σ α := ⟨l.get, l.set⟩


/-- Compose views (nested fields). The setter re-reads the outer field, which is
what makes `get ∘ set` behave like a nested update. -/
def comp (v₁ : View σ α) (v₂ : View α β) : View σ β where
  get := fun s => v₂.get (v₁.get s)
  set := fun s b => v₁.set s (v₂.set (v₁.get s) b)

/-- View of the first component of a product. -/
def fst : View (σ × α) σ := ⟨fun p => p.1, fun p a => (a, p.2)⟩

/-- View of the second component of a product. -/
def snd : View (σ × α) α := ⟨fun p => p.2, fun p a => (p.1, a)⟩

@[inherit_doc] infixr:80 " ∘ᵥ " => comp

end View

/-- Run `A` on the component selected by the view `v`. No lens laws are needed:
the resulting `rel` is literally the existential in the definition. -/
def focusView (v : View σ α) (A : Action α) : Action σ :=
  fun s z => ∃ a', rel A (v.get s) a' ∧ z = (Done.mk, v.set s a')

@[simp] theorem rel_focusView {v : View σ α} {A : Action α} {s s' : σ} :
    rel (focusView v A) s s' ↔ ∃ a', rel A (v.get s) a' ∧ s' = v.set s a' := by
  unfold rel focusView
  constructor
  · rintro ⟨a', ha, hz⟩
    cases hz
    exact ⟨a', ha, rfl⟩
  · rintro ⟨a', ha, hs'⟩
    exact ⟨a', ha, by rw [hs']⟩

theorem rel_viewOfLens {l : Lens σ α} {A : Action α} {s s' : σ} :
    rel (focusView (View.ofLens l) A) s s' ↔ rel (focus l A) s s' := by
  simp [rel_focus, View.ofLens]

/-! ### Enabledness of lifted/focused actions

Continuation of the `enabled_*` set from `LeanAction.Action`: focusing an
action on a sub-state preserves enabledness exactly, pointwise. -/

@[simp] theorem enabled_focusView {v : View σ α} {A : Action α} {s : σ} :
    Enabled (focusView v A) s ↔ Enabled A (v.get s) := by
  simp only [Enabled, rel_focusView]
  constructor
  · rintro ⟨s', a', h, -⟩
    exact ⟨a', h⟩
  · rintro ⟨a', h⟩
    exact ⟨v.set s a', a', h, rfl⟩

@[simp] theorem enabled_liftLeft {A : Action σ} {p : σ × α} :
    Enabled (liftLeft A) p ↔ Enabled A p.1 := by
  simp only [Enabled, rel_liftLeft]
  constructor
  · rintro ⟨q, h, -⟩
    exact ⟨q.1, h⟩
  · rintro ⟨s', h⟩
    exact ⟨(s', p.2), h, rfl⟩

@[simp] theorem enabled_liftRight {B : Action α} {p : σ × α} :
    Enabled (liftRight B) p ↔ Enabled B p.2 := by
  simp only [Enabled, rel_liftRight]
  constructor
  · rintro ⟨q, h, -⟩
    exact ⟨q.2, h⟩
  · rintro ⟨s', h⟩
    exact ⟨(p.1, s'), h, rfl⟩

/-! ## Function update (array-like fields)

A helper for `View`s whose getter is a function `α → β` (arrays). `upd` writes a
single index. Note that `upd.eq_def` is stated on the *fully applied* form
(`upd f i v j`), so it does not see the bare function value that appears inside
a structure update such as `{ s with arr := upd s.arr i v }`. `upd_fun` is the
function-level equation that `action_simp` rewrites with. -/

/-- Function update. -/
def upd [DecidableEq α] (f : α → β) (i : α) (v : β) : α → β :=
  fun j => if j = i then v else f j

/-- Function-level unfolding of `upd`: unlike `upd.eq_def`, this rewrites the
bare function value, which is what `simp`/`action_simp` sees inside a structure
update. -/
theorem upd_fun [DecidableEq α] (f : α → β) (i : α) (v : β) :
    upd f i v = fun j => if j = i then v else f j := rfl

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

end LeanAction
