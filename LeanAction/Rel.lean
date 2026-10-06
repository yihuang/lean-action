/-
LeanAction.Rel
==============

A Mathlib-free relation toolkit.

`LeanAction` deliberately avoids a Mathlib dependency (see `DESIGN.md`), so this
file re-states the small amount of relation theory the library needs:

* `Rel α β` is just `α → β → Prop`;
* `Rel.Comp` — relational composition (the semantic core of sequential action);
* `Rel.TransGen` / `Rel.ReflTransGen` — transitive / reflexive-transitive closure
  (the semantic core of loops and reachability).

Both closures are declared with a `refl`/`tail` shape so that the standard
`induction h with | refl => … | tail hstep ih => …` idiom works, matching
`Mathlib.Logic.Relation`.
-/
import Std

universe u v w x

namespace LeanAction

/-- A binary relation. Definitionally equal to `α → β → Prop`. -/
abbrev Rel (α : Type u) (β : Type v) : Type (max u v) := α → β → Prop

namespace Rel

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
variable {α' : Type u} {β' : Type v}

/-- Relational composition: `r` followed by `s`. -/
def Comp (r : Rel α β) (s : Rel β γ) : Rel α γ := fun a c => ∃ b, r a b ∧ s b c

@[inherit_doc] infixr:80 " ∘ᵣ " => Comp

theorem comp_apply {r : Rel α β} {s : Rel β γ} {a : α} {c : γ} :
    (r ∘ᵣ s) a c ↔ ∃ b, r a b ∧ s b c := Iff.rfl

theorem comp_assoc {r : Rel α β} {s : Rel β γ} {t : Rel γ δ} :
    (r ∘ᵣ s) ∘ᵣ t = r ∘ᵣ (s ∘ᵣ t) := by
  funext a d
  exact propext
    ⟨fun ⟨c, ⟨b, h₁, h₂⟩, h₃⟩ => ⟨b, h₁, c, h₂, h₃⟩,
     fun ⟨b, h₁, c, h₂, h₃⟩ => ⟨c, ⟨b, h₁, h₂⟩, h₃⟩⟩

theorem comp_mono {r₁ r₂ : Rel α β} {s₁ s₂ : Rel β γ}
    (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ b c, s₁ b c → s₂ b c) :
    ∀ a c, (r₁ ∘ᵣ s₁) a c → (r₂ ∘ᵣ s₂) a c :=
  fun _ _ ⟨b, h₁, h₂⟩ => ⟨b, hr _ _ h₁, hs _ _ h₂⟩

/-- Inverse image (change of variables on both sides). -/
def Map (f : α' → α) (g : β' → β) (r : Rel α β) : Rel α' β' := fun a b => r (f a) (g b)

/-- Transitive closure. -/
inductive TransGen (r : Rel α α) : Rel α α where
  | single {a b : α} : r a b → TransGen r a b
  | tail {a b c : α} : TransGen r a b → r b c → TransGen r a c

/-- Reflexive-transitive closure ("zero or more steps"). -/
inductive ReflTransGen (r : Rel α α) : Rel α α where
  | refl (a : α) : ReflTransGen r a a
  | tail {a b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

attribute [refl] ReflTransGen.refl

theorem reflTransGen_single {r : Rel α α} {a b : α} (h : r a b) : ReflTransGen r a b :=
  ReflTransGen.tail (ReflTransGen.refl a) h

theorem reflTransGen_trans {r : Rel α α} {a b c : α}
    (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  revert hab
  induction hbc with
  | refl => intro hab; exact hab
  | tail _ hstep ih => intro hab; exact ReflTransGen.tail (ih hab) hstep

theorem reflTransGen_head {r : Rel α α} {a b c : α}
    (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  reflTransGen_trans (reflTransGen_single hab) hbc

theorem TransGen.trans {r : Rel α α} {a b c : α}
    (hab : TransGen r a b) (hbc : TransGen r b c) : TransGen r a c := by
  revert hab
  induction hbc with
  | single h => intro hab; exact TransGen.tail hab h
  | tail _ hstep ih => intro hab; exact TransGen.tail (ih hab) hstep

theorem TransGen.to_reflTransGen {r : Rel α α} {a b : α} (h : TransGen r a b) :
    ReflTransGen r a b := by
  induction h with
  | single h => exact reflTransGen_single h
  | tail _ hstep ih => exact ReflTransGen.tail ih hstep

theorem reflTransGen_of_transGen {r : Rel α α} {a b : α} (h : TransGen r a b) :
    ReflTransGen r a b := h.to_reflTransGen

theorem TransGen.single_to_reflTransGen {r : Rel α α} {a b : α} (h : r a b) :
    ReflTransGen r a b := reflTransGen_single h

theorem reflTransGen_mono {r s : Rel α α} (h : ∀ a b, r a b → s a b) {a b : α}
    (hr : ReflTransGen r a b) : ReflTransGen s a b := by
  induction hr with
  | refl => exact ReflTransGen.refl _
  | tail _ hstep ih => exact ReflTransGen.tail ih (h _ _ hstep)

theorem TransGen.mono {r s : Rel α α} (h : ∀ a b, r a b → s a b) {a b : α}
    (hr : TransGen r a b) : TransGen s a b := by
  induction hr with
  | single hstep => exact TransGen.single (h _ _ hstep)
  | tail _ hstep ih => exact TransGen.tail ih (h _ _ hstep)

/-- Decomposition of one `tail` step, handy for `rcases`-style automation. -/
theorem reflTransGen_tail_cases {r : Rel α α} {a c : α}
    (h : ReflTransGen r a c) : a = c ∨ ∃ b, ReflTransGen r a b ∧ r b c := by
  cases h with
  | refl => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-- Induction principle for `ReflTransGen` in "prefix" form: to prove `P` on every
reachable state it suffices to prove it at the start and to preserve it under steps. -/
theorem reflTransGen_induction {r : Rel α α} {P : α → Prop} {a : α}
    (hinit : P a) (hstep : ∀ b c, P b → r b c → P c) {b : α}
    (h : ReflTransGen r a b) : P b := by
  revert hinit
  induction h with
  | refl => intro hinit; exact hinit
  | tail _ hs ih => intro hinit; exact hstep _ _ (ih hinit) hs

end Rel
end LeanAction
