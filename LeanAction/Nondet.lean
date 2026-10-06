/-
LeanAction.Nondet
=================

`Nondet α := α → Prop` is a Prop-valued nondeterminism monad: the "set of
possible results" of a nondeterministic computation.

It is the one place where `LeanAction` replaces a Mathlib notion
(`Set α := α → Prop`) by a locally defined one, so that the library builds with
no external dependencies. Because the definition is *definitionally* `α → Prop`,
Mathlib's `Set` API interoperates without any conversion: `Nondet α` is the same
type as `Set α`, so lemmas about `∈`, `⊆`, `⋃` can be used directly once Mathlib
is imported (see `DESIGN.md` §"与 Mathlib 的关系").

Instances provided:

* `Monad Nondet`  — `pure a = {a}`, `s >>= f = ⋃ a ∈ s, f a` (angelic nondeterminism);
* `Alternative Nondet` — `failure = ∅`, `s <|> t = s ∪ t`;
* `Membership α (Nondet α)` — so `a ∈ s` reads like set membership.

Composing these with `StateT` (see `LeanAction.Action`) yields the action DSL
with `do`-notation, `get`/`set`/`modify` and `<|>` for free.
-/
import Std
import LeanAction.Rel

universe u

namespace LeanAction

/-- Prop-valued nondeterminism monad. Definitionally `α → Prop`. -/
abbrev Nondet (α : Type u) : Type u := α → Prop

namespace Nondet

variable {α β γ : Type u}

instance : Membership α (Nondet α) := ⟨fun s a => s a⟩

/-- The empty nondeterministic result (deadlock / failure). -/
def empty : Nondet α := fun _ => False

/-- The singleton result. -/
def singleton (a : α) : Nondet α := fun b => b = a

/-- Angelic choice. -/
def union (s t : Nondet α) : Nondet α := fun a => s a ∨ t a

/-- Conjunction of results. -/
def inter (s t : Nondet α) : Nondet α := fun a => s a ∧ t a

/-- Indexed union, the `bind` of the monad. -/
def biUnion (s : Nondet α) (f : α → Nondet β) : Nondet β := fun b => ∃ a, s a ∧ f a b

/-- Image of a nondeterministic result. -/
def image (f : α → β) (s : Nondet α) : Nondet β := fun b => ∃ a, s a ∧ f a = b

/-- Preimage. -/
def preimage (f : α → β) (t : Nondet β) : Nondet α := fun a => t (f a)

/-- `s ⊆ t`. -/
def Subset (s t : Nondet α) : Prop := ∀ a, s a → t a

@[inherit_doc] infix:50 " ⊆ₙ " => Subset

/-- Extensional equality of nondeterministic results. -/
def Equiv (s t : Nondet α) : Prop := ∀ a, s a ↔ t a

@[inherit_doc] infix:50 " ≡ₙ " => Equiv

instance instMonad : Monad Nondet where
  pure := singleton
  bind := biUnion
  map := image

instance instAlternative : Alternative Nondet where
  failure := empty
  orElse := fun s t => union s (t ())

/-! ## `simp` normal forms -/

@[simp] theorem mem_singleton {a b : α} : b ∈ (singleton a : Nondet α) ↔ b = a := Iff.rfl

@[simp] theorem mem_empty {a : α} : ¬ (a ∈ (empty : Nondet α)) := id

@[simp] theorem mem_union {a : α} {s t : Nondet α} : a ∈ (union s t) ↔ a ∈ s ∨ a ∈ t := Iff.rfl

@[simp] theorem mem_inter {a : α} {s t : Nondet α} : a ∈ (inter s t) ↔ a ∈ s ∧ a ∈ t := Iff.rfl

@[simp] theorem mem_biUnion {b : β} {s : Nondet α} {f : α → Nondet β} :
    b ∈ biUnion s f ↔ ∃ a, a ∈ s ∧ b ∈ f a := Iff.rfl

@[simp] theorem mem_image {b : β} {f : α → β} {s : Nondet α} :
    b ∈ image f s ↔ ∃ a, a ∈ s ∧ f a = b := Iff.rfl

@[simp] theorem mem_preimage {a : α} {f : α → β} {t : Nondet β} :
    a ∈ preimage f t ↔ f a ∈ t := Iff.rfl

@[simp] theorem mem_pure {a b : α} : b ∈ (pure a : Nondet α) ↔ b = a := Iff.rfl

@[simp] theorem mem_bind {b : β} {s : Nondet α} {f : α → Nondet β} :
    b ∈ (s >>= f) ↔ ∃ a, a ∈ s ∧ b ∈ f a := Iff.rfl

@[simp] theorem mem_failure {a : α} : ¬ (a ∈ (failure : Nondet α)) := id

@[simp] theorem mem_orElse {a : α} {s t : Nondet α} : a ∈ (s <|> t) ↔ a ∈ s ∨ a ∈ t := Iff.rfl

theorem mem_map {b : β} {f : α → β} {s : Nondet α} :
    b ∈ (f <$> s) ↔ ∃ a, a ∈ s ∧ f a = b := Iff.rfl

/-! ## Monad laws (propositional) -/

theorem pure_bind (a : α) (f : α → Nondet β) : ((pure a : Nondet α) >>= f) ≡ₙ f a := by
  intro b
  exact ⟨fun ⟨a', ha', hb⟩ => ha' ▸ hb, fun hb => ⟨a, rfl, hb⟩⟩

theorem bind_pure (s : Nondet α) : (s >>= (pure : α → Nondet α)) ≡ₙ s := by
  intro b
  exact ⟨fun ⟨a, ha, hb⟩ => hb ▸ ha, fun hb => ⟨b, hb, rfl⟩⟩

theorem bind_assoc (s : Nondet α) (f : α → Nondet β) (g : β → Nondet γ) :
    ((s >>= f) >>= g) ≡ₙ (s >>= fun a => f a >>= g) := by
  intro c
  constructor
  · rintro ⟨b, ⟨a, ha, hb⟩, hc⟩
    exact ⟨a, ha, b, hb, hc⟩
  · rintro ⟨a, ha, b, hb, hc⟩
    exact ⟨b, ⟨a, ha, hb⟩, hc⟩

theorem map_eq_bind (f : α → β) (s : Nondet α) :
    (f <$> s) ≡ₙ (s >>= fun a => pure (f a)) := by
  intro b
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩⟩

/-! ## Lattice-style laws -/

theorem union_assoc (s t u : Nondet α) : union (union s t) u ≡ₙ union s (union t u) := by
  intro a; exact ⟨fun h => h.elim (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr h)),
                    fun h => h.elim (fun h => Or.inl (Or.inl h)) (fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr)⟩

/-- Every `Nondet` is extensional: pointwise `↔` gives equality. -/
theorem ext {s t : Nondet α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

theorem subset_refl (s : Nondet α) : s ⊆ₙ s := fun _ h => h

theorem subset_trans {r s t : Nondet α} (hrs : r ⊆ₙ s) (hst : s ⊆ₙ t) : r ⊆ₙ t :=
  fun a ha => hst a (hrs a ha)

theorem subset_antisymm {s t : Nondet α} (hst : s ⊆ₙ t) (hts : t ⊆ₙ s) : s = t :=
  ext fun a => ⟨hst a, hts a⟩

theorem empty_subset (s : Nondet α) : empty ⊆ₙ s := fun _ h => h.elim

theorem subset_union_left (s t : Nondet α) : s ⊆ₙ union s t := fun _ h => Or.inl h

theorem subset_union_right (s t : Nondet α) : t ⊆ₙ union s t := fun _ h => Or.inr h

theorem union_subset {s t u : Nondet α} (hs : s ⊆ₙ u) (ht : t ⊆ₙ u) : union s t ⊆ₙ u :=
  fun _ h => h.elim (hs _) (ht _)

theorem bind_mono {s₁ s₂ : Nondet α} {f₁ f₂ : α → Nondet β} (hs : s₁ ⊆ₙ s₂)
    (hf : ∀ a, f₁ a ⊆ₙ f₂ a) : (s₁ >>= f₁) ⊆ₙ (s₂ >>= f₂) :=
  fun b hb => hb.elim fun a ha => ⟨a, hs a ha.1, hf a b ha.2⟩

theorem union_bind (s t : Nondet α) (f : α → Nondet β) :
    ((s <|> t) >>= f) ≡ₙ ((s >>= f) <|> (t >>= f)) := by
  intro b
  constructor
  · rintro ⟨a, ha | ha, hb⟩
    · exact Or.inl ⟨a, ha, hb⟩
    · exact Or.inr ⟨a, ha, hb⟩
  · rintro (⟨a, ha, hb⟩ | ⟨a, ha, hb⟩)
    · exact ⟨a, Or.inl ha, hb⟩
    · exact ⟨a, Or.inr ha, hb⟩

theorem bind_union (s : Nondet α) (f g : α → Nondet β) :
    (s >>= fun a => f a <|> g a) ≡ₙ ((s >>= f) <|> (s >>= g)) := by
  intro b
  constructor
  · rintro ⟨a, ha, hf | hg⟩
    · exact Or.inl ⟨a, ha, hf⟩
    · exact Or.inr ⟨a, ha, hg⟩
  · rintro (⟨a, ha, hf⟩ | ⟨a, ha, hg⟩)
    · exact ⟨a, ha, Or.inl hf⟩
    · exact ⟨a, ha, Or.inr hg⟩

end Nondet
end LeanAction
