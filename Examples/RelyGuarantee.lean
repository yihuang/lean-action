/-
Examples.RelyGuarantee
======================

Rely/guarantee composition for components whose footprints **overlap** — the case
`Disjoint` cannot express, and which therefore `ViewModule.parallel` cannot
compose either (both components here write the same cell).

The point of the rely/guarantee rule is what the two obligations *mention*: each
component's obligation is stated against the other's **interface** (`R₁`/`R₂`),
never against the other component's code. Component 2 could be re-implemented by
anything satisfying `R₁` without touching component 1's proof.

For *state* invariants this buys modularity, not shorter proofs (with concrete
actions and a state invariant, a guard-free step that breaks the invariant cannot
be rescued by a rely — the rely constrains the environment, not the current
state). The refactor's "rely as output" observation makes that precise: the
safety fragment needs no rely at all — `preserves_of_guarantees` composes the two
guarantee lemmas directly, and `Compatible` with the `derivedRely I` is
*definitional*. Where the explicit `Rel` genuinely changes the shape of a proof is
a *prefix* property ("this region holds until the goal is reached"), which is what
`relyGuarantee_until` is for and what `Examples/MutexLiveness.region_until_goal`
now uses.
-/
import LeanAction

open LeanAction

namespace Examples.RelyGuarantee

/-- A shared cell. -/
structure Cell where
  v : Nat

/-- Component 1: an unconditional decrement. -/
def dec : Action Cell := update fun s => { s with v := s.v - 1 }

/-- Component 2: an increment, guarded so that it never exceeds the bound. -/
def bump : Action Cell := guard (fun s => s.v < 3) ;; update fun s => { s with v := s.v + 1 }

/-- The interleaving of the two components. -/
def next : Action Cell := dec <|> bump

/-- The invariant: the cell stays below the bound. -/
def I : Nondet Cell := fun s => s.v ≤ 3

/-- Component 1's rely — what it may assume about component 2. -/
def R₁ : Rel Cell Cell := fun _ s' => s'.v ≤ 3

/-- Component 2's rely — what it may assume about component 1: the environment
never increases the cell, so the bound is not endangered by it. -/
def R₂ : Rel Cell Cell := fun s s' => s'.v ≤ s.v

/-- Each component's steps are permitted by the *other's* rely. Both directions are
stated against an interface; neither mentions the other's code. -/
theorem compatible : Compatible I dec bump R₁ R₂ where
  left := by
    intro s s' _ h
    simp only [dec, rel_update] at h
    simp only [R₂]
    rw [h]
    simp
  right := by
    intro s s' _ h
    simp only [R₁, bump] at h ⊢
    action_simp
    grind

/-- The invariant is stable under each rely. -/
theorem stable_R₁ : ∀ s s', I s → R₁ s s' → I s' := fun _ _ _ h => h

theorem stable_R₂ : ∀ s s', I s → R₂ s s' → I s' := by
  intro s s' hs h
  simp only [I] at hs ⊢
  simp only [R₂] at h
  omega

/-- **Composed by rely/guarantee**, with each component verified against the
other's interface. -/
theorem next_preserves : Preserves next I :=
  Preserves.orElse_of_compatible compatible stable_R₁ stable_R₂

/-! ## The same composition with the rely *derived* ("rely as output")

Each component's obligation can be stated in its own vocabulary (a guarantee
lemma), and then the rely is no longer a parameter: `derivedRely I` is the only
sensible one, and `Compatible` against it is definitional. -/

/-- The guarantee lemma for `dec`, stated with no reference to the other
component or to any `Rel`. -/
theorem dec_guarantee : ∀ s s', I s → rel dec s s' → I s' := by
  intro s s' hi h
  simp only [dec, I] at hi h ⊢
  action_simp
  grind

/-- The guarantee lemma for `bump`. -/
theorem bump_guarantee : ∀ s s', I s → rel bump s s' → I s' := by
  intro s s' _ h
  simp only [bump, I] at h ⊢
  action_simp
  grind

/-- Against the derived relies, `Compatible` is definitional — the only content
is the two guarantee lemmas. -/
theorem compatible_derived :
    Compatible I dec bump (derivedRely I) (derivedRely I) :=
  compatible_of_guarantees dec_guarantee bump_guarantee

/-- **The new shortcut**: the same `next_preserves`, with no explicit `Rel` at
the call site. The refined interfaces remain available (above) for the residual
tier where the rely is a genuine value constraint, not `I → I`. -/
theorem next_preserves_by_guarantees : Preserves next I := by
  simpa [next] using preserves_of_guarantees dec_guarantee bump_guarantee

/-- The invariant is not provable by the frame machinery: both components have the
same footprint (the whole cell), so `Disjoint` is provably false for it. -/
theorem not_disjoint_self :
    ¬ Disjoint (View.ofLens (Lens.id : Lens Cell Cell)) (View.ofLens Lens.id) := by
  intro h
  have hh := h.set_set (⟨0⟩ : Cell) (⟨1⟩ : Cell) (⟨2⟩ : Cell)
  simp only [View.ofLens, Lens.id] at hh
  have : (1 : Nat) = 2 := congrArg Cell.v hh
  omega

/-- Sanity check: the composed system really does step as `dec` or `bump`, and the
flat proof agrees. -/
theorem next_preserves_direct : Preserves next I := by
  unfold Preserves
  intro s hs s' h
  simp only [next, dec, bump, I] at hs h ⊢
  action_simp
  grind

end Examples.RelyGuarantee
