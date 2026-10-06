/-
LeanAction.Proof
================

The proof layer: safety via inductive invariants, Hoare triples, modules and
refinement.

The key engine is `Preserves.reach`: an inductive proof over `Rel.ReflTransGen`
that carries a preserved predicate from the initial state to *every* reachable
state. Every other safety statement in this file is a corollary of it, so the
automation in `LeanAction.Tactic` only ever has to discharge **one-step**
obligations.
-/
import Std
import LeanAction.Action
import LeanAction.Lens

universe u

namespace LeanAction

open Nondet

variable {σ τ : Type u} {σ_a σ_c : Type u}

/-- Reachability: `Reach A s s'` holds when `s'` is obtained from `s` by finitely
many steps of `A`. -/
def Reach (A : Action σ) : Rel σ σ := Rel.ReflTransGen (rel A)

theorem Reach.refl (A : Action σ) (s : σ) : Reach A s s := Rel.ReflTransGen.refl s

theorem Reach.step {A : Action σ} {s t u : σ} (hst : Reach A s t) (htu : rel A t u) :
    Reach A s u := Rel.ReflTransGen.tail hst htu

theorem Reach.trans {A : Action σ} {s t u : σ} (hst : Reach A s t) (htu : Reach A t u) :
    Reach A s u := Rel.reflTransGen_trans hst htu

theorem Reach.single {A : Action σ} {s t : σ} (h : rel A s t) : Reach A s t :=
  Rel.reflTransGen_single h

theorem Reach.mono {A B : Action σ} (h : ∀ s s', rel A s s' → rel B s s') {s t : σ}
    (hr : Reach A s t) : Reach B s t :=
  Rel.reflTransGen_mono h hr

/-! ## One-step invariants -/

/-- `I` is preserved by every step of `A`. -/
def Preserves (A : Action σ) (I : Nondet σ) : Prop :=
  ∀ s, I s → ∀ s', rel A s s' → I s'

theorem Preserves.skip (I : Nondet σ) : Preserves (skip : Action σ) I := by
  intro s hs s' h
  simp only [rel_skip] at h
  simpa [h] using hs

theorem Preserves.fail (I : Nondet σ) : Preserves (fail : Action σ) I := by
  intro s _ s' h
  simp only [rel_fail] at h

theorem Preserves.failure (I : Nondet σ) : Preserves (failure : Action σ) I := by
  intro s _ s' h
  simp only [rel_failure] at h

theorem Preserves.guard {P : σ → Prop} {I : Nondet σ} (_h : ∀ s, I s → P s) :
    Preserves (guard P : Action σ) I := by
  intro s hs s' hstep
  simp only [rel_guard] at hstep
  simpa [hstep.2] using hs

theorem Preserves.assert {P : σ → Prop} {I : Nondet σ} (h : ∀ s, I s → P s) :
    Preserves (assert P : Action σ) I :=
  Preserves.guard (I := I) h

theorem Preserves.update {f : σ → σ} {I : Nondet σ} (h : ∀ s, I s → I (f s)) :
    Preserves (update f : Action σ) I := by
  intro s hs s' hstep
  simp only [rel_update] at hstep
  simpa [hstep] using h s hs

theorem Preserves.nondet {R : Rel σ σ} {I : Nondet σ}
    (h : ∀ s, I s → ∀ s', R s s' → I s') : Preserves (nondet R : Action σ) I := by
  intro s hs s' hstep
  simp only [rel_nondet] at hstep
  exact h s hs s' hstep

theorem Preserves.seq {A B : Action σ} {I : Nondet σ}
    (hA : Preserves A I) (hB : Preserves B I) : Preserves (seq A B) I := by
  intro s hs s' hstep
  simp only [rel_seq] at hstep
  obtain ⟨t, h1, h2⟩ := hstep
  exact hB t (hA s hs t h1) s' h2

theorem Preserves.orElse {A B : Action σ} {I : Nondet σ}
    (hA : Preserves A I) (hB : Preserves B I) : Preserves (A <|> B) I := by
  intro s hs s' hstep
  simp only [rel_orElse] at hstep
  exact hstep.elim (hA s hs s') (hB s hs s')

theorem Preserves.choice {A B : Action σ} {I : Nondet σ}
    (hA : Preserves A I) (hB : Preserves B I) : Preserves (choice A B) I :=
  Preserves.orElse hA hB

theorem Preserves.choiceAll {ι : Type u} {B : ι → Action σ} {I : Nondet σ}
    (h : ∀ i, Preserves (B i) I) : Preserves (choiceAll B) I := by
  intro s hs s' hstep
  simp only [rel_choiceAll] at hstep
  obtain ⟨i, hi⟩ := hstep
  exact h i s hs s' hi

theorem Preserves.iterate {A : Action σ} {I : Nondet σ} (h : Preserves A I) :
    ∀ n, Preserves (iterate A n) I
  | 0 => by
    intro s hs s' hstep
    simp only [rel_iterate_zero] at hstep
    simpa [hstep] using hs
  | n + 1 => by
    intro s hs s' hstep
    simp only [rel_iterate_succ] at hstep
    obtain ⟨t, h1, h2⟩ := hstep
    exact Preserves.iterate h n t (h s hs t h1) s' h2

theorem Preserves.and {A : Action σ} {I J : Nondet σ} (hI : Preserves A I)
    (hJ : Preserves A J) : Preserves A (fun s => I s ∧ J s) :=
  fun s hs s' hstep => ⟨hI s hs.1 s' hstep, hJ s hs.2 s' hstep⟩

/-- **The induction engine.** A predicate preserved by every step of `A` holds
at every `A`-reachable state. -/
theorem Preserves.reach {A : Action σ} {I : Nondet σ} (h : Preserves A I) :
    ∀ s, I s → ∀ s', Reach A s s' → I s' := by
  intro s hs s' hr
  revert hs
  induction hr with
  | refl => exact fun hs => hs
  | tail _ hstep ih => exact fun hs => h _ (ih hs) _ hstep

/-- Invariance from an initial state set. -/
theorem Preserves.from_init {A : Action σ} {I Init : Nondet σ} (hstep : Preserves A I)
    (hinit : Init ⊆ₙ I) : ∀ s, Init s → ∀ s', Reach A s s' → I s' :=
  fun s hs s' hr => hstep.reach s (hinit s hs) s' hr

/-! ## Hoare triples -/

/-- Partial-correctness Hoare triple: every terminating run of `A` from a state
satisfying `P` ends in a state satisfying `Q`. -/
def Hoare (P : Nondet σ) (A : Action σ) (Q : Nondet σ) : Prop :=
  ∀ s, P s → ∀ s', rel A s s' → Q s'

theorem Hoare.skip {P Q : Nondet σ} (h : P ⊆ₙ Q) : Hoare P (skip : Action σ) Q := by
  intro s hs s' hstep
  simp only [rel_skip] at hstep
  simpa [hstep] using h s hs

theorem Hoare.fail {P Q : Nondet σ} : Hoare P (fail : Action σ) Q := by
  intro s _ s' hstep
  simp only [rel_fail] at hstep

theorem Hoare.seq {P Q R : Nondet σ} {A B : Action σ} (hA : Hoare P A R)
    (hB : Hoare R B Q) : Hoare P (seq A B) Q := by
  intro s hs s' hstep
  simp only [rel_seq] at hstep
  obtain ⟨t, h1, h2⟩ := hstep
  exact hB t (hA s hs t h1) s' h2

theorem Hoare.orElse {P Q : Nondet σ} {A B : Action σ} (hA : Hoare P A Q)
    (hB : Hoare P B Q) : Hoare P (A <|> B) Q := by
  intro s hs s' hstep
  simp only [rel_orElse] at hstep
  exact hstep.elim (hA s hs s') (hB s hs s')

theorem Hoare.choice {P Q : Nondet σ} {A B : Action σ} (hA : Hoare P A Q)
    (hB : Hoare P B Q) : Hoare P (choice A B) Q :=
  Hoare.orElse hA hB

theorem Hoare.conseq {P P' Q Q' : Nondet σ} {A : Action σ} (hPP' : P ⊆ₙ P')
    (h : Hoare P' A Q') (hQ'Q : Q' ⊆ₙ Q) : Hoare P A Q :=
  fun s hs s' hstep => hQ'Q s' (h s (hPP' s hs) s' hstep)

theorem Hoare.guard {P Q : Nondet σ} {R : σ → Prop} (_h : ∀ s, P s → R s)
    (hQ : P ⊆ₙ Q) : Hoare P (guard R : Action σ) Q := by
  intro s hs s' hstep
  simp only [rel_guard] at hstep
  simpa [hstep.2] using hQ s hs

/-- Hoare rule for a focused action: the inner triple, transported through the
view, gives the outer pre/post-conditions. -/
theorem Hoare.focusView {v : View σ α} {A : Action α} {P Q : Nondet σ}
    {P' Q' : Nondet α} (hP : ∀ s, P s → P' (v.get s))
    (h : Hoare P' A Q')
    (hQ : ∀ s a, P s → Q' a → Q (v.set s a)) : Hoare P (focusView v A) Q := by
  intro s hs s' hstep
  simp only [rel_focusView] at hstep
  obtain ⟨a', ha, hs'⟩ := hstep
  rw [hs']
  exact hQ s a' hs (h (v.get s) (hP s hs) a' ha)

/-! ## Modules -/

/-- A transition system: an initial state set and a next-state action. -/
structure Module (σ : Type u) where
  init : Nondet σ
  next : Action σ

namespace Module

variable {M : Module σ}

/-- States reachable from an initial state. -/
def reachable (M : Module σ) : Nondet σ := fun s => ∃ s₀, M.init s₀ ∧ Reach M.next s₀ s

/-- Safety: every reachable state satisfies `P`. -/
def Safe (M : Module σ) (P : Nondet σ) : Prop :=
  ∀ s, M.init s → ∀ s', Reach M.next s s' → P s'

/-- Safety from a one-step invariant. This is the main entry point for the
automation: `safe_of_preserves` reduces safety to `init ⊆ I` and
`Preserves next I`, both of which are first-order goals over states. -/
theorem safe_of_preserves {P : Nondet σ} (hinit : M.init ⊆ₙ P)
    (hstep : Preserves M.next P) : M.Safe P :=
  fun s hs s' hr => hstep.reach s (hinit s hs) s' hr

theorem safe_of_invariant {I P : Nondet σ} (hinit : M.init ⊆ₙ I)
    (hstep : Preserves M.next I) (hIP : I ⊆ₙ P) : M.Safe P :=
  fun s hs s' hr => hIP s' (hstep.reach s (hinit s hs) s' hr)

theorem Safe.mono {M : Module σ} {P Q : Nondet σ} (h : M.Safe P) (hPQ : P ⊆ₙ Q) :
    M.Safe Q := fun s hs s' hr => hPQ s' (h s hs s' hr)

/-- Interleaving (asynchronous) composition of two modules on a product state:
each step is a step of one component, leaving the other unchanged. -/
def interleave (M : Module σ) (N : Module τ) : Module (σ × τ) where
  init := fun p => M.init p.1 ∧ N.init p.2
  next := liftLeft M.next <|> liftRight N.next

@[simp] theorem rel_interleave_next {M : Module σ} {N : Module τ} {p q : σ × τ} :
    rel (M.interleave N).next p q ↔
      (rel M.next p.1 q.1 ∧ q.2 = p.2) ∨ (rel N.next p.2 q.2 ∧ q.1 = p.1) := by
  simp [interleave]

/-- A component invariant of an interleaved system. -/
theorem interleave_preserves_left {M : Module σ} {N : Module τ} {I : Nondet σ}
    (hM : Preserves M.next I) :
    Preserves (M.interleave N).next (fun p : σ × τ => I p.1 ∧ True) := by
  intro p hp q hstep
  simp only [rel_interleave_next] at hstep
  rcases hstep with ⟨h1, -⟩ | ⟨-, h1⟩
  · exact ⟨hM p.1 hp.1 q.1 h1, trivial⟩
  · exact ⟨by rw [h1]; exact hp.1, trivial⟩

end Module

/-! ## Refinement -/

/-- Simulation between an abstract (left) and a concrete (right) module through
a relation `R` on states. Each concrete step is matched by zero or more abstract
steps (stuttering is allowed). -/
def Simulates (R : Rel σ_a σ_c) (Abs : Module σ_a) (Conc : Module σ_c) : Prop :=
  (∀ c, Conc.init c → ∃ a, Abs.init a ∧ R a c) ∧
  (∀ a c, R a c → ∀ c', rel Conc.next c c' →
    ∃ a', Rel.ReflTransGen (rel Abs.next) a a' ∧ R a' c')

/-- Data refinement: the abstraction map `f` is a simulation. -/
def Refines (f : σ_c → σ_a) (Abs : Module σ_a) (Conc : Module σ_c) : Prop :=
  Simulates (fun a c => a = f c) Abs Conc

/-- A simulation lifts to reachability: any concrete run is matched by an
abstract run whose final state is related to the concrete final state. -/
theorem Refines.reach {f : σ_c → σ_a} {Abs : Module σ_a} {Conc : Module σ_c}
    (h : Refines f Abs Conc) :
    ∀ {a : σ_a} {c c' : σ_c}, a = f c → Reach Conc.next c c' →
      ∃ a', Reach Abs.next a a' ∧ a' = f c' := by
  intro a c c' hac hr
  revert hac
  induction hr with
  | refl => intro hac; exact ⟨a, Reach.refl _ _, hac⟩
  | tail hrc hc' ih =>
    intro hac
    obtain ⟨a₁, har, ha₁⟩ := ih hac
    obtain ⟨a₂, ha₁a₂, ha₂⟩ := h.2 a₁ _ ha₁ _ hc'
    exact ⟨a₂, Reach.trans har ha₁a₂, ha₂⟩

/-- Safety is preserved by data refinement. -/
theorem Refines.safe {f : σ_c → σ_a} {Abs : Module σ_a} {Conc : Module σ_c}
    {P : Nondet σ_a} (h : Refines f Abs Conc) (hsafe : Abs.Safe P) :
    Conc.Safe (fun c => P (f c)) := by
  intro c hc c' hr
  obtain ⟨a, hai, ha⟩ := h.1 c hc
  obtain ⟨a', har, ha'⟩ := h.reach ha hr
  rw [← ha']
  exact hsafe a hai a' har

end LeanAction
