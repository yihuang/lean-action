/-
LeanAction.Action
=================

The action DSL: state transitions as a Prop-valued nondeterministic state monad.

```
ActionM σ α := σ → Nondet (α × σ)   -- state transitions with a return value
Action  σ   := ActionM σ Done       -- plain state transitions (notation)
```

where `Done` is a singleton type in the *same universe* as `σ`. Keeping the
state and the return value in one universe is exactly what makes Lean's
`Monad`/`Alternative` classes applicable, so we get for free

* `do`-notation (`let x ← get`, `modify`, `write`, `read`),
* `<|>` for angelic (nondeterministic) choice,
* `failure` for deadlock.

`Action` is a *notation* rather than an `abbrev` on purpose: it expands to
`ActionM σ Done` before elaboration, keeping `ActionM` as the head of the
elaborated type. With a plain `abbrev`, Lean's `do`-elaborator would try to
synthesize `Pure Action` for the unapplied abbreviation and fail.

`rel A s s'` is the underlying state-transition relation:

```
rel A s s' = A s (Done.mk, s')
```

so an action can be read either as a monadic program or as a relation; the
relation view is what `Rel.ReflTransGen` and the proof layer use.

The `@[simp]` lemmas `rel_*` form the *semantic unfolding set*: `simp` turns any
composite action into a first-order `Prop` about the state, which is what the
automation in `LeanAction.Tactic` exploits.
-/
import Std
import LeanAction.Nondet
import LeanAction.Rel

universe u

namespace LeanAction

/-- Singleton type used as the return type of plain (valueless) statements.
It lives in the same universe as the state, which is what the state monad
needs in order to be a Lean `Monad` at that universe. -/
inductive Done : Type u where
  | mk

namespace Done

instance : Subsingleton Done := ⟨fun a b => by cases a; cases b; rfl⟩

theorem eq_mk (d : Done) : d = Done.mk := Subsingleton.elim d Done.mk

theorem mk_eq (d : Done) : Done.mk = d := (eq_mk d).symm

@[simp] theorem eq_iff_true (d e : Done) : (d = e) = True := propext ⟨fun _ => trivial, fun _ => Subsingleton.elim d e⟩

end Done

/-- Nondeterministic state monad: `ActionM σ α` is a transition on `σ` that may
return a value of type `α`, possibly in several ways. -/
abbrev ActionM (σ : Type u) (α : Type u) : Type u := σ → Nondet (α × σ)

namespace ActionM

variable {σ : Type u}

instance instMonad : Monad (ActionM σ) where
  pure a := fun s z => z = (a, s)
  bind x f := fun s z => ∃ p : _ × σ, x s p ∧ f p.1 p.2 z
  map f x := fun s z => ∃ p : _ × σ, x s p ∧ (f p.1, p.2) = z
  seq xf y := fun s z => ∃ p : _ × σ, xf s p ∧ ∃ q : _ × σ, y () p.2 q ∧ (p.1 q.1, q.2) = z
  seqLeft x y := fun s z => ∃ p : _ × σ, x s p ∧ ∃ q : _ × σ, y () p.2 q ∧ z = (p.1, q.2)
  seqRight x y := fun s z => ∃ p : _ × σ, x s p ∧ ∃ q : _ × σ, y () p.2 q ∧ z = (q.1, q.2)

instance instAlternative : Alternative (ActionM σ) where
  failure := fun _ _ => False
  orElse := fun x y => fun s z => x s z ∨ y () s z
  pure a := fun s z => z = (a, s)
  map f x := fun s z => ∃ p : _ × σ, x s p ∧ (f p.1, p.2) = z
  seq xf y := fun s z => ∃ p : _ × σ, xf s p ∧ ∃ q : _ × σ, y () p.2 q ∧ (p.1 q.1, q.2) = z
  seqLeft x y := fun s z => ∃ p : _ × σ, x s p ∧ ∃ q : _ × σ, y () p.2 q ∧ z = (p.1, q.2)
  seqRight x y := fun s z => ∃ p : _ × σ, x s p ∧ ∃ q : _ × σ, y () p.2 q ∧ z = (q.1, q.2)

/-- Read the state through a projection, without changing it. -/
def read (f : σ → α) : ActionM σ α := fun s z => z = (f s, s)

/-- Return the current state. -/
def get : ActionM σ σ := read id

/-- Overwrite the state. -/
def write (v : σ) : ActionM σ Done := fun _ z => z = (Done.mk, v)

/-- Transform the state. -/
def modify (f : σ → σ) : ActionM σ Done := fun s z => z = (Done.mk, f s)

@[simp] theorem read_apply {f : σ → α} {s : σ} {z : α × σ} :
    (read f : ActionM σ α) s z ↔ z = (f s, s) := Iff.rfl

@[simp] theorem get_apply {s : σ} {z : σ × σ} : (get : ActionM σ σ) s z ↔ z = (s, s) := Iff.rfl

@[simp] theorem write_apply {v s : σ} {z : Done × σ} :
    (write v : ActionM σ Done) s z ↔ z = (Done.mk, v) := Iff.rfl

@[simp] theorem modify_apply {f : σ → σ} {s : σ} {z : Done × σ} :
    (modify f : ActionM σ Done) s z ↔ z = (Done.mk, f s) := Iff.rfl

/-! `simp` semantics of the monad operations: these let `simp` push `rel`
through `do`-blocks (`>>=`, `pure`, `<|>`) without any user annotation. -/

@[simp] theorem pure_apply {a : α} {s : σ} {z : α × σ} :
    (pure a : ActionM σ α) s z ↔ z = (a, s) := Iff.rfl

@[simp] theorem bind_apply {x : ActionM σ α} {f : α → ActionM σ β} {s : σ} {z : β × σ} :
    (x >>= f) s z ↔ ∃ p : α × σ, x s p ∧ f p.1 p.2 z := Iff.rfl

@[simp] theorem map_apply {f : α → β} {x : ActionM σ α} {s : σ} {z : β × σ} :
    (f <$> x) s z ↔ ∃ p : α × σ, x s p ∧ (f p.1, p.2) = z := Iff.rfl

@[simp] theorem orElse_apply {x y : ActionM σ α} {s : σ} {z : α × σ} :
    (x <|> y) s z ↔ x s z ∨ y s z := Iff.rfl

@[simp] theorem failure_apply {s : σ} {z : α × σ} : ¬ (failure : ActionM σ α) s z := id

end ActionM

/-- Plain state transitions: notation for `ActionM σ Done`. -/
notation "Action" σ:max => ActionM σ Done

/-! ## The action algebra -/

variable {σ : Type u}
variable {α : Type u}

/-- The state-transition relation denoted by an action. -/
def rel (A : Action σ) : Rel σ σ := fun s s' => A s (Done.mk, s')

/-- Build an action out of a transition relation. -/
def ofRel (R : Rel σ σ) : Action σ := fun s z => R s z.2

@[simp] theorem rel_ofRel {R : Rel σ σ} {s s' : σ} : rel (ofRel R) s s' ↔ R s s' := Iff.rfl

/-- `rel` is a complete invariant of an action. -/
theorem ext {A B : Action σ} (h : ∀ s s', rel A s s' ↔ rel B s s') : A = B := by
  funext s z
  obtain ⟨a, s'⟩ := z
  cases a
  exact propext (h s s')

theorem ofRel_rel (A : Action σ) : ofRel (rel A) = A := by
  funext s z
  obtain ⟨a, s'⟩ := z
  cases a
  rfl

/-! ### Primitives -/

/-- Keep the state unchanged. -/
def skip : Action σ := fun s z => z = (Done.mk, s)

/-- Deadlock: no transition is possible. -/
def fail : Action σ := fun _ _ => False

/-- `guard P` proceeds when `P` holds, and deadlocks otherwise. -/
def guard (P : σ → Prop) : Action σ := fun s z => P s ∧ z = (Done.mk, s)

/-- Continue only when `P` holds; read as a proof obligation. -/
def assert (P : σ → Prop) : Action σ := guard P

/-- Continue only when `P` holds; read as an environment assumption. -/
def assume (P : σ → Prop) : Action σ := guard P

/-- Set the state to `f s`. -/
def update (f : σ → σ) : Action σ := fun s z => z = (Done.mk, f s)

/-- Set the state to a fixed value. -/
def set (v : σ) : Action σ := fun _ z => z = (Done.mk, v)

/-- Perform any transition permitted by the relation `R`. -/
def nondet (R : Rel σ σ) : Action σ := fun s z => R s z.2

/-- The *non-stuttering* part of `A`: the `A`-steps that actually change the
state. This is TLA's `⟨A⟩_v` with the whole state as the variable, written
`⟨A⟩`. Fairness of `⟨A⟩` (not of `A`) is what the stuttering-safe WF1 rule
consumes. -/
def nonStutter (A : Action σ) : Action σ := fun s z => rel A s z.2 ∧ z.2 ≠ s

/-- Angelic choice: `A <|> B` may behave as `A` or as `B`. -/
def choice (A B : Action σ) : Action σ := fun s z => A s z ∨ B s z

/-- Sequential composition: first `A`, then `B`. -/
def seq (A B : Action σ) : Action σ := A >>= fun _ => B

/-- `iterate A n` performs `A` exactly `n` times. -/
def iterate (A : Action σ) : Nat → Action σ
  | 0 => skip
  | n + 1 => seq A (iterate A n)

/-- `loop P A` iterates `A` while `P` holds and stops in a state where `P` fails. -/
def loop (P : σ → Prop) (A : Action σ) : Action σ :=
  fun s z => Rel.ReflTransGen (fun a b => P a ∧ rel A a b) s z.2 ∧ ¬ P z.2

/-- Angelic choice over a family of actions. -/
def choiceAll (B : α → Action σ) : Action σ := fun s z => ∃ a, B a s z

/-- Sequential composition notation: `A ;; B` is "first `A`, then `B`". -/
infixl:60 " ;; " => seq

@[inherit_doc] notation "while[" P "]" A => loop P A

/-! ### Semantic unfolding lemmas

These are the lemmas the automation rewrites with. They are all `[simp]`, and
they never mention `rel` on the right-hand side, so `simp` terminates with a
first-order goal about states. -/

@[simp] theorem rel_skip {s s' : σ} : rel (skip : Action σ) s s' ↔ s' = s := by
  unfold rel skip
  simp

@[simp] theorem rel_fail {s s' : σ} : ¬ rel (fail : Action σ) s s' := by
  unfold rel fail
  simp

@[simp] theorem rel_guard {P : σ → Prop} {s s' : σ} :
    rel (guard P : Action σ) s s' ↔ P s ∧ s' = s := by
  unfold rel guard
  simp

@[simp] theorem rel_assert {P : σ → Prop} {s s' : σ} :
    rel (assert P : Action σ) s s' ↔ P s ∧ s' = s := by
  simp [assert]

@[simp] theorem rel_assume {P : σ → Prop} {s s' : σ} :
    rel (assume P : Action σ) s s' ↔ P s ∧ s' = s := by
  simp [assume]

@[simp] theorem rel_update {f : σ → σ} {s s' : σ} :
    rel (update f : Action σ) s s' ↔ s' = f s := by
  unfold rel update
  simp

@[simp] theorem rel_set {v s s' : σ} : rel (set v : Action σ) s s' ↔ s' = v := by
  unfold rel set
  simp

@[simp] theorem rel_nondet {R : Rel σ σ} {s s' : σ} :
    rel (nondet R : Action σ) s s' ↔ R s s' := Iff.rfl

@[simp] theorem rel_nonStutter {A : Action σ} {s s' : σ} :
    rel (nonStutter A) s s' ↔ rel A s s' ∧ s' ≠ s := Iff.rfl

/-- Monadic `modify` seen as a transition relation. -/
@[simp] theorem rel_modify {f : σ → σ} {s s' : σ} :
    rel (ActionM.modify f) s s' ↔ s' = f s := by
  unfold rel
  simp

/-- Monadic `write` seen as a transition relation. -/
@[simp] theorem rel_write {v s s' : σ} : rel (ActionM.write v) s s' ↔ s' = v := by
  unfold rel
  simp

@[simp] theorem rel_choice {A B : Action σ} {s s' : σ} :
    rel (choice A B) s s' ↔ rel A s s' ∨ rel B s s' := Iff.rfl

/-- `<|>` (the `Alternative` notation) as angelic choice. -/
@[simp] theorem rel_orElse {A B : Action σ} {s s' : σ} :
    rel (A <|> B) s s' ↔ rel A s s' ∨ rel B s s' := Iff.rfl

@[simp] theorem rel_failure {s s' : σ} : ¬ rel (failure : Action σ) s s' := id

@[simp] theorem rel_seq {A B : Action σ} {s s' : σ} :
    rel (seq A B) s s' ↔ ∃ t, rel A s t ∧ rel B t s' := by
  show (∃ p : Done × σ, A s p ∧ B p.2 (Done.mk, s')) ↔ ∃ t, A s (Done.mk, t) ∧ B t (Done.mk, s')
  constructor
  · rintro ⟨⟨a, t⟩, ha, hb⟩
    cases a
    exact ⟨t, ha, hb⟩
  · rintro ⟨t, ha, hb⟩
    exact ⟨(Done.mk, t), ha, hb⟩

/-- `rel` pushed through `do`-notation binds. This is the lemma that makes
semantic unfolding work for actions written as `do`-blocks. -/
@[simp] theorem rel_bind {α : Type u} {x : ActionM σ α} {f : α → Action σ} {s s' : σ} :
    rel (x >>= f) s s' ↔ ∃ p : α × σ, x s p ∧ rel (f p.1) p.2 s' := Iff.rfl

/-- Special case of `rel_bind` for plain statements (`Done` is a singleton), so
`do`-blocks of statements rewrite to the expected `∃ t, rel A s t ∧ rel B t s'`.
Not a global `simp` lemma: `action_simp` tries it *before* the general
`rel_bind`, which keeps `do`-blocks in the familiar `∃ t` shape. -/
theorem rel_bind_action {A : Action σ} {f : Done → Action σ} {s s' : σ} :
    rel (A >>= f) s s' ↔ ∃ t, rel A s t ∧ rel (f Done.mk) t s' := by
  rw [rel_bind]
  constructor
  · rintro ⟨⟨a, t⟩, ha, hb⟩
    cases a
    exact ⟨t, ha, hb⟩
  · rintro ⟨t, ha, hb⟩
    exact ⟨(Done.mk, t), ha, hb⟩

@[simp] theorem rel_choiceAll {B : α → Action σ} {s s' : σ} :
    rel (choiceAll B) s s' ↔ ∃ a, rel (B a) s s' := Iff.rfl

@[simp] theorem rel_iterate_zero {A : Action σ} {s s' : σ} :
    rel (iterate A 0) s s' ↔ s' = s := by
  simp [iterate]

@[simp] theorem rel_iterate_succ {A : Action σ} {n : Nat} {s s' : σ} :
    rel (iterate A (n + 1)) s s' ↔ ∃ t, rel A s t ∧ rel (iterate A n) t s' := by
  simp [iterate, rel_seq]

/-- A guarded sequential action cannot run when the guard fails. -/
theorem not_rel_guard_seq {P : σ → Prop} {A : Action σ} {s t : σ} (h : ¬ P s) :
    ¬ rel (guard P ;; A) s t := by
  intro hrel
  rw [rel_seq] at hrel
  obtain ⟨u, hg, -⟩ := hrel
  rw [rel_guard] at hg
  exact h hg.1

/-- Unfolding of `loop`. Deliberately *not* a `simp` lemma: rewriting the
closure would not terminate. Use it explicitly at the start of an induction. -/
theorem rel_loop {P : σ → Prop} {A : Action σ} {s s' : σ} :
    rel (loop P A) s s' ↔
      Rel.ReflTransGen (fun a b => P a ∧ rel A a b) s s' ∧ ¬ P s' := Iff.rfl

/-! ### Enabledness: the "other half" of the `rel_*` set

`rel_*` normalizes *what happened*; `enabled_*` normalizes *what can happen*.
This is the shape TLAPS's `ENABLED` rewrite rules play: fairness and
leads-to rules (`WeakFair`, `leadsTo_of_wf1`) consume enabledness facts, and
every primitive/combinator gets an `@[simp] enabled_*` lemma whose RHS
mentions neither `Enabled` nor `rel`, so enabledness obligations collapse
under the same `action_simp; grind` pipeline as everything else. -/

/-- `A` is enabled at `s`: it has at least one possible successor. -/
def Enabled (A : Action σ) : Nondet σ := fun s => ∃ s', rel A s s'

@[simp] theorem enabled_skip {s : σ} : Enabled (skip : Action σ) s ↔ True := by
  simp [Enabled]

@[simp] theorem enabled_fail {s : σ} : Enabled (fail : Action σ) s ↔ False := by
  simp [Enabled]

@[simp] theorem enabled_failure {s : σ} : Enabled (failure : Action σ) s ↔ False := by
  simp [Enabled]

@[simp] theorem enabled_guard {P : σ → Prop} {s : σ} :
    Enabled (guard P : Action σ) s ↔ P s := by
  simp [Enabled]

@[simp] theorem enabled_assert {P : σ → Prop} {s : σ} :
    Enabled (assert P : Action σ) s ↔ P s := by
  simp [Enabled]

@[simp] theorem enabled_assume {P : σ → Prop} {s : σ} :
    Enabled (assume P : Action σ) s ↔ P s := by
  simp [Enabled]

@[simp] theorem enabled_update {f : σ → σ} {s : σ} :
    Enabled (update f : Action σ) s ↔ True := by
  simp [Enabled]

@[simp] theorem enabled_set {v s : σ} : Enabled (set v : Action σ) s ↔ True := by
  simp [Enabled]

@[simp] theorem enabled_nondet {R : Rel σ σ} {s : σ} :
    Enabled (nondet R : Action σ) s ↔ ∃ s', R s s' := by
  simp [Enabled]

@[simp] theorem enabled_nonStutter {A : Action σ} {s : σ} :
    Enabled (nonStutter A) s ↔ ∃ s', rel A s s' ∧ s' ≠ s := by
  simp [Enabled]

@[simp] theorem enabled_orElse {A B : Action σ} {s : σ} :
    Enabled (A <|> B) s ↔ Enabled A s ∨ Enabled B s := by
  simp only [Enabled, rel_orElse]
  constructor
  · rintro ⟨s', h | h⟩
    · exact Or.inl ⟨s', h⟩
    · exact Or.inr ⟨s', h⟩
  · rintro (⟨s', h⟩ | ⟨s', h⟩)
    · exact ⟨s', Or.inl h⟩
    · exact ⟨s', Or.inr h⟩

@[simp] theorem enabled_choice {A B : Action σ} {s : σ} :
    Enabled (choice A B) s ↔ Enabled A s ∨ Enabled B s :=
  enabled_orElse

@[simp] theorem enabled_seq {A B : Action σ} {s : σ} :
    Enabled (seq A B) s ↔ ∃ t, rel A s t ∧ Enabled B t := by
  simp only [Enabled, rel_seq]
  constructor
  · rintro ⟨u, t, h1, h2⟩
    exact ⟨t, h1, u, h2⟩
  · rintro ⟨t, h1, u, h2⟩
    exact ⟨u, t, h1, h2⟩

@[simp] theorem enabled_choiceAll {B : α → Action σ} {s : σ} :
    Enabled (choiceAll B) s ↔ ∃ a, Enabled (B a) s := by
  simp only [Enabled, rel_choiceAll]
  constructor
  · rintro ⟨s', a, h⟩
    exact ⟨a, s', h⟩
  · rintro ⟨a, s', h⟩
    exact ⟨s', a, h⟩

end LeanAction
