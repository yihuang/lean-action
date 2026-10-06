# LeanAction design document

> Goal: a DSL in Lean 4 for **expressing actions (state-transition relations)**,
> with **inductive invariant proofs automated** as far as possible.

This document records the reasoning behind a prototype that **actually compiles
under `lake build`** (Lean `v4.33.0`, zero external dependencies) — not a paper
proposal. Every code fragment is taken from a file in this repository.

---

## 1. Where the design came from, and the first trade-off

The design started from a discussion of "a DSL for actions (state transitions) in
Lean 4", whose candidate skeletons were:

| Candidate | Pros | Problems |
| --- | --- | --- |
| `Action σ := σ → σ → Prop` (pure relation) | closest to the semantics, clean universes | loses `do`-notation and monadic combinators |
| `Action σ := Set (σ × σ)` | reuses Mathlib's `Set` API | one layer away from the relational view; not computable |
| `ActionM σ α := StateT σ Set α` | `do`/`<|>`/`get`/`set` come for free | needs Mathlib's `Set` monad; `Unit` and the state do not share a universe, so `Action σ := ActionM σ Unit` is a universe error |

What this library does instead is keep **two views**: the **relation** is the
semantic ground truth, the **nondeterministic state monad** is the surface syntax.
The next section explains why, and the two engineering prices paid for it (`Done`,
and `Action` being a notation).

---

## 2. Layered architecture

```
LeanAction/Rel.lean      relation toolkit: Rel, Comp, TransGen, ReflTransGen + induction
LeanAction/Nondet.lean   Nondet α := α → Prop, with Monad/Alternative/Membership
LeanAction/Action.lean   the core DSL: ActionM, Action, primitives, combinators, rel lemmas
LeanAction/Lens.lean     modularity: Lens, View, focus, product lifts, interleave
LeanAction/Proof.lean    proof layer: Reach, Preserves, Hoare, Module, Refines
LeanAction/Tactic.lean   automation: action_simp, step, inv_induct, safe_induct
LeanAction/Liveness.lean temporal layer: Always / Eventually / LeadsTo, behaviors, fairness, ranks
LeanAction/Derive.lean   metaprogramming: view_defs / lens_defs commands
LeanAction/Frame.lean    shared-state composition: Disjoint (frame condition), frame theorem, parallel
Examples/                counters, nested structures, while, interleaving, refinement, …
```

Dependencies are strictly one-directional: `Rel → Nondet → Action → Lens → Proof →
Tactic`. There is **no Mathlib dependency** (§8).

---

## 3. Core semantic decisions

### 3.1 Nondeterminism is a `Prop`-valued monad

```lean
abbrev Nondet (α : Type u) : Type u := α → Prop
```

* `pure a := fun b => b = a`
* `s >>= f := fun b => ∃ a, s a ∧ f a b`
* `s <|> t := fun a => s a ∨ t a`, `failure := fun _ => False`

This is classic **angelic nondeterminism**: `s a` reads "`a` is a possible
result", `>>=` is the union over all branches, `<|>` is disjunction. Because it is
`Prop`-valued the library is inherently a **specification layer** rather than an
execution layer (see §9.1).

First engineering detail: in Lean 4.33 `Alternative.orElse` is **lazy**
(`f α → (Unit → f α) → f α`), so the instance has to be written as
`fun s t => union s (t ())`; and `Applicative`/`Monad`/`Alternative` all need
**every field spelled out**, otherwise `pure` resolves through the default values
of the instance being defined and loops back to itself (a trap actually hit here).

### 3.2 `ActionM σ α := σ → Nondet (α × σ)`

Why not simply `StateT σ Nondet α`? Because `StateT` *is* `σ → m (α × σ)`, and
Lean's `StateT`/`Monad` require **`α` and `σ` to live in the same universe**.
`Unit : Type 0`, so `StateT σ Nondet Unit` is only legal for `σ : Type 0`, which
would pin the state type to `Type 0`.

So the type is written out directly (definitionally the same as `StateT`), with the
monad instances attached explicitly to `ActionM σ` (`Monad` + `Alternative`, all
fields given). Consequences:

* the state `σ : Type u` and the return type `α : Type u` share a universe, so
  `Monad`/`Alternative` apply;
* `do`-notation, `<|>`, `get`/`write`/`modify`/`read` all come for free;
* no Mathlib dependency is needed.

### 3.3 `Done`: the return type of statements

A plain state transition needs a **singleton type in `Type u`** as its return type.
`ULift.{u,0} Unit : Type (u+1)` and `PUnit.{u} : Type (u+1)` are one universe too
high, so the library defines:

```lean
inductive Done : Type u where
  | mk

instance : Subsingleton Done := ⟨fun a b => by cases a; cases b; rfl⟩
@[simp] theorem eq_iff_true (d e : Done) : (d = e) = True := ...
```

`Done.eq_iff_true` and `rel_bind_action` (§4.3) exist to erase `Done` from the
existentials that `do` blocks produce, so that the automation sees the clean shape
`∃ t, rel A s t ∧ rel B t s'`.

### 3.4 `Action` is a notation, not an `abbrev`

```lean
notation "Action" σ:max => ActionM σ Done
```

This was forced by the `do`-elaborator: with
`abbrev Action σ := ActionM σ Done`, an expected type `Action Nat` makes Lean's
`do` block fix the monad variable to the **unapplied** `Action` and then try to
synthesize `Pure Action` — but the instances live on `ActionM σ`, so it fails.

With a notation, `Action Nat` expands to `ActionM Nat Done` before elaboration,
`ActionM` is always the head constant, and instance synthesis works. The price is
that `Action.rel`-style namespacing is impossible (`Action` became a keyword), so
everything in the library lives directly in `namespace LeanAction`; users
`open LeanAction` and use the bare names `rel`, `skip`, `Preserves`, ….

### 3.5 The relational view, `rel`

```lean
def rel (A : Action σ) : Rel σ σ := fun s s' => A s (Done.mk, s')
```

`rel` is the **only** bridge between the two views, and it is **complete**:

```lean
theorem ext {A B : Action σ} (h : ∀ s s', rel A s s' ↔ rel B s s') : A = B
theorem ofRel_rel (A : Action σ) : ofRel (rel A) = A
```

The proof layer only ever talks about `rel`, so specifications can be rewritten as
`do` blocks or as relations without touching the proofs.

---

## 4. The DSL

### 4.1 Primitives

| Notation | Semantics (`rel`) | Meaning |
| --- | --- | --- |
| `skip` | `s' = s` | do nothing |
| `fail` / `failure` | `False` | deadlock |
| `guard P` / `assert P` / `assume P` | `P s ∧ s' = s` | precondition |
| `update f` | `s' = f s` | state update |
| `set v` | `s' = v` | overwrite the state |
| `nondet R` | `R s s'` | any transition allowed by a relation |
| `choiceAll B` | `∃ i, rel (B i) s s'` | choose among a family of actions |

### 4.2 Combinators

| Notation | Semantics (`rel`) |
| --- | --- |
| `A <|> B` (`Alternative`) | `rel A s s' ∨ rel B s s'` |
| `seq A B` / `A >>= f` | `∃ t, rel A s t ∧ rel B t s'` |
| `iterate A n` | `n`-fold composition of `A` |
| `while[P] A` / `loop P A` | `(P ∧ A)^* ; ¬P`, i.e. `ReflTransGen` plus the exit condition |
| `liftLeft A` / `liftRight B` | single-component actions on a product state |

`<|>` reuses Lean's `Alternative` notation and `;`/`do` reuse the monad's bind —
exactly the "reuse existing structures and symbols" goal.

### 4.3 `do`-notation

```lean
def incr : Action Ctr := do
  let s ← (ActionM.get : ActionM Ctr Ctr)
  ActionM.modify fun t => { t with n := t.n + 1, log := s.n :: t.log }
```

`get`/`read`/`write`/`modify` are defined in `namespace ActionM` and re-exported
into `LeanAction`. The semantic lemmas `rel_bind` (general) and `rel_bind_action`
(statement-to-statement) let `simp` reduce a `do` block to an `∃` form directly; in
`action_simp`, `rel_bind_action` is listed **before** `rel_bind` so that
`do A; B` yields the most natural shape `∃ t, rel A s t ∧ rel B t s'`.

### 4.4 The `rel_*` lemma set = semantic normalization

Every `rel_skip`, `rel_seq`, `rel_orElse`, `rel_focus`, … is `@[simp]` and its
**right-hand side no longer mentions `rel`**. Hence `simp`/`grind` are guaranteed
to reduce any composite action to a first-order statement about states, and to
terminate while doing so. That is the foundation of all the automation; there is no
custom rewrite engine anywhere else.

---

## 5. Modularity

### 5.1 `View` (no laws) and `Lens` (with laws)

States built from nested structures need the ability to "zoom into a field". The
library offers two layers:

```lean
structure View (σ α : Type u) where   -- no laws, one line to construct
  get : σ → α
  set : σ → α → σ

structure Lens (σ α : Type u) where   -- get/set plus the three lens laws
  get : σ → α
  set : σ → α → σ
  get_set : ∀ s a, get (set s a) = a
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s a b, set (set s a) b = set s b
```

* `focusView v A` lifts `A : Action α` to `Action σ`; `rel_focusView` is an
  **`Iff.rfl`-level** unfolding that needs no laws at all;
* `Lens.comp`, `View.comp`: nested fields (`Outer → Inner → Nat`);
* `Lens.fst`/`Lens.snd`, `View.fst`/`View.snd`: components of a product.

Why two layers? Because the three lens laws are a **proof burden**. Laws are needed
only for reasoning such as "focusing does not change other fields" (`rel_focus'`),
while *defining* a focused action needs none of them. Decoupling laws from
definitions lets users write a one-line `View` and upgrade to a `Lens` only when
stronger reasoning is required.

**Generation** (`LeanAction/Derive.lean`) has two paths:

1. **`deriving ViewFields, LensFields`** (recommended): emits
   `Struct.fView : View Struct α` and `Struct.fLens : Lens Struct α` per field (the
   three lens laws are closed by structure eta's `rfl`). It goes through the
   `deriving` machinery (marker classes + `Lean.Elab.registerDerivingHandler`), so:
   * declaration names are **absolute** (`Deep.Point.xLens`), correct inside
     namespaces;
   * there is **no doc-comment restriction** (the `deriving` clause is part of the
     structure declaration).
   The price is that **parameterized structures are not supported**: the framework
   names parameter binders hygienically (`Deriving.mkHeader`), so they cannot be
   written into the getter/setter strings; the handler fails with a clear message
   pointing at the command path.
2. **`view_defs T` / `lens_defs T`**: the type is given as a **term**, so
   parameterized structures work too (inside a `section` with
   `variable (α : Type)`, write `view_defs (Box α)`). The implementation is a
   command: the getter/setter strings `"fun s : Box α => s.val"` /
   `"fun s v => { s with val := v }"` are parsed by `Parser.runParserCategory`
   into **well-formed `structInstLVal` nodes**, and `elabCommand` then emits the
   `def`.

Why not a term macro: see §11.6 — the field position in `{ s with f := v }` is a
`Lean.Parser.Term.structInstLVal` node, which a term macro cannot build from an
`ident` antiquotation (the macro *definition* checks fine; the *use site* reports
`unexpected syntax`).

Two usage notes for the command path (both consequences of the implementation, both
documented in `Derive.lean`):

* a custom command **cannot be preceded by a doc comment** (`/-- … -/` only
  attaches to declaration commands); use a plain `/- … -/` comment;
* the structure must live in the current namespace or below it, because
  `elabCommand` prefixes declaration names with the current namespace (otherwise
  they land at `Ns.Ns.Struct.fView`).

### 5.2 Product state and interleaving

```lean
def Module.interleave (M : Module σ) (N : Module τ) : Module (σ × τ) where
  init := fun p => M.init p.1 ∧ N.init p.2
  next := liftLeft M.next <|> liftRight N.next
```

The standard encoding of asynchronous (interleaved) parallelism: the state is a
product, and each step advances either the left or the right component. The
semantic lemmas for `liftLeft`/`liftRight` bake "the other component is unchanged"
directly into `rel`, so the step obligations of an interleaving stay first-order
(see `twoCounters_inv_step` in `Examples/Parallel.lean`).

### 5.3 Refinement

```lean
def Simulates (R : Rel σ_a σ_c) (Abs : Module σ_a) (Conc : Module σ_c) : Prop :=
  (∀ c, Conc.init c → ∃ a, Abs.init a ∧ R a c) ∧
  (∀ a c, R a c → ∀ c' , rel Conc.next c c' →
      ∃ a', Rel.ReflTransGen (rel Abs.next) a a' ∧ R a' c')

def Refines (f : σ_c → σ_a) (Abs : Module σ_a) (Conc : Module σ_c) : Prop :=
  Simulates (fun a c => a = f c) Abs Conc
```

**Stuttering** is allowed (the abstract side may take zero or more steps). The core
theorems are `Refines.reach` (a simulation lifts along concrete reachability) and
`Refines.safe` (safety transfers along a refinement); `Examples/Parallel.lean`
demonstrates "the implementation only stutters more, yet safety is inherited from
the specification".

---

### 5.4 Shared state: making the frame condition explicit (`LeanAction/Frame.lean`)

The `interleave` of §5.2 composes only **product states**, because there "the two
components do not interfere" is *hard-wired into the type*: the state is `σ × τ`,
and one component's action cannot touch the other's. A shared record has no such
convenience — process 1 writes `pc1`, process 2 writes `pc2`, and both may write
`turn`.

To recover compositionality one has to state the **frame condition** as a provable
fact:

```lean
structure Disjoint (v₁ : View σ α) (v₂ : View σ β) : Prop where
  get_set : ∀ s a, v₂.get (v₁.set s a) = v₂.get s     -- writing v₁ does not disturb reading v₂
  set_get : ∀ s b, v₁.get (v₂.set s b) = v₁.get s
  set_set : ∀ s a b, v₁.set (v₂.set s b) a = v₂.set (v₁.set s a) b   -- for simultaneous execution
```

Why **commutation** rather than "different field names"? At this abstraction level
there are no variable names; the only statement available is "one's effect is
invisible to the other". This is a **proof obligation**, not a convention (in
`Examples/Frame.lean` it is discharged by `cases s; rfl`).

On top of it sit three results:

* `Disjoint.get_of_rel`: a focused action does not move the other projection (the
  most-used form of the frame condition);
* `Preserves.focusView` (needs only `get_set`, not the full lens laws): a
  **component-local invariant lifts to the shared state**;
* `ViewModule.parallel_preserves`: the **frame theorem** — an interleaved step
  preserves `P ∘ v₁.get ∧ Q ∘ v₂.get`, where `P` is the responsibility of component
  1 and `Q` of component 2, and the "other half" is transported automatically by
  `Disjoint` (one-sided forms `parallel_preserves_fst/snd` are also provided).

From these come safety and liveness on shared state:

```lean
theorem parallel_safe    -- component invariants (each proved on its own state type) ⇒ composed safety
theorem parallel_leadsTo -- component liveness ⇒ composed liveness (with proj_step /
                         --   weakFair_of_lift / forward_stable_of_preserves: projections
                         --   stutter, hence the sequence-level rank theorem)
```

**The boundary is a theorem, not a remark.** `Examples/Frame.lean` proves that the
two mutex processes do **not** satisfy `Disjoint` (both write `turn`):

```lean
theorem mutex_not_disjoint : ¬ Disjoint mutexP₁ mutexP₂
```

so that protocol genuinely needs a hand-written global invariant (the `inv` of
§11.5), and the natural next step is **rely/guarantee** (letting footprints
overlap by replacing disjointness with R/G conditions) — see §9.3.

Relation to §5.2: the product version is the special case where "the frame
condition is hard-wired into the state type"; `disjoint_fst_snd` is precisely the
disjointness proof for `Lens.fst`/`Lens.snd`.

**When footprints overlap: rely/guarantee.** `Disjoint` says "the environment
cannot touch my footprint". Replacing the **footprint** by a **relation** yields
rely/guarantee: each component declares only the assumption it makes about the
environment (its rely), and the composition rule asks only that "my steps are
permitted by the other's rely":

```lean
structure Compatible (I : Nondet σ) (A₁ A₂ : Action σ) (R₁ R₂ : Rel σ σ) : Prop where
  left  : ∀ s s', I s → rel A₁ s s' → R₂ s s'    -- component 1's steps are permitted by R₂
  right : ∀ s s', I s → rel A₂ s s' → R₁ s s'

theorem Preserves.orElse_of_compatible (hc : Compatible I A₁ A₂ R₁ R₂)
    (h₁ : ∀ s s', I s → R₁ s s' → I s') (h₂ : ∀ s s', I s → R₂ s s') :
    Preserves (A₁ <|> A₂) I
```

The two stability obligations mention only the **interfaces** `R₁`/`R₂`, never the
other component's code — that is the payoff (modularity: the other component can be
re-implemented as long as it still satisfies the interface, and this component's
proof does not change). For **state invariants** what it buys is modularity rather
than shorter proofs (see the infeasibility argument in §11.9); what genuinely
changes the shape of a proof is a **prefix property** ("a region holds until the
goal is reached"):

```lean
theorem relyGuarantee_until (hbeh : ∀ n, rel (A₁ <|> A₂) (b n) (b (n+1)))
    (h₁ : ∀ s s', I s → rel A₁ s s' → I s' ∨ G s')     -- the component's own guarantee
    (h₂ : ∀ s s', I s → rel A₂ s s' → I s')            -- the environment's rely
    (h₀ : I (b 0)) : ∀ n, (∀ j, j ≤ n → ¬ G (b j)) → I (b n)
```

`Examples/MutexLiveness.region_until_goal` is now an instance of this theorem: the
old "six-way `action_simp; grind` plus a hand-written prefix induction" is split
into two interface lemmas (process 1's guarantee, process 2's rely), with the
induction supplied by the library.

**Synchronous (lock-step) composition**: `ViewModule.sync` makes both components
step together; `Disjoint.set_set` guarantees that the order of the two updates does
not matter, and `sync_preserves`/`sync_proj` say that both invariants are preserved
and that each projection advances **exactly** (unlike interleaving, which may
stutter). Note that lock-step composition requires both components to be able to
move.

**Automation**: `disjoint_auto` closes `Disjoint` goals for structure-field views in
one tactic (pointwise unfolding + `cases` + `rfl`).

## 6. The proof layer: a single induction engine

```lean
def Reach (A : Action σ) : Rel σ σ := Rel.ReflTransGen (rel A)

def Preserves (A : Action σ) (I : Nondet σ) : Prop :=
  ∀ s, I s → ∀ s', rel A s s' → I s'

theorem Preserves.reach (h : Preserves A I) :
    ∀ s, I s → ∀ s', Reach A s s' → I s'      -- ← the only induction
```

`Reach` uses `ReflTransGen` (not `TransGen`) so that the "zero steps" case lands
directly on the initial condition. Every safety statement is a corollary of
`Preserves.reach`:

```lean
theorem Module.safe_of_preserves (hinit : M.init ⊆ₙ P) (hstep : Preserves M.next P) : M.Safe P
theorem Module.safe_of_invariant (hinit : M.init ⊆ₙ I) (hstep : Preserves M.next I) (hIP : I ⊆ₙ P) : M.Safe P
```

Hoare triples `Hoare P A Q` are the other face of the same semantics, with rules for
`skip`/`seq`/`<|>`/`guard` and for **focusing** (`Hoare.focusView`: an inner triple
lifts through a view to the outer state).

This "single induction engine + algebra of combinators" structure is precisely why
the automation can stay simple: it only ever has to discharge **one step**, and
never touches the induction itself.

---

## 7. Automation

### 7.1 Why not heavier automation

Candidates were: a custom `aesop` rule set, `@[grind]` annotations everywhere, or
symbolic execution in metaprogramming. The prototype chose a narrower but
**predictable** path:

1. **semantic normalization goes to `simp`** — the `rel_*` set is already a
   complete unfolding rule set (§4.4);
2. **first-order reasoning goes to `grind`** — states are ordinary data structures
   and what remains is arithmetic/equality/disjunction;
3. **the proof skeleton goes to four macros**, which only "arrange the shape" and do
   no search.

So when the automation fails, the failure is always explicable ("some `def` has not
been unfolded", or "`grind` cannot derive this arithmetic fact").

### 7.2 The four macros

| Macro | Purpose |
| --- | --- |
| `action_simp` | `simp (config := {failIfUnchanged := false}) only [rel_*, ActionM.*_apply, Prod.mk.injEq, ...] at *`; unfold action semantics to first order |
| `step` | `action_simp; try grind`: one step obligation |
| `inv_induct` | `unfold Preserves; intro s hs s' hstep; step`: the canonical `Preserves` skeleton |
| `safe_induct` | `apply Module.safe_of_preserves`, leaving the two goals `init ⊆ P` and `Preserves next P` |

Two implementation details matter:

* `failIfUnchanged := false`: `action_simp` must not error when there is no `rel` to
  unfold, otherwise `try step` and subsequent manual unfolding fight each other;
* do **not** use `·` bullets inside a macro: an early version had `·` in a macro
  body, and the caller's `·` competed with the macro's goal focusing, producing the
  bizarre combination of "unsolved goals" and "No goals to be solved". Now the
  pattern is `apply ... <;> try step`, leaving the goal structure to the caller.

### 7.3 A typical user proof

```lean
theorem twoCounters_safe : twoCounters.Safe inv := by
  safe_induct
  · intro p hp                       -- init ⊆ inv
    simp only [twoCounters, Module.interleave, counter, inv] at hp ⊢
    omega
  · inv_induct                       -- Preserves twoCounters.next inv
    simp only [twoCounters, Module.interleave, counter, inv] at *
    action_simp
    grind
```

The pattern is fixed: **first unfold the user's own `def`s (the library cannot
guess them), then `action_simp` to unfold the action semantics, then `grind` to
finish**. Every theorem in `Examples/` follows it.

---

## 8. Relationship to Mathlib

The library **deliberately does not depend on Mathlib**, for three reasons:

1. environment constraints: on the machine this was developed on, Mathlib sources
   and cache were unavailable, and building from source needs several GB;
2. the user's other Lean repositories also keep zero/light dependencies;
3. the library needs very little from Mathlib: `Set`, `Relation.Comp`/
   `ReflTransGen`, `StateT`/`MonadState`. The first two are reproduced in
   `Rel.lean`/`Nondet.lean` in about 200 lines; the latter is replaced by the
   hand-written `ActionM` instances.

**Nothing is lost in interoperability**: `Nondet α` *is* `α → Prop`, and Mathlib's
`Set α` is also `α → Prop` (definitionally the same). So once a user writes
`import Mathlib`:

* `Nondet` values can be used directly as `Set`s, and Mathlib's `∈`/`⊆`/`⋃` lemmas
  apply as-is;
* `Rel` and `Relation`'s `Comp`/`ReflTransGen` are isomorphic formulations and can be
  converted either way;
* `Action σ` can be mapped through `rel` to `σ → Set σ`, connecting this library's
  `Preserves` to any `Set`-based verification tooling in Mathlib.

There is exactly one real risk: the library's own `Membership α (Nondet α)` instance
and Mathlib's `Set` instance could make `∈` ambiguous in the same environment. The
way out is to keep `Nondet` membership notation scoped, or to write `s a` directly.

---

## 9. Limits and roadmap

### 9.1 Specification layer vs execution layer

`Nondet` is `Prop`-valued and therefore **not computable**: this library cannot be
run directly. If execution is needed:

* write an executable `ActionM` over a `List`/`Multiset` monad and relate it to `rel`
  via `List.toSet` (soundness/completeness);
* or provide `Decidable` instances only for actions that are already deterministic.

### 9.2 Temporal logic and liveness

Implemented (`LeanAction/Liveness.lean`), in two layers:

* **temporal predicates**: `Behavior σ := Nat → σ`, `Always P b := ∀ n, P (b n)`,
  `Eventually P b := ∃ n, P (b n)`, `LeadsTo P Q b` (eventually, from any time), plus
  `IsBehavior` / `IsRun`. The bridge from safety to temporal logic is
  `always_of_safe`: `M.Safe P` plus a behavior starting in an initial state gives
  `Always P b`.
* **inevitability under fairness**: `TakesStep`, `WeakFair`, `StrongFair` (and
  `StrongFair.toWeakFair`), plus the rank arguments
  `eventually_zero_of_nat_progress_from` / `eventually_zero_of_weakFair(_inv)` /
  `leadsTo_zero_of_weakFair(_inv)`: if the progress action `A` strictly decreases
  `μ : σ → Nat` while the goal is unreached, no step increases `μ`, `A` is always
  enabled when `μ > 0`, and the behavior is weakly fair for `A`, then `μ` reaches
  zero (and "from any time" holds, so it can be packaged as `LeadsTo`). The `_inv`
  variants only require their hypotheses **inside an invariant region `I`**, and
  only while `μ > 0` — variants for shared-memory protocols are usually **not
  globally monotone** (leaving the critical section sends the variant back up), and
  this relaxation is a prerequisite for such proofs.
* **termination of loops**: `loop_can_exit` turns a decreasing variant into the
  "there exists a terminating run" half of termination for `while`; combined with
  `Hoare.loop` (partial correctness) this gives **total correctness** of a loop (see
  `countTo3_total` in `Examples/Liveness.lean`).

Liveness of a shared-memory protocol is instantiated in
`Examples/MutexLiveness.lean`: "if process 1 is in the region (waiting and holding
the turn) and `enter1` is weakly fair, it eventually enters the critical section",
and the complementary direction "inside the critical section, weak fairness for
`exit1` eventually takes it out" (the latter **consumes** safety: the stability of
the region comes from `Mutex.inv_step`). The approach is to pair the variant with a
hand-written region `Region`, rather than to hope for global monotonicity.

Liveness of an interleaving composes as well: `interleave_leadsTo` combines
"component eventually reaches `P`/`Q`" into "the product eventually reaches
`P ∧ Q`", where the components' `Preserves` supply **forward stability**
(`forward_stable_of_preserves`) and fairness is transferred from product to
component by `weakFair_fst_of_weakFair` / `weakFair_snd_of_weakFair`
(`Examples/ParallelLiveness.lean`).

Still missing: a fixpoint calculus and composition rules for `Always`/`Eventually`
(such as `Always (Eventually P)`), compassion / fairness invariants, and
**automatic synthesis of regions** — today both the region and the variant are given
by hand (the "stable until the goal" fact for `Region` has to be proved by prefix
induction, because it is not globally preserved).

### 9.3 Other

* **Lens derivation**: a `deriving` handler or a `lens!` macro (see §5.1).
* **Parallel semantics**: four layers exist — product state (`interleave`, §5.2),
  shared state with disjoint footprints (`ViewModule.parallel`),
  **rely/guarantee** (`Compatible` + `Preserves.orElse_of_compatible`, used when
  footprints overlap, as in `Examples/RelyGuarantee` and `Examples/MutexLiveness`),
  and **synchronous** (`ViewModule.sync`). Still missing: (a) **automatic discovery
  of relies** (today they are written by hand, usually after some trial and error);
  (b) **systematic support for non-state relies** (every rely here is a
  `σ → σ → Prop`; how to generate and validate a suitable rely from code has no
  methodology yet); (c) **liveness for synchronous composition** (only safety so
  far); (d) footprint inference only reaches the pointwise `cases`+`rfl` case
  (`disjoint_auto`); complex views still need hand-written proofs.
* **Invariant synthesis**: `inv` must be supplied by hand today; the shape of
  `Module.safe_of_invariant` is already suitable for hooking up IC3/Houdini-style
  invariant guessing.
* **The `grind` dependency**: `action_simp` falls back to Lean core's `grind`; where
  that is unsuitable, fall back to `omega`/`simp_all`/manual `rcases` (the examples
  keep that escape hatch open).

---

## 10. Verification

```bash
lake build      # Lean v4.33.0, zero dependencies, 25 jobs, no warnings
```

Examples that compile, and what they cover:

| Example | Coverage |
| --- | --- |
| `Examples/Basic` | `do` DSL, `<|>`, the invariant `n = log.length`, `safe_induct`, `while` + `rel_loop`, nested-field focus via `View.comp` |
| `Examples/Parallel` | `Module.interleave`, a sum invariant, `Refines` with stuttering |
| `Examples/Mutex` | shared-variable protocol (turn-based mutual exclusion): `guard` + six process steps, an invariant mixing both processes, `safe_induct`/`safe_of_invariant`, constructive reachability, `not_rel_guard_seq` to prove "blocked" |
| `Examples/Hoare` | partial correctness: `Hoare.iterate` (arithmetic post-condition), `Hoare.loop` (`while` + exit condition), `Hoare.nondet`, `Hoare.focusView` (focused triples) |
| `Examples/DataRefinement` | non-identity abstraction map, safety transfer along refinement, an implementation-only invariant (`count = log.length`), `Refines.reach` lifting concrete runs |
| `Examples/Machine` | stack machine with the program in the state: `choiceAll` dispatch, safety for **every** program (the code never grows), the concrete run `[push 2, push 3, add] → [5]` |
| `Examples/Liveness` | inevitability under fairness (a counter must reach 3), an explicit theorem that **liveness fails without fairness** (a stuttering behavior), the safety→`Always` bridge (including `Always`-form mutual exclusion), `while` termination and loop total correctness |
| `Examples/MutexLiveness` | liveness of the shared-memory protocol: a region-restricted (non-globally-monotone) variant, both "enter" and "leave" directions; the latter gets region stability from safety (the mutex invariant) |
| `Examples/ParallelLiveness` | liveness composition for interleaving: component liveness (projection + fairness transfer + sequence-level rank argument) into product liveness, with a counterexample showing the fairness hypothesis for the right component cannot be dropped |
| `Examples/Frame` | disjoint footprints on a shared record: the frame condition as a proof obligation, the frame theorem (each half proved on its own state type), composed liveness, synchronous composition (`sync`), and `¬ Disjoint` explaining why mutex is outside this layer |
| `Examples/RelyGuarantee` | composing **overlapping** footprints by interfaces: `Compatible` + `Preserves.orElse_of_compatible` (each component answers only to its own interface), `¬ Disjoint` showing why the frame layer cannot do it |

---

## 11. Exploring expressiveness and practicality through examples

This section is the record of what actually happened while writing the examples
(including the traps), measured against the expectations of §3–§7.

### 11.1 Library capabilities the examples forced into existence

| Gap | Addition |
| --- | --- |
| no way to state a `while` invariant | `Preserves.loop`, `loop_invariant` |
| partial correctness only covered `skip/seq/guard/nondet` | `Hoare.update`, `Hoare.set`, `Hoare.iterate`, `Hoare.loop` |
| "a failed guard makes this step unreachable" (proving a process blocked in the mutex) | `not_rel_guard_seq` |
| safety of an interleaving could not be composed | `interleave_init`, `reach_interleave_fst/snd`, `interleave_safe` |
| no notation for sequential composition (`seq A B` or `do`) | `;;` (`infixl:60`, over `seq`) |

The most valuable of these is `interleave_safe`: the **safety composition theorem
for interleaving** — `M.Safe P` and `N.Safe Q` imply
`(M.interleave N).Safe (P ∘ fst ∧ Q ∘ snd)`, and the proof only needs "reachability
descends through the two projections" (`reach_interleave_fst/snd`).

### 11.2 What felt natural

* **Protocol size is not a problem**: the mutex protocol's six-way nondeterministic
  step (including two `exit`s that rewrite the shared `turn`) goes through in one
  shot with `inv_induct; simp only [...]; action_simp; grind`, no manual `rcases`.
* **The three-stage invariant** (`init ⊆ I` → `Preserves next I` → `I ⊆ P`) matches
  real proof habits and `Module.safe_of_invariant` provides exactly that shape.
* **Constructive reachability**: a chain of `Reach.single`/`Reach.step` with one
  `action_simp` lemma per step proves both what *can* happen (`p1_can_enter`) and
  what *cannot* (`p2_blocked_…`).
* **Refinement and implementation details coexist**: the abstract layer uses
  `Refines.safe` for interface properties while the implementation proves
  log-length invariants invisible to the abstraction, with no interference.
* **Dispatch on a program stored in the state**: `choiceAll` +
  `guard (code.head? = some i)` removes the need for dependent pattern matching on
  the state; `Instr` stays an ordinary inductive type and dispatch goes through an
  existential witness.

### 11.3 Awkward spots, and the changes made

1. **`inv_induct` used to include `try grind`, silently proving the whole goal**;
   the user's following `simp only [...]`/`grind` then reported
   `No goals to be solved`, and the message pointed nowhere near the cause. It is
   now `inv_induct = unfold Preserves; intro …; action_simp` (no `grind`), so it is
   predictable; places that need `grind` say so explicitly.
2. **`apply L (P' := …)` is unreliable when the named implicit argument does not
   occur in the conclusion** (hit with `Hoare.focusView` and
   `Module.safe_of_invariant`). Use `refine L (…) ?_ ?_ ?_` or term mode; this is a
   consequence of `apply`'s goal-directed unification.
3. **Turning a `rel` hypothesis into a concrete equality cannot be done with
   `have`**: `rel (update f) s s'` and `s' = f s` are separated by
   `Done`/`Prod.mk.injEq`, so they are **not** defeq. One must first
   `simp only [f, Module.next, rel_update] at h` and only then treat it as an
   equality.
4. **A `match` binder in the state shadows same-named variables**:
   `match m.stack with | a::b::rest => … | s => …` introduces an `s` that makes a
   later `cases m.stack` unable to find `m`. Workarounds: catch the intermediate
   state in a same-named variable (`obtain ⟨m, ⟨-, rfl⟩, h⟩ := h`), or — more
   robustly — factor the per-instruction fact into its own lemma
   (`execInstr_code_shrinks`).
5. **`decide`/`native_decide` do not work on `rel` goals**: `Decidable (rel A s s')`
   cannot be synthesized, because `rel` is a function and instance search does not
   unfold it. Concrete computations use
   `simp only [...] <;> first | rfl | grind` instead.
6. **`grind`'s behaviour is environment-sensitive**: for the same goal in the machine
   example, having `deriving DecidableEq` or not changed the outcome;
   `code_never_grows` succeeded once and failed later on a similar goal, and only
   became stable after extracting the arithmetic into `execInstr_code_shrinks`.
   **Conclusion: do not bet a critical proof entirely on `grind`; extract the parts
   one can do by hand (arithmetic, list lengths) into lemmas.**
7. **Shared-variable parallelism is not what `interleave` is for**: the mutex `turn`
   is read and written by both processes, so "take the product of two independent
   modules" cannot express it; one has to write a global record plus an interleaving
   of process steps. This delimits `interleave`'s meaning: asynchronous composition
   of **independent components**; shared memory needs a frame/separation layer.
8. **Loop termination was still absent**: `Preserves.loop`/`Hoare.loop` only give
   partial correctness; liveness (fairness, `Eventually`) was out of scope (§9.2).

### 11.4 Extra lessons from the liveness layer

* **The core lemma cannot use `Nat.find`**: with `import Std` there is no
  `Nat.find/find_spec/min'`, nor `Nat.strong_induction_on`, nor `Nat.le_induction`.
  The zero-dependency constraint therefore turned the rank argument into
  **well-founded recursion on `Nat.strongRecOn`**: start from "rank > 0", use
  fairness to produce one strict decrease, and recurse on the smaller rank
  (`eventually_zero_of_nat_progress_from`). This is in fact shorter than "take the
  minimum of the sequence", and it does not need a least-element existence lemma.
* **`by_contra` is not in core** (it is Mathlib): the proof-by-contradiction style
  for liveness had to become `by_cases` + `absurd` (see
  `eventually_iff_not_always_not`).
* **Fairness has to be refuted once, explicitly**: `Examples/Liveness.stuck` gives a
  stuttering behavior of the very same module and proves that it is not weakly fair
  and never reaches the goal (`liveness_needs_fairness`). Writing "no fairness, no
  liveness" as a theorem is more convincing than asserting it in prose, and it
  prevents fairness from being treated as a technicality.
* **Total correctness = partial correctness + termination**: `Hoare.loop` (partial
  correctness) and `loop_can_exit` (a terminating run exists) assemble into
  `countTo3_total`; this assembly validates the interface between the proof layer
  and the liveness layer.
* **The quantifier order in `LeadsTo` matters**: the conclusion of
  `eventually_zero_of_weakFair` is first shaped as `∀ n, ∃ N ≥ n, …` and only then
  packaged as `LeadsTo`; otherwise one only gets the weak "starting at time 0" form.
* **State-based vs relation-based fairness**: here "taken" means
  `rel A (b n) (b (n+1))` (the step satisfies `A`'s relation), so for a module
  `A <|> B`, "`A` is always enabled but the environment always takes `B`" is exactly
  a violation of weak fairness — which is why `stuck` can be refuted.

### 11.5 Lessons from liveness of a shared-memory protocol

Pushing liveness to a shared-variable protocol like `Mutex` exposed three things:

1. **The variant is not globally monotone.**
   `rank s = if s.pc1 = 2 then 0 else 1` goes back from `0` to `1` on the
   "leave the critical section" step. The original rank argument demanded a global
   `μ s' ≤ μ s`, so it had to be relaxed to "only inside the invariant region `I`,
   only while `μ > 0`, and only then monotone/enabled"
   (`eventually_zero_of_weakFair_inv`). The relaxation is not cosmetic: `hI` is only
   needed while `μ > 0`, which corresponds exactly to "once the goal is reached it
   does not matter what happens next".
2. **The region is not globally preserved**, so `Preserves`/`always_of_preserves` do
   not apply: `Region ∨ pc1 = 2` is broken by `exit1` (`pc1` becomes `0`). What does
   hold is the **prefix form**: "as long as the critical section has not been
   entered, the state stays in the region", proved by induction over the behavior
   prefix (`region_until_goal`), where the "next step is not `pc1 = 2`" hypothesis
   rules out the `enter1` branch. This is also why `eventually_enter1` has to start
   with `by_cases (∃ N, pc1 = 2)`: if the goal is already reached, one is done;
   otherwise "`μ > 0` throughout" holds and hence the region does.
3. **Safety and liveness have different demands on the model.** The original `Mutex`
   example wrote `req1` (request the lock) as the unguarded
   `update (pc1 := 1)`: safety was unaffected (it does not touch `turn`), but a
   process inside the critical section could "re-request" and drop back to waiting,
   which destroys the stability of the region, so liveness could not be proved.
   Adding `guard (pc1 = 0)` made everything go through. **Conclusion: a model that is
   permissive enough for safety will betray you at liveness.**

The complementary direction `leadsTo_exit1` (leaving the critical section) is an
example of liveness **consuming** safety: the fact "in the critical section implies
holding the turn" comes from `Mutex.inv_step` + `always_of_preserves`, and without
it the other process's steps cannot be ruled out and the variant's monotonicity
cannot be established.

### 11.6 Generators: why a term macro fails and a command succeeds

Automatic generation of `Lens`/`View` took two detours before a command solved it:

* **Term macros failed twice** (`lens!`, `view!`). The field position in
  `{ s with f := v }` is a `Lean.Parser.Term.structInstLVal` syntax node, while a
  term macro's antiquotation can only produce an `ident`; forcing it into that
  position means **the macro definition type-checks** but the expansion is rejected
  at **every use site** with `unexpected syntax` — the failure point and the cause
  are separated, which makes it very easy to misdiagnose.
* **The command approach**: parse the getter/setter as strings
  (`Parser.runParserCategory env `term "fun s v => { s with f := v }"`), obtaining
  well-formed nodes, then `elabCommand` to emit the `def`. This worked first try.
* Two concrete traps were hit in the implementation, both now documented in the
  command's docstring:
  1. **a custom command cannot be preceded by a doc comment**: `/-- … -/` only
     attaches to declaration commands (`def`/`theorem`/`structure`…), so
     `/-- … -/ view_defs Foo` is a syntax error;
  2. **`elabCommand` prefixes declaration names with the current namespace**, so the
     generated name is relativized (`Name.replacePrefix currNs anonymous`); otherwise
     it lands at `Ns.Ns.Struct.fieldView`. If the structure is not inside the current
     namespace, the command fails outright.
  (Neither of these is a "documentation-type" note: both make users fail in
  mysterious ways, so they belong in the docstring.)
* **The `deriving` path** came afterwards and exposed three more metaprogramming
  details:
  1. the framework API is `Lean.Elab.registerDerivingHandler` (not
     `Lean.Elab.Deriving.*`), with
     `DerivingHandler := Array Name → CommandElabM Bool`; returning `true` means
     "handled", so **no** default instance is generated; and the registration name
     must be the **fully qualified** class name (`LeanAction.ViewFields`) — the short
     name simply does not match;
  2. `deriving X` requires `X` to resolve in the environment, hence a **marker class**
     (`class ViewFields (σ : Type u)`) — nobody uses it as a real type class, and the
     handler returns `true` to suppress instance generation;
  3. **`liftTermElabM (Term.elabType …)` inside a custom command cannot see section
     variables**, so the command cannot use `elabType` to extract the structure name
     (it logs "Unknown identifier α" while **still** creating the `def`, because
     `elabCommand` elaborates declarations — where section variables *are* visible).
     The fix is to read the structure name **purely syntactically**: find the
     leftmost identifier, try the candidates (as written / under the current
     namespace / with `_root_.` stripped), and skip `anonymous` identifier nodes.

### 11.7 Composing liveness over interleaving: projections stutter

Moving the idea of `interleave_safe` over to liveness revealed a structural
difference:

* **A projection is not a behavior of the component module.** Projecting a product
  behavior onto the first component makes the other component's steps appear as
  **stuttering** steps, whereas `IsBehavior M` requires every consecutive pair to be
  related by `M.next`. Hence the module-level rank theorems
  (`eventually_zero_of_weakFair*`) do not apply here, and the rank argument has to be
  pushed down to the **sequence level** (`eventually_zero_of_seq`, which needs only
  the pointwise facts "rank does not increase + fairness + the progress action is
  enabled"); the module-level versions then become corollaries.
* **Conjoining two "eventually"s needs stability.** Taking the later of "eventually
  `P`" and "eventually `Q`" yields `P ∧ Q` only if `P`/`Q` are **forward stable**
  along the behavior (`forward_stable_of_preserves`, from `Preserves`). This is the
  concrete form of "safety + liveness ⇒ conjunctive liveness", and it is exactly what
  the two `Preserves` hypotheses in `interleave_leadsTo` are for — in the examples
  they degenerate to the obvious monotonicity of the targets ("the counters only
  grow").
* **Fairness transfers along projections**: `weakFair_fst_of_weakFair` /
  `weakFair_snd_of_weakFair` need only the correspondence "component action enabled
  ↔ lifted action enabled" (i.e. the unfolding of
  `rel_liftLeft`/`rel_liftRight`), which is independent of stuttering.
* **A counterexample**: `leftOnly` (only the left component ever moves) is a
  legitimate behavior of the product and is even weakly fair for the left lifted
  action, yet it never reaches `p.1 ≥ 3 ∧ p.2 ≥ 4` — so the fairness hypothesis for
  the right component really cannot be dropped.

### 11.8 Making the frame condition explicit: lessons

* **`ViewModule` needs only `get_set`**, not the full lens laws: the frame theorem
  uses only "write into the view and read it back", so the footprint is weaker than a
  `Lens` (`View` + one law). That lowers the entry cost: users need not prove
  `set_get`/`set_set` to use the composition theorems. (I started with `Lens` as the
  footprint and later found it unnecessary.)
* **Do not add a `Lens → View` `Coe` instance**: when the target type is unknown,
  Lean **silently does not insert the coercion**, so `Disjoint M₁.view M₂.view`
  reports "`M₂.view` has type `Lens` but is expected to have type `View ?m`" — very
  hard to trace back to the root cause. Writing `View.ofLens` explicitly (or making
  the footprint type itself a `View`) is clean.
* **`parallel` is not syntactically commutative**: the `next` of `M₁ ∥ M₂` is
  `lift₁ <|> lift₂`, which is only *logically* equivalent to `lift₂ <|> lift₁`. So
  applying the same generic component-liveness lemma to the second component needs a
  small lemma `isBehavior_parallel_swap` (or a `Module`-level commutativity law).
  Wherever semantics are symmetric but syntax is not, instantiating a generic lemma
  costs one extra hand-off.
* **Lean's `rw` only matches syntactically**, and this layer hit the same trap twice:
  1. beta-redexes: the goal says `(fun s => P (v.get s)) s'`, so `rw [h]` cannot find
     `v.get s'` → open it with `change P (v.get s')` first;
  2. projections of structure constants: the generic lemma produces `C₁.view.get`
     while the goal already has `fp₁.get` → use
     `have h' : <equality with an explicit type> := h` (`have` goes through defeq,
     `rw` does not).
  In the end I wrote the example's liveness lemmas generically over `M.view` and
  instantiated them with `C₁`/`C₂`, which concentrated the second kind of friction in
  one place.
* **Stating the boundary as a theorem is most convincing**: `mutex_not_disjoint`
  turns "this protocol cannot be composed by the frame layer" from an assertion into
  a one-line counterexample — the same trick as `liveness_needs_fairness` from the
  previous round: **formalize the "cannot be done"**.

### 11.9 Rely/guarantee and synchronous composition: lessons

* **R/G only really pays off on prefix properties.** The original
  `region_until_goal` in `Examples/MutexLiveness` was "six-way `action_simp; grind`
  plus a hand-written prefix induction"; with R/G it becomes two one-sided interface
  lemmas (`region_steps1` is the component's own guarantee, `region_steps2` is the
  environment's rely, the latter never mentioning `steps1`) plus the library's
  `relyGuarantee_until` doing the induction. By contrast the mutex's **safety**
  (`inv_step`) is not shorter with R/G — see the next point.
* **For state invariants, R/G buys modularity, not brevity.** I tried to redo a
  "shared cell × two components" safety example and the conclusion was clear: if some
  component's **guard-free** step can break `I` from an `I`-state, no rely can rescue
  it — a rely constrains the **environment's transitions**, not the **current state**
  (this infeasibility argument is precisely what makes the composition rule sound). So
  the value of the safety example is that *obligations mention only interfaces*
  (in `Examples/RelyGuarantee` each direction looks only at the other component),
  not the proof length.
* **`sync` hit the same defeq trap again**: `rel`'s equality is `z = (Done.mk, x)`
  while one wants to say `s' = x`, and the two need `Prod.mk.injEq`, not defeq. That
  is the third time (`rel_focusView`, `rel_lift`, now `rel_sync`), and the fix is the
  same: `unfold rel` then `rintro` manually plus `congrArg Prod.snd`. **Conclusion:
  when writing a "relation unfolding" lemma for a new action, do not count on
  `Iff.rfl` by default — think through the `Done`/`Prod` layer first.**
* **`<|>` in a position whose expected type is `Prop` elaborates as
  `HOrElse Prop ...`**: `theorem next_eq : next = a <|> b <|> c := ...` reports
  "failed to synthesize HOrElse Prop (Action St)". Writing such equivalence lemmas at
  the `rel` level (`rel next s s' ↔ rel (a <|> b) s s'`) avoids it — and is closer to
  the semantics anyway. Incidentally, `Action.ext`-style "namespace prefix" notation
  does not work either (`Action` is a notation, not a namespace).
* **`sync` wants to be an `abbrev`, not a `def`**: under `def`, `Iff.rfl` cannot
  reduce `rel (M₁.sync M₂) s s'` to the unfolded form (the `Done` layer of `rel`
  blocks it); `abbrev` lets delta happen during definitional-equality checking, so
  `rel_sync` *can* be written with `Iff.rfl` … in practice even with `abbrev` one
  still needs the manual `Prod.snd` (previous point), but `abbrev` saves `unfold`
  elsewhere.

### 11.10 Conclusions

* On expressiveness: sequencing, nondeterminism (`<|>` / `nondet` / `choiceAll`),
  guards, loops, focusing (`focus`/`focusView`), refinement (with stuttering),
  interleaving and constructive reachability can all be expressed and proved under
  the same `rel` semantics; not one of the new examples needed to bypass the DSL and
  write `σ → Prop` directly.
* On practicality, the most effective proof recipe is:
  **`safe_induct`/`Module.safe_of_*` → `inv_induct` → `simp only [<your defs>] at *`
  → `action_simp` → `grind`** (switch to `omega`, or extract a lemma, when arithmetic
  or list reasoning is shaky).
* The main "automation risk" is not insufficient coverage but **being silently too
  strong** (`grind` finishing the whole goal unasked) and **environment sensitivity**
  (`deriving`, simp-set order). Both should keep being handled by the same
  trade-off: **predictability over power**.
