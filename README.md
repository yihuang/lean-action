# LeanAction

A small Lean 4 library for **expressing actions (state-transition relations)** and
**automating inductive invariant proofs**.

![CI](https://github.com/yihuang/lean-action/actions/workflows/ci.yml/badge.svg)

* **Two views of the same thing**: a nondeterministic state monad written with
  `do`-notation, and the plain relational semantics given by `rel`; the two are
  inter-convertible.
* **Modularity**: `View`/`Lens` + `focus` to zoom into nested structure fields, and
  four ways of composing components in parallel — product state (`interleave`),
  shared state with **disjoint footprints** (`ViewModule.parallel`, where the frame
  condition `Disjoint` is a proof obligation and comes with a frame theorem),
  **rely/guarantee** (interface-based composition when footprints overlap), and
  **synchronous / lock-step** composition (`ViewModule.sync`).
* **Proof layer**: `Reach`, `Preserves`, `Hoare`, `Module`, `Refines`, built on a
  **single induction engine**.
* **Temporal layer**: `Always` / `Eventually` / `LeadsTo`, behaviors, weak/strong
  fairness, rank arguments (inevitability under fairness, with variants that only
  have to hold inside an invariant region), **composition of liveness over
  interleaving** (`interleave_leadsTo`), and termination of `while` loops
  (`loop_can_exit`). There are worked examples for shared-memory protocols and for
  parallel systems.
* **Metaprogramming**: `deriving ViewFields, LensFields` (recommended) or the
  `view_defs` / `lens_defs` commands generate `View`s / `Lens`es for structure
  fields (`import LeanAction.Derive`; use the commands for parameterized
  structures).
* **Automation**: `action_simp` / `step` / `inv_induct` / `safe_induct`, finished
  off by `grind`.
* **No external dependencies** (Mathlib is not needed), Lean `v4.33.0`.

Design and trade-offs: [`DESIGN.md`](DESIGN.md).

---

## Quick start

```lean
import LeanAction
open LeanAction

structure Ctr where
  n : Nat
  log : List Nat

/-- `do` DSL: read the state, bump the counter, log the old value -/
def incr : Action Ctr := do
  let s ← (ActionM.get : ActionM Ctr Ctr)
  ActionM.modify fun t => { t with n := t.n + 1, log := s.n :: t.log }

def reset : Action Ctr := set { n := 0, log := [] }

def init : Nondet Ctr := fun s => s.n = 0 ∧ s.log = []
def inv  : Nondet Ctr := fun s => s.n = s.log.length
def M    : Module Ctr := ⟨init, incr <|> reset⟩

/-- One step preserves the invariant -/
theorem inv_step : Preserves (incr <|> reset) inv := by
  inv_induct
  simp only [inv, incr, reset] at *
  action_simp
  grind

/-- Safety: every reachable state satisfies `inv` -/
theorem safe : M.Safe inv := by
  safe_induct
  · intro s hs
    unfold M at hs
    simp only [init, inv] at hs ⊢
    grind
  · inv_induct
    simp only [M, inv, incr, reset] at *
    action_simp
    grind
```

The automation pattern is always the same: **first `simp only` the user's own
`def`s (the library cannot guess them), then `action_simp` to unfold the action
semantics into a first-order statement, then `grind` (or `omega`) to finish**.

Complete, compiling examples live in `Examples/`:

| File | Contents |
| --- | --- |
| `Examples/Basic.lean` | `do` DSL, `<|>`, `while` loops, nested-field focus via `View.comp`, and the deriver's pairwise `Disjoint` certificates closed by `disjoint_auto` |
| `Examples/Parallel.lean` | `Module.interleave`, refinement (`Refines`) with stuttering |
| `Examples/Mutex.lean` | shared-variable protocol: mutual exclusion from six process steps, constructive reachability, a proof that a process is blocked |
| `Examples/Hoare.lean` | partial correctness: `iterate`, `while` (`Hoare.loop`), `nondet`, `focusView` |
| `Examples/DataRefinement.lean` | non-identity abstraction map, safety transfer, implementation-only invariant, run lifting |
| `Examples/Machine.lean` | stack machine with the program in the state: dispatch by `choiceAll`, safety for *every* program, a concrete run |
| `Examples/Liveness.lean` | inevitability under fairness, a theorem that **liveness fails without fairness**, `Always`-form mutual exclusion, loop termination and total correctness |
| `Examples/MutexLiveness.lean` | liveness of the shared-memory protocol: a region-restricted (not globally monotone) variant, both "enter" and "leave" directions, the latter using safety for region stability; the enter direction is proved twice (rank argument and the rank-free `leadsTo_of_wf1`) |
| `Examples/ParallelLiveness.lean` | liveness of an interleaving: projection + fairness transfer + sequence-level rank argument ⇒ product liveness; a counterexample shows the fairness hypothesis is needed |
| `Examples/Frame.lean` | disjoint footprints on a shared record: frame theorem (each half proved on its own state type), composed liveness, synchronous composition, nested/indexed footprints (`Disjoint.comp_of_disjoint`, `upd` + an `i ≠ j` side condition), conditional disjointness (`DisjointUnder` and aliasing freedom), and `¬ Disjoint` explaining why the mutex protocol is outside this layer |
| `Examples/RelyGuarantee.lean` | overlapping footprints composed by interfaces: each component answers only to its own rely/guarantee, plus the rely-as-output shortcut (`derivedRely`/`preserves_of_guarantees`) that needs no explicit `Rel` |

```bash
lake build          # library + examples + LeanActionTests (Lean v4.33.0)
```

---

## API at a glance

### Types

| Name | Meaning |
| --- | --- |
| `Nondet α` | `α → Prop`, a `Prop`-valued nondeterminism monad (`Monad` + `Alternative`) |
| `ActionM σ α` | state transitions returning `α`: `σ → Nondet (α × σ)` |
| `Action σ` | plain state transitions, notation for `ActionM σ Done` |
| `Rel α β` | `α → β → Prop` (`Rel.Comp` / `Rel.TransGen` / `Rel.ReflTransGen`) |
| `View σ α` / `Lens σ α` | field selection (no laws / with the three lens laws) |
| `Module σ` | `{ init : Nondet σ, next : Action σ }` |

### Actions

`skip` `fail` `guard P` `assert P` `assume P` `update f` `set v` `nondet R`
`choiceAll B`, plus the combinators `A ;; B` (`seq`), `A <|> B` (`Alternative`),
`A >>= f`, `iterate A n`, `while[P] A` (`loop P A`), `liftLeft`/`liftRight`,
`focus`/`focusView`.

### Proof layer

| Name | Meaning |
| --- | --- |
| `rel A s s'` | the transition relation of an action |
| `Reach A s s'` | reflexive-transitive closure of `rel A` |
| `Preserves A I` | one-step preservation of an invariant |
| `Hoare P A Q` | partial-correctness triple |
| `Module.Safe M P` | every reachable state satisfies `P` |
| `Refines f Abs Conc` | data refinement (stuttering allowed) |
| `Always P b` / `Eventually P b` / `LeadsTo P Q b` | temporal predicates ("always / eventually / once…then eventually…"), `b : Behavior σ := Nat → σ` |
| `IsBehavior M b` / `IsRun M b` | `b` is a behavior of `M` / a behavior starting in an initial state |
| `WeakFair A b` / `StrongFair A b` | weak / strong fairness for the action `A` |
| `leadsTo_zero_of_weakFair(_inv)` | rank argument: inevitability under fairness (`_inv` only requires its hypotheses inside an invariant region) |
| `loop_can_exit` | a `while` loop has a terminating run (with `Hoare.loop`: total correctness) |
| `eventually_zero_of_strongFair_inv` | the strong-fairness version of the rank argument (`StrongFair ⟹ WeakFair`) |
| `eventually_zero_of_seq` | sequence-level rank argument (stuttering allowed — needed for projected behaviors) |
| `interleave_leadsTo` | liveness composition for interleaving (with `forward_stable_of_preserves`, `weakFair_fst/snd_of_weakFair`) |
| `deriving ViewFields, LensFields` | generates `Struct.fView` / `Struct.fLens` per field (absolute names, works inside namespaces) |
| `view_defs` / `lens_defs` | generate `View` / `Lens` with the type given as a term (the path for parameterized structures) |
| `Preserves.loop` / `Hoare.loop` | loop invariance / partial correctness |
| `Module.interleave` + `interleave_safe` | interleaving on product states and its safety composition theorem |
| `Disjoint` + `ViewModule.parallel_safe/parallel_leadsTo` | composition on **disjoint footprints** of a shared state (frame condition made explicit, with a frame theorem) |
| `Compatible` + `Preserves.orElse_of_compatible` | **rely/guarantee** composition when footprints overlap (obligations mention only interfaces) |
| `relyGuarantee_until` | prefix stability ("a region holds until the goal is reached"), the temporal twin of rely/guarantee |
| `ViewModule.sync` / `sync_preserves` / `sync_proj` | synchronous (lock-step) composition and its theorems |
| `disjoint_auto` | closes `Disjoint` goals for structure-field views |

### Automation

| Macro | Purpose |
| --- | --- |
| `action_simp` | unfold action semantics (`rel_*` lemma set, `at *`) |
| `step` | `action_simp; try grind`, one step obligation |
| `inv_induct` | the canonical skeleton for `Preserves A I` |
| `safe_induct` / `safe_induct using I` | prove `M.Safe P` (optionally with an auxiliary invariant) |

---

## Repository layout

```
LeanAction/Rel.lean      relation toolkit (Comp / TransGen / ReflTransGen + induction)
LeanAction/Nondet.lean   Prop-valued nondeterminism monad
LeanAction/Action.lean   the DSL: ActionM / Action / primitives / combinators / rel lemmas
LeanAction/Lens.lean     View / Lens / focus / product lifts / interleave
LeanAction/Proof.lean    Reach / Preserves / Hoare / Module / Refines
LeanAction/Tactic.lean   action_simp / step / inv_induct / safe_induct
LeanAction/Derive.lean   view_defs / lens_defs commands (needs `import Lean`)
LeanAction/Liveness.lean Always / Eventually / LeadsTo, behaviors, fairness, rank arguments
LeanAction/Frame.lean    shared-state composition: Disjoint, frame theorem, ViewModule.parallel
Examples/                compiling examples (the API in use)
Tests/                   LeanActionTests: compile-time regression tests for the library
DESIGN.md                design document (semantics, automation, limits, roadmap)
```

The `Tests/` modules are the project's unit tests. They are proofs, so
*compiling them is running them*: `lake build` fails if any lemma that used to
hold stops holding. They are deliberately thin — each one records a small
obligation that a library change once broke (the two-channel `disjoint_auto`,
`DisjointUnder`, WF1, `derivedRely`, …) and consume only the public API.

## Examples as experiments

The files in `Examples/` are not just API demos: they are the record of what
happened when the design met real proofs. The library pieces they forced into
existence (`Preserves.loop`, `Hoare.iterate/loop/nondet/update/set`,
`not_rel_guard_seq`, `interleave_safe`, `;;`, the rely/guarantee rules, `sync`)
and the traps that were hit (`apply` with named implicit arguments, turning `rel`
into an equality with `have`, `match` binders shadowing the state variable,
`decide` being unusable on `rel`, the environment sensitivity of `grind`, shared
variables being outside `interleave`, …) are written up in
[§11 of `DESIGN.md`](DESIGN.md#11-exploring-expressiveness-and-practicality-through-examples).

## Known limits

* `Nondet` is `Prop`-valued and therefore **not computable**: this library is a
  specification/proof layer. Executing would need a separate `List`/`Multiset`
  monad (`DESIGN.md` §9.1).
* The temporal layer has **rank arguments** (`Always`/`Eventually`/`LeadsTo` + weak/
  strong fairness + `while` termination + region-restricted variants for
  shared-memory protocols) **and a rank-free WF1 rule** (`leadsTo_of_wf1`, at an
  arbitrary step relation, with a non-stuttering `⟨A⟩` variant), plus basic
  `LeadsTo` algebra. There is no fixpoint calculus and no compassion, and
  invariant regions still have to be supplied by hand (`DESIGN.md` §9.2, §11.4,
  §11.5).
* Parallelism has four composition modes (interleaving over product or shared
  state, rely/guarantee, synchronous). For the safety fragment the rely is now
  *derived* (`derivedRely`/`preserves_of_guarantees`), so it need not be written
  by hand; an explicit `Rel` remains only for value-constraint interfaces, and
  there is no *liveness* rely/guarantee rule. Footprint inference covers flat
  structures (deriver certificates) and composes (`Disjoint.comp_of_disjoint`),
  with the array-like case handled conditionally (`DisjointUnder`); arbitrary
  hand-written views still need hand-written proofs. Also missing: liveness for
  synchronous composition (`DESIGN.md` §5.4, §9.3).
* Field `View`s/`Lens`es can be generated by `deriving ViewFields, LensFields`
  (recommended, absolute names); for parameterized structures use the
  `view_defs`/`lens_defs` commands (note: no doc comment may precede a custom
  command, and the structure must live in the current namespace) — `DESIGN.md`
  §5.1, §11.6.
