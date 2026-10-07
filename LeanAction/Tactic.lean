/-
LeanAction.Tactic
=================

Automation for inductive safety proofs.

The design is deliberately small and predictable:

* `action_simp` rewrites with the *semantics* of every action combinator
  (`rel_skip`, `rel_seq`, `rel_orElse`, …), turning any composite action into a
  first-order statement about states. There is no search here, only unfolding and
  normalization; the normalization half is what keeps the result usable at scale:
  * the `∃ t, (P s ∧ t = s) ∧ Q t` shape produced by `rel_seq` +
    `rel_guard`/`rel_update` is collapsed to `P s ∧ Q t`
    (`exists_and_left`/`exists_eq_left`/`exists_eq`/`and_assoc`), and
    `∃ a, B₁ a ∨ B₂ a` is pushed out (`exists_or`) so that a disjunction of
    *concrete* branches remains — this is what lets `grind` case-split the
    witness of `choiceAll`/`<|>` instead of the caller writing `rcases`;
  * the array-update helper `upd` is unfolded at the *function* level by
    `upd_fun` (see below).
* `step` = `action_simp; try grind`: discharges a one-step obligation.
* `inv_induct` proves a `Preserves A I` goal by the canonical skeleton
  (`unfold Preserves; intro s hs s' hstep; action_simp`).
* `safe_induct` proves `M.Safe P` by `Module.safe_of_preserves`, leaving exactly
  the two first-order obligations `M.init ⊆ P` and `Preserves M.next P`.

Two boundaries are deliberate:

* `action_simp` does **not** unfold the users' own `def`s (that would be
  unguessable, and is where a `Def` can be a state predicate rather than an
  action); the caller still writes `simp only [myModule, myAction, …]` first. In
  particular a named update helper such as `setPc s i v := { s with pc := upd … }`
  is opaque to `action_simp`; either list it in that `simp only`, or write the
  update inline so that the library primitive `upd` is what remains. (Making the
  helpers ambient would need a persisted registry consulted by `action_simp` —
  the mechanism `@[field_disjoint]`/`disjoint_auto` already demonstrates; this
  package has no custom `simp`-set registry to hang it on, because it is
  Std-only.)
* `upd` is a `def` whose `eq_def` is stated on the *fully applied* form
  (`upd f i v j`), so it does not rewrite the bare function value that appears
  inside `{ s with pc := upd s.pc i v }`. The function-level `upd_fun` (in
  `LeanAction/Lens.lean`) is what `action_simp` uses instead.

Because the semantics lemmas are `@[simp]`, plain `simp`/`simp_all` and `grind`
also see them; the macros only fix the *shape* of the proof, not the reasoning.
Users usually finish with

```
safe_induct <;> simp only [myModule, myInv, myAction1, myAction2] at * <;> action_simp <;> grind
```
-/
import Std
import LeanAction.Action
import LeanAction.Lens
import LeanAction.Proof

universe u

namespace LeanAction

/-- Unfold the semantics of actions everywhere: any `rel (composite action) s s'`
becomes a first-order `Prop` over states. -/
macro "action_simp" : tactic =>
  `(tactic|
    simp (config := { failIfUnchanged := false }) only [rel_skip, rel_fail, rel_failure, rel_guard, rel_assert, rel_assume,
               rel_update, rel_set, rel_modify, rel_write, rel_nondet, rel_choice,
               rel_orElse, rel_seq, rel_bind_action, rel_bind, rel_choiceAll,
               rel_iterate_zero, rel_iterate_succ, rel_focus, rel_focusView,
               rel_liftLeft, rel_liftRight,
               ActionM.get_apply, ActionM.read_apply, ActionM.pure_apply,
               ActionM.bind_apply, ActionM.map_apply, ActionM.orElse_apply,
               ActionM.failure_apply, ActionM.modify_apply, ActionM.write_apply,
               Done.eq_iff_true, Prod.mk.injEq, exists_prop, exists_and_left, true_and,
               and_true, true_implies, and_imp,
               -- collapse the `∃ t, (P s ∧ t = s) ∧ Q t` shape that `rel_seq` +
               -- `rel_guard`/`rel_update` produce into `P s ∧ Q s`, pushing
               -- disjunctions out (`choiceAll`/`<|>` witnesses): this is what
               -- keeps `action_simp` goals first-order without an `obtain`.
               and_assoc, exists_or, exists_eq_left, exists_eq,
               -- array-like fields: `upd.eq_def` only matches `upd f i v j`, so
               -- the function-level `upd_fun` is needed for the bare value
               -- inside `{ s with pc := upd s.pc i v }`.
               upd_fun] at *)

/-- Discharge a one-step obligation: unfold the action semantics, then `grind`. -/
macro "action_step" : tactic => `(tactic| (action_simp; try grind))

/-- Discharge a one-step obligation: unfold the action semantics, then `grind`. -/
macro "step" : tactic => `(tactic| (action_simp; try grind))

/-- The canonical skeleton for a one-step invariant (`Preserves A I`):
introduce the binders and unfold the action semantics. Deliberately *does not*
call `grind`: it leaves a first-order goal for the caller, so a following
`simp only [...]`/`grind` line always has something to do. -/
macro "inv_induct" : tactic =>
  `(tactic| (unfold Preserves; intro s hs s' hstep; action_simp))

/-- Prove `M.Safe P` from a one-step invariant. Leaves two goals:
`M.init ⊆ P` and `Preserves M.next P`, both first-order after `action_simp`. -/
macro "safe_induct" : tactic =>
  `(tactic| apply Module.safe_of_preserves)

/-- Prove `M.Safe P` using an auxiliary invariant `I`: produces the goals
`M.init ⊆ I`, `Preserves M.next I` and `I ⊆ P`. -/
macro "safe_induct" "using" I:term : tactic =>
  `(tactic| apply Module.safe_of_invariant (I := $I))

end LeanAction
