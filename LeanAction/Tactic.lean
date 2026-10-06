/-
LeanAction.Tactic
=================

Automation for inductive safety proofs.

The design is deliberately small and predictable:

* `action_simp` rewrites with the *semantics* of every action combinator
  (`rel_skip`, `rel_seq`, `rel_orElse`, …), turning any composite action into a
  first-order statement about states. There is no search here, only unfolding.
* `step` = `action_simp; try grind`: discharges a one-step obligation.
* `inv_induct` proves a `Preserves A I` goal by the canonical skeleton
  (`unfold Preserves; intro s hs s' hstep; step`).
* `safe_induct` proves `M.Safe P` by `Module.safe_of_preserves`, leaving exactly
  the two first-order obligations `M.init ⊆ P` and `Preserves M.next P`.

Because the semantics lemmas are `@[simp]`, plain `simp`/`simp_all` and `grind`
also see them; the macros only fix the *shape* of the proof, not the reasoning.
Users usually finish with

```
safe_induct <;> simp only [myModule, myInv, myAction1, myAction2] at * <;> grind
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
               and_true, true_implies, and_imp] at *)

/-- Discharge a one-step obligation: unfold the action semantics, then `grind`. -/
macro "action_step" : tactic => `(tactic| (action_simp; try grind))

/-- Discharge a one-step obligation: unfold the action semantics, then `grind`. -/
macro "step" : tactic => `(tactic| (action_simp; try grind))

/-- The canonical skeleton for a one-step invariant (`Preserves A I`). -/
macro "inv_induct" : tactic =>
  `(tactic| (unfold Preserves; intro s hs s' hstep; step))

/-- Prove `M.Safe P` from a one-step invariant. Leaves two goals:
`M.init ⊆ P` and `Preserves M.next P`, both first-order after `action_simp`. -/
macro "safe_induct" : tactic =>
  `(tactic| apply Module.safe_of_preserves)

/-- Prove `M.Safe P` using an auxiliary invariant `I`: produces the goals
`M.init ⊆ I`, `Preserves M.next I` and `I ⊆ P`. -/
macro "safe_induct" "using" I:term : tactic =>
  `(tactic| apply Module.safe_of_invariant (I := $I))

end LeanAction
