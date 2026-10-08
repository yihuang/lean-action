/-
Tests.DisjointUnder
=================

Regression tests for `DisjointUnder` (now in `LeanAction.Frame`) —
conditional disjointness, with a state-dependent condition.

Tests:
* constant conditions reduce to plain `Disjoint` (`toUnder`);
* the aliasing-freedom demo: two pointer-directed views into the same array
  commute *while* the pointers do not alias — not expressible as a plain
  `Disjoint`, since under aliasing the two views are literally the same slot.
-/

import LeanAction
import Std
import Tests.Commute

open LeanAction

namespace Tests.DisjointUnder

open Tests.Commute

/-! ## Constant conditions reduce to plain `Disjoint` -/

/-- Two fixed table entries: the conditional form degenerates to the
unconditional one. -/
theorem entry_disjoint_under {i j : Fin 10} (h : i ≠ j) :
    DisjointUnder (fun _ : Table => i ≠ j) (entryView i) (entryView j) :=
  (entry_disjoint h).toUnder _

/-! ## State-dependent conditions: aliasing freedom -/

/-- A table whose two write targets are *pointers into the array*: whether
the two views interfere is now a state predicate — aliasing freedom. -/
structure PtrTable where
  arr : Fin 10 → Nat
  ptr₁ : Fin 10
  ptr₂ : Fin 10

/-- The view of "the slot pointed to by `getPtr`". -/
def ptrView (getPtr : PtrTable → Fin 10) : View PtrTable Nat where
  get := fun s => s.arr (getPtr s)
  set := fun s v => { s with arr := upd s.arr (getPtr s) v }

/-- The aliasing-freedom invariant. -/
def aliasFree : Nondet PtrTable := fun s => s.ptr₁ ≠ s.ptr₂

/-- **The** demo: conditional frame with a state-dependent condition. While
`aliasFree` holds, writes through `ptr₁` and `ptr₂` commute. This fact is
not expressible as a plain `Disjoint` — under aliasing (`ptr₁ = ptr₂`) the
two views are literally the same slot. -/
theorem ptrView_disjointUnder :
    DisjointUnder aliasFree (ptrView fun s => s.ptr₁) (ptrView fun s => s.ptr₂) where
  get_set s a h := by
    cases s
    simp only [ptrView, upd_noteq (Ne.symm h)]
  set_get s b h := by
    cases s
    simp only [ptrView, upd_noteq h]
  set_set s a b h _ := by
    cases s
    simp only [ptrView]
    rw [upd_comm (Ne.symm h)]

end Tests.DisjointUnder
