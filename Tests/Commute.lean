/-
Tests.Commute
===========

Regression tests for the compositional `Disjoint` theorems and the
function-update footprint lemmas, now in `LeanAction.Frame`
(`Disjoint.comp_of_disjoint` / `comp_left` / `comp_right`, `upd` etc.).

Tests:
* nested views compose from base cases instead of one big pointwise proof;
* the boundary of the syntactic fragment is function-update (array-like)
  views: `Disjoint` there needs a side condition (`i ≠ j`) and the
  update-commutation lemmas — `disjoint_auto` cannot see it, because `upd`
  with a *variable* index does not reduce.
-/

import LeanAction
import Std

open LeanAction

namespace Tests.Commute

universe u

variable {σ α β γ : Type u}

/-! ## Nested structures: composition at work -/

structure Inner where
  x : Nat
  y : Nat

structure Outer where
  inner : Inner
  z : Nat

def Inner.xLens : Lens Inner Nat where
  get := fun s => s.x
  set := fun s v => { s with x := v }
  get_set := by intro s a; rfl
  set_get := by intro s; cases s; rfl
  set_set := by intro s a b; cases s; rfl

def Inner.yLens : Lens Inner Nat where
  get := fun s => s.y
  set := fun s v => { s with y := v }
  get_set := by intro s a; rfl
  set_get := by intro s; cases s; rfl
  set_set := by intro s a b; cases s; rfl

def Outer.innerLens : Lens Outer Inner where
  get := fun s => s.inner
  set := fun s v => { s with inner := v }
  get_set := by intro s a; rfl
  set_get := by intro s; cases s; rfl
  set_set := by intro s a b; cases s; rfl

def Outer.zLens : Lens Outer Nat where
  get := fun s => s.z
  set := fun s v => { s with z := v }
  get_set := by intro s a; rfl
  set_get := by intro s; cases s; rfl
  set_set := by intro s a b; cases s; rfl

/-- Base fact: the two fields of `Inner` are disjoint.

NOTE: `disjoint_auto` provably fails here — its `try cases a` splits the
`Nat`-valued set into `zero`/`succ` branches and the `succ` branch does not
close by `rfl` (see the build log of this test). For `Nat`-valued
views, `cases s; rfl` without casing the value works. (For pair-valued
views, as in `Examples/Frame`, `cases` on the value splits the pair one
level and everything stays reducible.) -/
theorem Inner.xy_disjoint : Disjoint (View.ofLens Inner.xLens) (View.ofLens Inner.yLens) where
  get_set s a := by cases s; rfl
  set_get s b := by cases s; rfl
  set_set s a b := by cases s; rfl

/-- Base fact: the two fields of `Outer` are disjoint. Same story: one field
is `Nat`-valued, so `disjoint_auto`'s `cases a` on it gets stuck. -/
theorem Outer.inner_z_disjoint :
    Disjoint (View.ofLens Outer.innerLens) (View.ofLens Outer.zLens) where
  get_set s a := by cases s; rfl
  set_get s b := by cases s; rfl
  set_set s a b := by cases s; rfl

/-- Nested view: `x` seen through `Outer.inner`. -/
def Outer.xView : View Outer Nat := View.ofLens (Outer.innerLens ∘ₗ Inner.xLens)

/-- Nested view: `y` seen through `Outer.inner`. -/
def Outer.yView : View Outer Nat := View.ofLens (Outer.innerLens ∘ₗ Inner.yLens)

/-- Nested disjointness, proved **by composition** — no `cases` on `Outer`. -/
theorem Outer.xy_disjoint_nested : Disjoint Outer.xView Outer.yView :=
  Inner.xy_disjoint.comp_of_disjoint Outer.innerLens

/-- Mixed: a nested view against a sibling field, by `comp_left`. -/
theorem Outer.x_z_disjoint : Disjoint Outer.xView (View.ofLens Outer.zLens) :=
  Outer.inner_z_disjoint.comp_left (View.ofLens Inner.xLens)

/-! ## The boundary: function-update (array-like) views -/

/-- A state with an indexed table. -/
structure Table where
  arr : Fin 10 → Nat
  epoch : Nat

/-- The footprint of one table entry: read/write index `i` of the table. -/
def entryView (i : Fin 10) : View Table Nat where
  get := fun s => s.arr i
  set := fun s v => { s with arr := upd s.arr i v }

/-- The footprint of the epoch field. -/
def epochView : View Table Nat where
  get := fun s => s.epoch
  set := fun s v => { s with epoch := v }

/-- Disjointness of two *distinct* table entries: **conditional** on `i ≠ j`.
This is where `disjoint_auto` (`cases; rfl`) provably stops working — the
`if j = i` in `upd` cannot reduce with both indices abstract, so the
commutation needs `upd_noteq`/`upd_comm` instead. -/
theorem entry_disjoint {i j : Fin 10} (h : i ≠ j) : Disjoint (entryView i) (entryView j) where
  get_set s a := by
    cases s
    simp only [entryView, upd_noteq (Ne.symm h)]
  set_get s b := by
    cases s
    simp only [entryView, upd_noteq h]
  set_set s a b := by
    cases s
    simp only [entryView]
    rw [upd_comm (Ne.symm h)]

/-- Entry vs. epoch: the same shape of argument, one index at a time. -/
theorem entry_epoch_disjoint (i : Fin 10) : Disjoint (entryView i) epochView where
  get_set _ _ := rfl
  set_get _ _ := rfl
  set_set _ _ _ := rfl

end Tests.Commute
