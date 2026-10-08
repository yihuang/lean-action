/-
Tests.Certificates
================

Regression tests for the two-channel `disjoint_auto`:

* certificate channel — per-field-pair `T.disjoint_f_g` theorems emitted
  by `deriving ViewFields` (Test 1–2) and by the `view_defs` command for
  parameterized structures (Test 3–4, implicit and explicit parameters),
  found by naming-convention lookup on
  the goal's view heads (with `Disjoint.symm` for the reversed order);
* semantic fallback — `cases; rfl` *without* casing the values first, which
  fixes the old failure on `Nat`-valued manual views (Test 5).

Every test below failed with the previous single-channel `disjoint_auto`.

Tests 7–10 cover the channel's *exception* paths, which the fallback used to
mask (see DESIGN §11.9): a registered certificate with a side condition
(transactional apply), a reversed goal that needs `Disjoint.symm` on an
`upd`-indexed view the fallback cannot close, the `LensFields`
naming-convention lookup (asserted on the trace, because there the fallback
does close), and a parameterized `lens_defs` structure.
-/
import LeanAction
import LeanAction.Derive

open LeanAction

namespace Tests.Certificates

/-! ## Test 1–2: certificate channel on a derived structure -/

structure Reg where
  n : Nat
  flag : Bool
  deriving ViewFields

/-- `Nat`-valued field: the old `disjoint_auto` split `a : Nat` into
`zero`/`succ` and got stuck; the certificate closes it directly. -/
theorem reg_disjoint : Disjoint Reg.nView Reg.flagView := by
  disjoint_auto

/-- The symmetric goal resolves through `Disjoint.symm` over the same
certificate. -/
theorem reg_disjoint_symm : Disjoint Reg.flagView Reg.nView := by
  disjoint_auto

/-! ## Test 3: parameterized structure via the `view_defs` command -/

section

variable {α : Type}

structure Box (α : Type) where
  payload : α
  stamp : Nat

-- The generated certificate `Box.disjoint_payload_stamp` is stated with the
-- parameter `α` tied to the section variable through a type ascription on the
-- view references. Without it the header cannot solve the implicit `α` and the
-- declaration is rejected.
view_defs (Box α)

theorem box_disjoint :
    Disjoint (Box.payloadView : View (Box α) _) (Box.stampView : View (Box α) _) := by
  disjoint_auto

end

/-! ## Test 4: explicit structure parameters

With `variable (γ : Type)` the generated views take `γ` as an *explicit*
argument, so the certificate must apply them (`Box2.aView γ`) rather than rely
on the type ascription alone. -/

section

variable (γ : Type)

structure Box2 (γ : Type) where
  a : γ
  b : Nat

view_defs (Box2 γ)

theorem box2_disjoint : Disjoint (Box2.aView γ) (Box2.bView γ) := by
  disjoint_auto

end

/-! ## Test 5: semantic fallback, `Nat`-valued manual views -/

structure Two where
  x : Nat
  y : Nat

def xView : View Two Nat := ⟨fun s => s.x, fun s v => { s with x := v }⟩
def yView : View Two Nat := ⟨fun s => s.y, fun s v => { s with y := v }⟩

/-- No certificate exists (manual views); the fallback must close this
*without* casing the `Nat` values — the old tactic got stuck here. -/
theorem two_disjoint : Disjoint xView yView := by
  disjoint_auto

/-! ## Test 6: explicit `@[field_disjoint]` registration

A hand-written certificate whose name is *not* `T.disjoint_f_g` is found through
the registry, not the naming convention. -/

structure Manual where
  p : Nat
  q : Bool

def Manual.pView : View Manual Nat := ⟨fun s => s.p, fun s v => { s with p := v }⟩
def Manual.qView : View Manual Bool := ⟨fun s => s.q, fun s v => { s with q := v }⟩

@[field_disjoint] theorem manual_cert : Disjoint Manual.pView Manual.qView :=
  ⟨by intro s a; cases s; rfl, by intro s b; cases s; rfl, by intro s a b; cases s; rfl⟩

theorem manual_disjoint : Disjoint Manual.pView Manual.qView := by
  disjoint_auto

/-! ## Test 7: a registered certificate with a side condition

The certificate carries a premise (`i ≠ j`), so `disjoint_auto` must *commit* the
applied certificate and leave the premise as a subgoal. The `upd`-indexed views
make the semantic fallback fail (`set_set` needs `upd_comm`), so the certificate
channel is genuinely the only way through. -/

structure Arr where
  arr : Fin 2 → Nat

def arrView (i : Fin 2) : View Arr Nat :=
  ⟨fun s => s.arr i, fun s v => { s with arr := upd s.arr i v }⟩

@[field_disjoint] theorem arrView_disjoint {i j : Fin 2} (h : i ≠ j) :
    Disjoint (arrView i) (arrView j) where
  get_set s a := by simp [arrView, upd_noteq (Ne.symm h)]
  set_get s b := by simp [arrView, upd_noteq h]
  set_set s a b := by simp [arrView]; exact upd_comm (Ne.symm h) s.arr b a

/-- The certificate applies and leaves `i ≠ j`, closed by `assumption`. Before
the transactional fix the assigned goal fell through to the fallback (which
cannot close `upd`-disjointness) and errored. -/
theorem arrView_disjoint_fwd {i j : Fin 2} (h : i ≠ j) :
    Disjoint (arrView i) (arrView j) := by
  disjoint_auto <;> assumption

/-! ## Test 8: reversed goal uses `Disjoint.symm`

Two *distinct* registered views and a reversed goal: the forward application does
not unify, so only the `Disjoint.symm` script can find the certificate — and the
fallback cannot close the `upd`-disjointness. -/

def arrView0 : View Arr Nat := ⟨fun s => s.arr 0, fun s v => { s with arr := upd s.arr 0 v }⟩
def arrView1 : View Arr Nat := ⟨fun s => s.arr 1, fun s v => { s with arr := upd s.arr 1 v }⟩

@[field_disjoint] theorem arrView01_disjoint : Disjoint arrView0 arrView1 where
  get_set s a := by simp [arrView0, arrView1, upd_noteq (by decide : (1 : Fin 2) ≠ 0)]
  set_get s b := by simp [arrView0, arrView1, upd_noteq (by decide : (0 : Fin 2) ≠ 1)]
  set_set s a b := by
    simp [arrView0, arrView1]
    exact upd_comm (by decide : (1 : Fin 2) ≠ 0) s.arr b a

theorem arrView01_disjoint_symm : Disjoint arrView1 arrView0 := by
  disjoint_auto

/-! ## Test 9: `LensFields`-only structure, naming-convention certificate

The generated `LSt.disjoint_x_y` is stated over `View.ofLens LSt.xLens`, so the
lookup has to unwrap `View.ofLens` down to the lens constant — otherwise the
naming-convention channel is dead and the goal is silently closed by the
semantic fallback. Assert on the trace so the fallback cannot mask it. -/

structure LSt where
  x : Nat
  y : Bool
  deriving LensFields

/--
trace: [LeanAction.disjoint_auto] certificate Tests.Certificates.LSt.disjoint_x_y applied
-/
#guard_msgs in
set_option trace.LeanAction.disjoint_auto true in
example : Disjoint (View.ofLens LSt.xLens) (View.ofLens LSt.yLens) := by
  disjoint_auto

/- Reversed, so this also exercises the `Disjoint.symm` script on the unwrapped
lens key. -/
/--
trace: [LeanAction.disjoint_auto] certificate Tests.Certificates.LSt.disjoint_x_y applied
-/
#guard_msgs in
set_option trace.LeanAction.disjoint_auto true in
example : Disjoint (View.ofLens LSt.yLens) (View.ofLens LSt.xLens) := by
  disjoint_auto

/-! ## Test 10: parameterized `LensFields`-only structure

With `variable (δ : Type)` the generated lens takes `δ` explicitly, so the
certificate must apply it (`LBox.payloadLens δ`) under `View.ofLens`. The
certificate is *generated*, so a missing application makes `lens_defs` itself
fail to elaborate. -/

section

variable (δ : Type)

structure LBox (δ : Type) where
  payload : δ
  stamp : Nat

lens_defs (LBox δ)

theorem lbox_disjoint :
    Disjoint (View.ofLens (LBox.payloadLens δ)) (View.ofLens (LBox.stampLens δ)) := by
  disjoint_auto

end

end Tests.Certificates
