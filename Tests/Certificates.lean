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
  fixes the old failure on `Nat`-valued manual views (Test 4).

Every test below failed with the previous single-channel `disjoint_auto`.
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

end Tests.Certificates
