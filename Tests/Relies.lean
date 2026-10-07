/-
Tests.Relies
==========

Test: where can a rely candidate come from, and what does it cost to
check? Two shapes emerge on the two existing examples:

* **Frame-relies** (footprints mostly disjoint): the rely says "the partner
  preserves the fields it does not write". For mutex node `i`, a step of node
  `j ≠ i` writes only `pc j` and `turn`, so the candidate rely is "`pcView i` is
  preserved". That is now a **certificate channel** — the `PreservesView`
  analogue of `field_disjoint`: a theorem tagged `@[rely_cert]`, looked up by
  `rely_auto` by the head pair `(action, view)`, with the per-index side
  condition (`i ≠ j`) left as the certificate's business.
* **Constraint-relies** (footprints fully overlap, as in
  `Examples/RelyGuarantee`): the rely is a value constraint (`v` does not
  increase) that cannot be derived from write sets — it is user knowledge.
  Automation can only *check*, never *guess*, this shape.

So "automatic discovery of relies" means: derive the frame part mechanically
(`rely_defs`, below), leave the constraint part to the user, and fail loudly when
a guard-free partner step breaks the invariant (the §11.9 infeasibility case).
-/
import LeanAction
import Examples.Mutex
import Examples.MutexLiveness

open LeanAction

namespace Tests.Relies

open Examples.Mutex (Pc St M next req enter exit steps setPc pcView)
open Examples.MutexLiveness (Region others)

/-! ## Frame-relies: certificates for non-written views -/

/-- A step of node `j ≠ i` writes only `pc j` and `turn`, hence it leaves the
view `pcView i` unchanged. This is the certificate shape: `rely_auto` looks it up
by the head pair `(steps, pcView)` and discharges the `i ≠ j` side condition from
the context. -/
@[rely_cert] theorem steps_preserves_pcView {n : Nat} {i j : Fin n} (h : i ≠ j) :
    PreservesView (steps j) (pcView i) := by
  intro s s' hstep
  simp only [steps, req, enter, exit, pcView] at hstep ⊢
  action_simp
  grind

/-- The same fact in the raw-projection form the old test used, read off the
certificate (no proof search). -/
theorem steps_preserves_other_pc {n : Nat} {i j : Fin n} (h : i ≠ j) {s s' : St n}
    (hstep : rel (steps j) s s') : s'.pc i = s.pc i :=
  steps_preserves_pcView h s s' hstep

/-- The candidate frame-rely for node `i`, as a relation. -/
def R_frame {n : Nat} (i : Fin n) : Rel (St n) (St n) :=
  fun s s' => (pcView i).get s' = (pcView i).get s

/-- Checking a single node step `j ≠ i` against `R_frame i` is now a certificate
lookup: `rely_auto` finds `steps_preserves_pcView` from `(steps, pcView)` and
closes the side condition from context. -/
theorem steps_respects_frame_rely {n : Nat} {i j : Fin n} (h : i ≠ j) {s s' : St n}
    (hstep : rel (steps j) s s') : R_frame i s s' := by
  simp only [R_frame]
  rely_auto

/-! ## Deriving frame certificates (`rely_defs`)

For the monomorphic `view_defs`/`deriving ViewFields` fragment, `rely_defs` emits
and registers the certificates itself from the **footprint metadata** (which
field each action writes): the generated lemma shape is the same
`PreservesView` statement as `steps_preserves_pcView` above, and `rely_auto` then
finds it by the head pair. -/

/-- Two independent counters; `bumpA` writes only `a`. -/
structure Pair where
  a : Nat
  b : Nat
  deriving ViewFields

/-- Writes `a` only. -/
def bumpA : Action Pair := update (fun s => { s with a := s.a + 1 })

/-- Writes `b` only. -/
def bumpB : Action Pair := update (fun s => { s with b := s.b + 1 })

-- `bumpA` writes `a` (so it preserves `bView`), `bumpB` writes `b` (so it
-- preserves `aView`). NB: a custom command cannot follow a doc comment
-- (DESIGN §11.6), hence the `/--`-free comment here.
rely_defs Pair [bumpA, bumpB] writes [[a], [b]]

/-- The generated certificate is found by `rely_auto` from `(bumpA, bView)`. -/
example {s s' : Pair} (h : rel bumpA s s') : Pair.bView.get s' = Pair.bView.get s := by
  rely_auto

/-! ## What the frame-rely buys in the region proof -/

/-- The environment's obligation in `relyGuarantee_until` for the region.
The `pc i` conjunct of `Region i` is preserved by the *certified* frame lemma
(`rely_auto`); the rest is what genuinely needs the protocol argument
(`region_steps_others`). The proof splits exactly along the "derivable vs. user
knowledge" line. -/
theorem region_env_via_frame {n : Nat} {i j : Fin n} (h : j ≠ i) {s s' : St n}
    (hs : Region i s) (hstep : rel (steps j) s s') : Region i s' := by
  have hne : i ≠ j := Ne.symm h
  have hp : (pcView i).get s' = (pcView i).get s := by rely_auto
  exact Examples.MutexLiveness.region_steps_others i hs (by
    simp only [others, rel_choiceAll]
    exact ⟨⟨j, h⟩, hstep⟩)

/-! ## The constraint-rely shape (from Examples/RelyGuarantee) -/

/- For comparison: in the Cell example the two components have the *same*
footprint, so no frame-rely exists (`not_disjoint_self`). The rely there is
`R₂ s s' := s'.v ≤ s.v` — a value constraint about *how much* the partner
may change, which no write-set analysis can derive. The honest automation
boundary: generate and check frame-relies; ask the user for constraint-relies;
and prove `¬ Disjoint` (as the library already does) to justify the upgrade
from the frame layer to R/G. -/

end Tests.Relies
