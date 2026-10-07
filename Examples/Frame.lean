/-
Examples.Frame
==============

Shared-state composition through **disjoint footprints** (the frame assumption
made explicit).

* The state is one record holding both components (`Two`), not a product: the
  footprint of each component is a *view* into it.
* `Disjoint fp₁ fp₂` is a proof obligation, discharged by `disjoint_auto`
  (which finds the deriver's certificate, falling back to `cases s; rfl`).
* Nested and indexed footprints follow the same pattern: base disjointness
  composes (`Disjoint.comp_of_disjoint`/`comp_left`), and the array-like case
  needs a side condition, which is what `DisjointUnder` is for.
* `ViewModule.parallel_safe` then gives the composed safety property, where each
  half is proved **only** about the component's own state (`n = log.length`) —
  no global case analysis over the interleavings.
* Liveness composes the same way, and the mutex processes are proved *not*
  disjoint, which is why that protocol still needs a hand-written invariant.
-/
import LeanAction
import LeanAction.Derive
import Examples.Mutex

open LeanAction

namespace Examples.Frame

/-! ## A shared record with two footprints -/

/-- Shared state: two counters, each with its own audit log. -/
structure Two where
  n₁ : Nat
  n₂ : Nat
  l₁ : List Nat
  l₂ : List Nat

/-- Footprint of the first component: its counter and its log. -/
def fp₁ : View Two (Nat × List Nat) :=
  ⟨fun s => (s.n₁, s.l₁), fun s v => { s with n₁ := v.1, l₁ := v.2 }⟩

/-- Footprint of the second component. -/
def fp₂ : View Two (Nat × List Nat) :=
  ⟨fun s => (s.n₂, s.l₂), fun s v => { s with n₂ := v.1, l₂ := v.2 }⟩

/-- **The frame assumption**, as a proof obligation: the two footprints do not
interfere. -/
theorem disjoint_fp : Disjoint fp₁ fp₂ := by disjoint_auto

/-! ## The components, each described on its own state type -/

/-- Increment and log the previous value. -/
def step : Action (Nat × List Nat) := do
  let s ← (ActionM.get : ActionM (Nat × List Nat) (Nat × List Nat))
  ActionM.modify fun t => (t.1 + 1, s.1 :: t.2)

def C₁ : ViewModule Two (Nat × List Nat) where
  view := fp₁
  get_set := by intro s a; cases s; cases a; rfl
  init := fun s => s.n₁ = 0 ∧ s.l₁ = []
  next := step

def C₂ : ViewModule Two (Nat × List Nat) where
  view := fp₂
  get_set := by intro s a; cases s; cases a; rfl
  init := fun s => s.n₂ = 0 ∧ s.l₂ = []
  next := step

/-- The component's own invariant — proved on `Nat × List Nat` only. -/
theorem inv_step : Preserves step (fun t : Nat × List Nat => t.1 = t.2.length) := by
  inv_induct
  simp only [step] at *
  action_simp
  grind

theorem init_fp₁ : ∀ s, C₁.init s → (fun t : Nat × List Nat => t.1 = t.2.length) (C₁.view.get s) := by
  rintro s ⟨h1, h2⟩
  show s.n₁ = s.l₁.length
  simp [h1, h2]

theorem init_fp₂ : ∀ s, C₂.init s → (fun t : Nat × List Nat => t.1 = t.2.length) (C₂.view.get s) := by
  rintro s ⟨h1, h2⟩
  show s.n₂ = s.l₂.length
  simp [h1, h2]

/-- **The frame theorem in action.** The composed system satisfies both component
invariants, although each half was proved only about one component's state. -/
theorem two_safe : (C₁.parallel C₂).Safe
    (fun s : Two => s.n₁ = s.l₁.length ∧ s.n₂ = s.l₂.length) := by
  have h := ViewModule.parallel_safe (M₁ := C₁) (M₂ := C₂) disjoint_fp
    init_fp₁ init_fp₂ inv_step inv_step
  show (C₁.parallel C₂).Safe (fun s : Two => s.n₁ = s.l₁.length ∧ s.n₂ = s.l₂.length)
  exact h

/-! ## Liveness through the same frame

Targets: the first counter reaches 3, the second reaches 4. The rank lives on the
*component* state; the projection stutters when the other component moves, which
is exactly what `ViewModule.proj_step` and the sequence-level rank theorem
(`eventually_zero_of_seq`) handle. -/

def μ (k : Nat) (t : Nat × List Nat) : Nat := k - t.1

theorem step_increments {t t' : Nat × List Nat} (h : rel step t t') : t'.1 = t.1 + 1 := by
  simp only [step] at h
  action_simp
  grind

theorem step_enabled (t : Nat × List Nat) : ∃ q, rel step t q :=
  ⟨(t.1 + 1, t.1 :: t.2), by simp only [step]; action_simp; grind⟩

/-- Liveness of one component of the composition, at target `k`: it only uses the
component's *own* increment/enabledness facts and fairness for its lifted action,
plus disjointness to know that the other component's steps stutter. -/
theorem component_live (k : Nat) {M M' : ViewModule Two (Nat × List Nat)}
    (hd : Disjoint M.view M'.view) (hbeh : IsBehavior (M.parallel M') b)
    (hinc : ∀ t t', rel M.next t t' → t'.1 = t.1 + 1)
    (hen : ∀ t, ∃ q, rel M.next t q)
    (hfair : WeakFair (focusView M.view M.next) b) :
    LeadsTo (fun _ : Nat × List Nat => True) (fun t => t.1 ≥ k) (fun n => M.view.get (b n)) := by
  intro n _
  have hwf : WeakFair M.next (fun n => M.view.get (b n)) :=
    ViewModule.weakFair_of_lift M.get_set hfair
  have hdec : ∀ m, μ k (M.view.get (b m)) > 0 →
      μ k (M.view.get (b (m + 1))) ≤ μ k (M.view.get (b m)) := by
    intro m _
    rcases ViewModule.proj_step hd hbeh m with hstut | hstep
    · have h' : M.view.get (b (m + 1)) = M.view.get (b m) := hstut
      rw [h']
      exact Nat.le_refl _
    · simp only [μ]
      rw [hinc _ _ hstep]
      omega
  have hA : ∀ m, μ k (M.view.get (b m)) > 0 →
      rel M.next (M.view.get (b m)) (M.view.get (b (m + 1))) →
      μ k (M.view.get (b (m + 1))) < μ k (M.view.get (b m)) := by
    intro m hpos hstep
    simp only [μ] at hpos ⊢
    rw [hinc _ _ hstep]
    omega
  have henabled : ∀ m, μ k (M.view.get (b m)) > 0 → ∃ q, rel M.next (M.view.get (b m)) q :=
    fun m _ => hen _
  obtain ⟨N, hN, hz⟩ := eventually_zero_of_seq (A := M.next)
    (I := fun _ : Nat × List Nat => True) (μ := μ k) (b := fun n => M.view.get (b n))
    (fun _ _ => trivial) (fun m _ h => hdec m h) (fun m _ hpos h => hA m hpos h)
    (fun m _ hpos => henabled m hpos) hwf n
  have hz' : k - (M.view.get (b N)).1 = 0 := hz
  refine ⟨N, hN, ?_⟩
  show (M.view.get (b N)).1 ≥ k
  omega

theorem ge_preserves (k : Nat) : Preserves step (fun t : Nat × List Nat => t.1 ≥ k) := by
  inv_induct
  simp only [step] at *
  action_simp
  grind

/-- **Composed liveness on the shared state**, with each component's liveness
proved on its own projection. -/
theorem two_live (b : Behavior Two) (hbeh : IsBehavior (C₁.parallel C₂) b)
    (hf₁ : WeakFair (focusView C₁.view step) b) (hf₂ : WeakFair (focusView C₂.view step) b) :
    LeadsTo (fun _ : Two => True) (fun s => s.n₁ ≥ 3 ∧ s.n₂ ≥ 4) b := by
  have h := ViewModule.parallel_leadsTo (M₁ := C₁) (M₂ := C₂) disjoint_fp hbeh
    (ge_preserves 3) (ge_preserves 4)
    (component_live 3 (M := C₁) (M' := C₂) disjoint_fp hbeh
      (fun _ _ h => step_increments h) (fun _ => step_enabled _) hf₁)
    (component_live 4 (M := C₂) (M' := C₁) disjoint_fp.symm
      (ViewModule.isBehavior_parallel_swap hbeh)
      (fun _ _ h => step_increments h) (fun _ => step_enabled _) hf₂)
  show LeadsTo (fun _ : Two => True) (fun s : Two => s.n₁ ≥ 3 ∧ s.n₂ ≥ 4) b
  exact h

/-! ## Stepping together (synchronous composition)

`ViewModule.sync` runs both components in lock-step. `Disjoint.set_set` is what
makes the two updates order-independent, and — unlike the interleaving — a
simultaneous step advances *both* projections. -/

theorem sync_advances_both (s s' : Two) (h : rel (C₁.sync C₂) s s') :
    s'.n₁ = s.n₁ + 1 ∧ s'.n₂ = s.n₂ + 1 := by
  obtain ⟨a', b', ha', h₁, hb', h₂⟩ := ViewModule.sync_proj disjoint_fp h
  have h₁' : s'.n₁ = a'.1 := by simpa [C₁, fp₁] using congrArg Prod.fst h₁
  have h₂' : s'.n₂ = b'.1 := by simpa [C₂, fp₂] using congrArg Prod.fst h₂
  refine ⟨?_, ?_⟩
  · rw [h₁', step_increments ha']
    rfl
  · rw [h₂', step_increments hb']
    rfl

theorem two_sync_safe : (C₁.syncModule C₂).Safe
    (fun s : Two => s.n₁ = s.l₁.length ∧ s.n₂ = s.l₂.length) := by
  have h := ViewModule.syncModule_safe (M₁ := C₁) (M₂ := C₂) disjoint_fp
    init_fp₁ init_fp₂ inv_step inv_step
  show (C₁.syncModule C₂).Safe (fun s : Two => s.n₁ = s.l₁.length ∧ s.n₂ = s.l₂.length)
  exact h

/-! ### Liveness of the lock-step composition

Unlike the interleaving, `sync`'s step relation *is* the joint relation, so no
projection/stutter argument is needed: `leadsTo_of_rank_region` applies with
`T := C₁.sync C₂` directly. -/

/-- Distance to the joint target `(n₁ ≥ 3, n₂ ≥ 4)`. -/
def syncRank (s : Two) : Nat := (3 - s.n₁) + (4 - s.n₂)

/-- The joint step is enabled everywhere (`step` always is). -/
theorem sync_enabled (s : Two) : Enabled (C₁.sync C₂) s := by
  obtain ⟨a', ha'⟩ := step_enabled (C₁.view.get s)
  obtain ⟨b', hb'⟩ := step_enabled (C₂.view.get s)
  exact ⟨C₂.view.set (C₁.view.set s a') b',
    ViewModule.rel_sync.mpr ⟨a', b', ha', hb', rfl⟩⟩

/-- **Liveness of the lock-step composition.** Weak fairness of the joint step
drives both counters to their targets. This closes the "liveness for synchronous
composition" roadmap item with an example rather than a new rule. -/
theorem two_sync_live (b : Behavior Two) (hbeh : IsBehavior (C₁.syncModule C₂) b)
    (hfair : WeakFair (C₁.sync C₂) b) :
    LeadsTo (fun _ : Two => True) (fun s => s.n₁ ≥ 3 ∧ s.n₂ ≥ 4) b :=
  leadsTo_of_rank_region (T := C₁.sync C₂) (A := C₁.sync C₂) (r := (· < ·))
    Nat.lt_wfRel.wf (fun _ _ _ => Nat.lt_trans)
    (P := fun _ => True) (Q := fun s => s.n₁ ≥ 3 ∧ s.n₂ ≥ 4)
    (I := fun _ => True) (μ := syncRank) hbeh hfair
    (by intro s s' _ _ _; simp only [true_and]; omega)
    (by intro s _ _; trivial)
    (by
      intro s s' _ _ h
      obtain ⟨h1, h2⟩ := sync_advances_both s s' h
      simp only [syncRank]; omega)
    (by
      intro s _ hq s' h
      have hpos : syncRank s > 0 := by simp only [syncRank]; omega
      obtain ⟨h1, h2⟩ := sync_advances_both s s' h
      simp only [syncRank] at hpos ⊢; omega)
    (by intro s _ _; exact sync_enabled s)

/-! ## Nested footprints compose

Disjointness of nested views is built from the base case plus the lens laws
(`Disjoint.comp_of_disjoint`), not from another `cases; rfl` over the whole
record. `Inner2`/`Outer2` get their views, lenses and pairwise `Disjoint`
certificates straight from `deriving ViewFields, LensFields`. -/

structure Inner2 where
  x : Nat
  y : Nat
  deriving ViewFields, LensFields

structure Outer2 where
  inner : Inner2
  z : Nat
  deriving ViewFields, LensFields

/-- The base fact: the deriver emitted the certificate `Inner2.disjoint_x_y`,
and `disjoint_auto` only had to look it up by name. -/
theorem Inner2.x_y : Disjoint Inner2.xView Inner2.yView := by disjoint_auto

/-- `x` and `y` seen through `Outer2.inner`, from the *derived* views/lenses. -/
def Outer2.xNested : View Outer2 Nat := View.ofLens Outer2.innerLens ∘ᵥ Inner2.xView

def Outer2.yNested : View Outer2 Nat := View.ofLens Outer2.innerLens ∘ᵥ Inner2.yView

/-- Nested disjointness **by composition** — no `cases` on `Outer2`. -/
theorem Outer2.xNested_yNested : Disjoint Outer2.xNested Outer2.yNested :=
  Inner2.x_y.comp_of_disjoint Outer2.innerLens

/-- Mixed: a nested view against a sibling field, by `comp_left`. The certificate
`Outer2.disjoint_inner_z` is about `Outer2.innerView`, which is definitionally
`View.ofLens Outer2.innerLens`. -/
theorem Outer2.xNested_z : Disjoint Outer2.xNested Outer2.zView :=
  Outer2.disjoint_inner_z.comp_left Inner2.xView

/-! ## Indexed footprints: function update

An array-like footprint reads/writes one entry. With a *variable* index `upd`
does not reduce, so the pointwise channel of `disjoint_auto` is out — instead
`upd_noteq` / `upd_comm` supply the commutation, with an explicit `i ≠ j`. -/

structure Table where
  arr : Fin 10 → Nat
  epoch : Nat

/-- The footprint of one table entry: read/write index `i`. -/
def entryView (i : Fin 10) : View Table Nat where
  get := fun s => s.arr i
  set := fun s v => { s with arr := upd s.arr i v }

/-- The footprint of the epoch field. -/
def epochView : View Table Nat where
  get := fun s => s.epoch
  set := fun s v => { s with epoch := v }

/-- Two distinct entries are disjoint — **conditional** on `i ≠ j` (the `upd`
commutation lemmas are what make it work). -/
theorem entry_disjoint {i j : Fin 10} (h : i ≠ j) :
    Disjoint (entryView i) (entryView j) where
  get_set s a := by cases s; simp only [entryView, upd_noteq (Ne.symm h)]
  set_get s b := by cases s; simp only [entryView, upd_noteq h]
  set_set s a b := by cases s; simp only [entryView]; rw [upd_comm (Ne.symm h)]

/-- Entry vs. epoch: unconditional, and the *semantic* channel of
`disjoint_auto` closes it (no certificate exists for a manual view). -/
theorem entry_epoch_disjoint (i : Fin 10) : Disjoint (entryView i) epochView := by
  disjoint_auto

/-! ## Conditional footprints: `DisjointUnder`

`entry_disjoint` needs the side condition `i ≠ j` because `upd` does not reduce
at a variable index. `DisjointUnder P v₁ v₂` is exactly that conditional frame:
the three commutation laws only have to hold at `P`-states. It is simultaneously
the footprint frame, the rely special case and the temporal shadow of a
region. -/

/-- Two fixed entries: the conditional form degenerates to the unconditional
one (`toUnder`). -/
theorem entry_disjointUnder {i j : Fin 10} (h : i ≠ j) :
    DisjointUnder (fun _ : Table => i ≠ j) (entryView i) (entryView j) :=
  (entry_disjoint h).toUnder _

/-- A table whose two write targets are *pointers into the array*: whether the
two views interfere is a state predicate — aliasing freedom. -/
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

/-- **The** demo: a conditional frame with a state-dependent condition. While
`aliasFree` holds, writes through the two pointers commute. This is not
expressible as a plain `Disjoint` — under aliasing the two views are literally
the same slot. -/
theorem ptrView_disjointUnder :
    DisjointUnder aliasFree (ptrView fun s => s.ptr₁) (ptrView fun s => s.ptr₂) where
  get_set s a h := by cases s; simp only [ptrView, upd_noteq (Ne.symm h)]
  set_get s b h := by cases s; simp only [ptrView, upd_noteq h]
  set_set s a b h _ := by cases s; simp only [ptrView]; rw [upd_comm (Ne.symm h)]

/-- The footprint reading: an environment write through `ptr₂` leaves the
`ptr₁`-slot untouched (while `aliasFree` holds). -/
theorem ptr₁_get_eq_of_write (s : PtrTable) (v : Nat) (h : aliasFree s) :
    (ptrView fun t => t.ptr₁).get ((ptrView fun t => t.ptr₂).set s v) =
      (ptrView fun t => t.ptr₁).get s := by
  apply ptrView_disjointUnder.get_eq_of_write h
  simp only [ptrView, upd_same]

/-- A component that only writes its own pointer's slot preserves `aliasFree`. -/
theorem ptr₁_preserves_aliasFree :
    Preserves (focusView (ptrView fun s => s.ptr₁) (update (· + 1))) aliasFree := by
  intro s hs s' hr
  obtain ⟨a', -, hs'⟩ := rel_focusView.mp hr
  rw [hs']
  simpa [aliasFree, ptrView] using hs

theorem ptr₂_preserves_aliasFree :
    Preserves (focusView (ptrView fun s => s.ptr₂) (update (· + 1))) aliasFree := by
  intro s hs s' hr
  obtain ⟨a', -, hs'⟩ := rel_focusView.mp hr
  rw [hs']
  simpa [aliasFree, ptrView] using hs

/-- **The combined system is safe.** The interleaving of the two slot-writers
preserves aliasing freedom (plus the trivial component invariants);
`parallel_preserves_under` is the step from the two single-step frame lemmas to
the system theorem. -/
theorem ptr_safe_under :
    Preserves (focusView (ptrView fun s => s.ptr₁) (update (· + 1)) <|>
                focusView (ptrView fun s => s.ptr₂) (update (· + 1)))
      aliasFree := by
  have h := parallel_preserves_under (P := aliasFree) ptrView_disjointUnder
    (update (· + 1)) (update (· + 1))
    (by intro s a; simp only [ptrView, upd_same])
    (by intro s a; simp only [ptrView, upd_same])
    ptr₁_preserves_aliasFree ptr₂_preserves_aliasFree
    (P₁ := fun _ : Nat => True) (P₂ := fun _ : Nat => True)
    (by intro s _ s' _; trivial) (by intro s _ s' _; trivial)
  simpa using h

/-! ## Where the frame assumption fails: the mutex protocol

Both processes of `Examples.Mutex` write `turn`, so no disjointness proof exists,
and the hand-written global invariant (with `action_simp; grind` over the six
process steps) is genuinely necessary there. -/

/-- Footprint of mutex process 1: its program counter and the shared turn. -/
def mutexP₁ : View Mutex.St (Nat × Nat) :=
  ⟨fun s => (s.pc1, s.turn), fun s v => { s with pc1 := v.1, turn := v.2 }⟩

/-- Footprint of mutex process 2: it also writes the shared turn. -/
def mutexP₂ : View Mutex.St (Nat × Nat) :=
  ⟨fun s => (s.pc2, s.turn), fun s v => { s with pc2 := v.1, turn := v.2 }⟩

theorem mutex_not_disjoint : ¬ Disjoint mutexP₁ mutexP₂ := by
  intro h
  have hh := h.set_set (⟨0, 0, 1⟩ : Mutex.St) (⟨1, 1⟩ : Nat × Nat) (⟨1, 2⟩ : Nat × Nat)
  have : (1 : Nat) = 2 := by
    simpa [mutexP₁, mutexP₂] using congrArg Mutex.St.turn hh
  omega

end Examples.Frame
