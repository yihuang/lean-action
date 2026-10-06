/-
Examples.Mutex
==============

A shared-memory two-process protocol on a single state record: turn-based
mutual exclusion. This is the example that stresses the parts of the library
that `Examples/Parallel.lean` does not:

* a *shared* variable (`turn`) read and written by both processes — so the
  system is one `Module` over one record, not an `interleave` of two modules;
* per-process actions built from `guard` + update;
* a non-trivial inductive invariant that mixes both processes;
* a constructive reachability proof (what *can* happen) next to the safety
  proof (what *cannot* happen).
-/
import LeanAction

open LeanAction

namespace Examples.Mutex

/-- `pc1`/`pc2` are 0 = out, 1 = waiting, 2 = in the critical section;
`turn` says whose turn it is to enter (1 or 2). -/
structure St where
  pc1 : Nat
  pc2 : Nat
  turn : Nat

/-- Process 1 asks for the lock. Note the guard: without it a process could
"re-request" from inside the critical section, which is harmless for safety (the
turn is not touched) but breaks liveness reasoning, where the region
`pc1 = 1` must be stable. -/
def req1 : Action St := guard (fun s => s.pc1 = 0) ;; update fun s => { s with pc1 := 1 }

/-- Process 1 enters the critical section when it holds the turn. -/
def enter1 : Action St :=
  guard (fun s => s.pc1 = 1 ∧ s.turn = 1) ;; update (fun s => { s with pc1 := 2 })

/-- Process 1 leaves the critical section and hands the turn to process 2. -/
def exit1 : Action St :=
  guard (fun s => s.pc1 = 2) ;; update (fun s => { s with pc1 := 0, turn := 2 })

def req2 : Action St := guard (fun s => s.pc2 = 0) ;; update fun s => { s with pc2 := 1 }

def enter2 : Action St :=
  guard (fun s => s.pc2 = 1 ∧ s.turn = 2) ;; update (fun s => { s with pc2 := 2 })

def exit2 : Action St :=
  guard (fun s => s.pc2 = 2) ;; update (fun s => { s with pc2 := 0, turn := 1 })

/-- One step is any of the six process steps. -/
def next : Action St := req1 <|> enter1 <|> exit1 <|> req2 <|> enter2 <|> exit2

def init : Nondet St := fun s => s.pc1 = 0 ∧ s.pc2 = 0 ∧ (s.turn = 1 ∨ s.turn = 2)

/-- The invariant: whoever is in the critical section holds the turn. -/
def inv : Nondet St := fun s => (s.pc1 = 2 → s.turn = 1) ∧ (s.pc2 = 2 → s.turn = 2)

def M : Module St := ⟨init, next⟩

/-- The invariant is inductive. The `action_simp` + `grind` pair has to look at
all six steps, including the two `exit` steps that *change* `turn`. -/
theorem inv_step : Preserves next inv := by
  inv_induct
  simp only [next, req1, enter1, exit1, req2, enter2, exit2, inv] at *
  action_simp
  grind

theorem inv_init : init ⊆ₙ inv := by
  intro s hs
  simp only [init, inv] at hs ⊢
  grind

/-- Mutual exclusion: the two processes are never in the critical section
together. -/
theorem mutex_safe : M.Safe (fun s => ¬ (s.pc1 = 2 ∧ s.pc2 = 2)) :=
  Module.safe_of_invariant (M := M) (I := inv)
    (fun s hs => inv_init s hs)
    (by simpa only [M] using inv_step)
    (fun s hs => by simp only [inv] at hs; grind)

/-! ## Constructive reachability: what *can* happen -/

/-- From the initial state with the turn held by process 1, process 1 can reach
the critical section while process 2 waits. -/
theorem p1_can_enter :
    Reach M.next ⟨0, 0, 1⟩ ⟨2, 1, 1⟩ := by
  -- req1, enter1, req2
  have h1 : rel next ⟨0, 0, 1⟩ ⟨1, 0, 1⟩ := by
    simp only [next, req1, enter1, exit1, req2, enter2, exit2]
    action_simp
    grind
  have h2 : rel next ⟨1, 0, 1⟩ ⟨2, 0, 1⟩ := by
    simp only [next, req1, enter1, exit1, req2, enter2, exit2]
    action_simp
    grind
  have h3 : rel next ⟨2, 0, 1⟩ ⟨2, 1, 1⟩ := by
    simp only [next, req1, enter1, exit1, req2, enter2, exit2]
    action_simp
    grind
  exact (Reach.step (Reach.step (Reach.single h1) h2) h3)

/-- While process 1 is in the critical section and process 2 waits, process 2
cannot take a step into the critical section: its guard is still false. -/
theorem p2_blocked_while_p1_critical :
    ∀ q, ¬ rel enter2 ⟨2, 1, 1⟩ q := by
  intro q
  apply not_rel_guard_seq
  simp

/-- Combined statement: mutual exclusion holds, and process 2 is stuck exactly
while process 1 holds the turn. -/
theorem mutex_demo :
    Reach M.next ⟨0, 0, 1⟩ ⟨2, 1, 1⟩ ∧ (∀ q, ¬ rel enter2 ⟨2, 1, 1⟩ q) :=
  ⟨p1_can_enter, p2_blocked_while_p1_critical⟩

/-! ## Per-process bounds as an extra invariant -/

/-- Both program counters stay inside the intended range. -/
theorem pc_bounds : M.Safe (fun s => s.pc1 ≤ 2 ∧ s.pc2 ≤ 2) := by
  apply Module.safe_of_preserves
  · intro s hs
    simp only [M, init] at hs ⊢
    grind
  · inv_induct
    simp only [M, next, req1, enter1, exit1, req2, enter2, exit2] at *
    action_simp
    grind

end Examples.Mutex
