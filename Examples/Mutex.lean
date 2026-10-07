/-
Examples.Mutex
==============

N-node token-based mutual exclusion on a single shared state record.

This generalizes the original two-process turn protocol along the two axes the
old version hard-coded:

* the **node count is a parameter** `n`, with nodes indexed by `Fin n`, and the
  six process steps of the two-process version become a `choiceAll` over `Fin n`;
* the per-node **program counter is an inductive type** `Pc`
  (`out`/`wait`/`cs`) instead of `Nat`, so there are no magic numbers and no
  separate "the pc is in range" invariant to prove — see `pc_cases`.

The protocol is the same token/turn discipline: node `i` asks for the token
(`req`), enters the critical section when it holds it (`enter`), and on leaving
hands the token to the next node in the ring (`exit`). Mutual exclusion rests on
one invariant: *a node in the critical section holds the token*. Since `turn` is
a single value, two nodes in the critical section would both have to equal it,
which pins them to the same index.

The system is still *one* `Module` over *one* record (the token is shared), as in
the two-process version; what changes is that the state is an *array* of program
counters, so the actions write `upd s.pc i v`. Because `upd_fun` is part of
`action_simp`'s simp set and the `choiceAll` witness is case-split by the
normalization there, the obligations stay `action_simp; grind` (see `inv_step`). -/
import LeanAction

open LeanAction

namespace Examples.Mutex

/-- Per-node program counter. -/
inductive Pc where
  /-- The node is not interested in the critical section. -/
  | out
  /-- The node is requesting and waiting for the token. -/
  | wait
  /-- The node is in the critical section. -/
  | cs
  deriving DecidableEq, Repr

/-- State of an `n`-node system: a program counter per node, and the single
token position `turn`. -/
structure St (n : Nat) where
  pc : Fin n → Pc
  turn : Fin n

/-- Successor in the ring: where `exit` hands the token. Note that `i : Fin n`
itself supplies the proof `0 < n`, so no `NeZero` side condition is needed. -/
def nxt {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- Write node `i`'s program counter. Used to *name* states (`waiting`,
`critical`, `queued`); the actions below write the update inline so that
`action_simp` (which unfolds `upd` via `upd_fun`) sees the array update. -/
def setPc {n : Nat} (s : St n) (i : Fin n) (v : Pc) : St n :=
  { s with pc := upd s.pc i v }

/-- The view of node `i`'s program counter (`Tests/Relies` registers a
`PreservesView` certificate for it). -/
def pcView {n : Nat} (i : Fin n) : View (St n) Pc :=
  ⟨fun s => s.pc i, fun s v => setPc s i v⟩

/-- Node `i` asks for the token. The guard keeps a node inside the critical
section from "re-requesting", which safety would not notice but which destroys
the stability of the liveness region (see `Examples/MutexLiveness`). -/
def req {n : Nat} (i : Fin n) : Action (St n) :=
  guard (fun s => s.pc i = Pc.out) ;; update (fun s => { s with pc := upd s.pc i Pc.wait })

/-- Node `i` enters the critical section when it holds the token. -/
def enter {n : Nat} (i : Fin n) : Action (St n) :=
  guard (fun s => s.pc i = Pc.wait ∧ s.turn = i) ;;
    update (fun s => { s with pc := upd s.pc i Pc.cs })

/-- Node `i` leaves the critical section and hands the token to its successor. -/
def exit {n : Nat} (i : Fin n) : Action (St n) :=
  guard (fun s => s.pc i = Pc.cs) ;;
    update (fun s => { s with pc := upd s.pc i Pc.out, turn := nxt i })

/-- Node `i`'s own steps. -/
def steps {n : Nat} (i : Fin n) : Action (St n) := req i <|> enter i <|> exit i

/-- One step of the system: any node moves. This replaces the two-process
`steps1 <|> steps2` by `choiceAll` over `Fin n`. -/
def next {n : Nat} : Action (St n) := choiceAll (fun i => steps i)

/-- A node step is a system step. -/
theorem rel_next_of {n : Nat} {i : Fin n} {s s' : St n} (h : rel (steps i) s s') :
    rel (next (n := n)) s s' :=
  ⟨i, h⟩

/-- Initially every node is `out`; the token may be anywhere. -/
def init {n : Nat} : Nondet (St n) := fun s => ∀ i, s.pc i = Pc.out

/-- The parameterized module. -/
def M (n : Nat) : Module (St n) := ⟨init, next⟩

/-- **The invariant**: a node in the critical section holds the token. -/
def inv {n : Nat} (s : St n) : Prop := ∀ i, s.pc i = Pc.cs → s.turn = i

/-- Mutual exclusion, as a predicate: at most one node is in the critical
section. (It follows from `inv` because `turn` is single-valued.) -/
def Mutex {n : Nat} (s : St n) : Prop :=
  ∀ i j, s.pc i = Pc.cs → s.pc j = Pc.cs → i = j

/-! ## Safety -/

/-- The invariant is inductive. With `action_simp` now consuming the `choiceAll`
witness, unfolding the array update (`upd_fun`) and collapsing the
`∃ t, (P s ∧ t = s) ∧ …` shape of `guard ;; update`, the whole obligation is one
`action_simp; grind` — the same shape as the two-process version. The `exit`
branch's new token value `nxt a` is never needed: the `exit` guard plus the old
invariant already force the moved node to be the one in the critical section. -/
theorem inv_step {n : Nat} : Preserves (next (n := n)) (inv (n := n)) := by
  unfold Preserves
  intro s hs s' hstep
  simp only [next, steps, req, enter, exit, inv] at *
  action_simp
  grind

theorem inv_init {n : Nat} : (init (n := n)) ⊆ₙ inv (n := n) := by
  intro s hs
  simp only [init, inv] at hs ⊢
  intro i hi
  have := hs i
  grind

/-- Mutual exclusion: two nodes are never in the critical section together. -/
theorem mutex_safe {n : Nat} : (M n).Safe (Mutex (n := n)) :=
  Module.safe_of_invariant (M := M n) (I := inv (n := n))
    (fun s hs => inv_init s hs)
    (by simpa only [M] using inv_step (n := n))
    (fun s hs => by
      simp only [inv, Mutex] at hs ⊢
      intro i j hi hj
      have hi' := hs i hi
      have hj' := hs j hj
      grind)

/-- The replacement for the old `pc_bounds`: with an inductive program counter
every pc is one of the three phases, so "the pc is in range" is discharged by
`cases` rather than by a protocol invariant. -/
theorem pc_cases {n : Nat} (s : St n) (i : Fin n) :
    s.pc i = Pc.out ∨ s.pc i = Pc.wait ∨ s.pc i = Pc.cs := by
  cases s.pc i <;> simp

/-! ## Constructive reachability: what *can* happen -/

/-- The all-`out` state with the token at `i`. -/
def start {n : Nat} (i : Fin n) : St n := { pc := fun _ => Pc.out, turn := i }

/-- The state in which node `i` waits for the token — the result of `req`. -/
def waiting {n : Nat} (i : Fin n) : St n := setPc (start i) i Pc.wait

/-- `req` then `enter`: an initial state whose token sits at `i` reaches the
state in which node `i` is in the critical section. -/
theorem can_enter {n : Nat} (i : Fin n) :
    Reach (next (n := n)) (start i) (setPc (waiting i) i Pc.cs) := by
  have h1 : rel (req i) (start i) (waiting i) := by
    simp only [req, waiting, start, setPc]
    action_simp <;> grind
  have h2 : rel (enter i) (waiting i) (setPc (waiting i) i Pc.cs) := by
    simp only [enter, waiting, start, setPc]
    action_simp <;> grind
  have hs1 : rel (steps i) (start i) (waiting i) := by
    simp only [steps, rel_orElse]
    grind
  have hs2 : rel (steps i) (waiting i) (setPc (waiting i) i Pc.cs) := by
    simp only [steps, rel_orElse]
    grind
  exact Reach.step (Reach.single (rel_next_of hs1)) (rel_next_of hs2)

/-- A state in which node `i` is in the critical section and node `j` is
waiting for the token. -/
def critical {n : Nat} (i : Fin n) : St n := setPc (start i) i Pc.cs

/-- The critical section of `i` with `j` queued behind it. -/
def queued {n : Nat} (i j : Fin n) : St n := setPc (critical i) j Pc.wait

/-- While node `i` holds the token, a *waiting* node `j ≠ i` cannot enter the
critical section: its guard asks for the token, which is at `i`. Compared with
the two-process version this is the same `not_rel_guard_seq` argument, but with
the `j ≠ i` side condition made explicit. -/
theorem blocked_by_token {n : Nat} {i j : Fin n} (h : j ≠ i) :
    ∀ q, ¬ rel (enter j) (queued i j) q := by
  intro q
  apply not_rel_guard_seq
  unfold queued critical start setPc upd at *
  simp_all
  exact fun hij => h hij.symm

/-- Combined statement: mutual exclusion holds, and node `j` is stuck exactly
while node `i` holds the token. -/
theorem mutex_demo {n : Nat} {i j : Fin n} (h : j ≠ i) :
    (M n).Safe (Mutex (n := n)) ∧ (∀ q, ¬ rel (enter j) (queued i j) q) :=
  ⟨mutex_safe, blocked_by_token h⟩

end Examples.Mutex
