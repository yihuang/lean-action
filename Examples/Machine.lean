/-
Examples.Machine
================

A program-parameterised machine: the *remaining code* lives in the state and a
step executes whatever instruction sits at the head. This exercises the parts of
the DSL the other examples do not:

* `choiceAll` — an unbounded nondeterministic choice over instructions, used to
  *dispatch* on the state-stored program: the guard `code.head? = some i` pins
  the witness down, so no dependent matching on the state is needed;
* a generic safety property that holds for **every** program (the code never
  grows), proved once with `inv_induct` + `action_simp` + `grind`;
* concrete runs: `[push 2, push 3, add]` computes 5, and the result is exposed by
  reachability without needing a `halt`.
-/
import LeanAction

open LeanAction

namespace Examples.Machine

inductive Instr where
  | push (n : Nat)
  | add
  | halt
  deriving DecidableEq, Repr

structure VM where
  code : List Instr
  stack : List Nat

/-- The effect of a single (already decoded) instruction. -/
def execInstr : Instr → Action VM
  | .push n => update fun m => { m with code := m.code.tail, stack := n :: m.stack }
  | .add => guard (fun m => 2 ≤ m.stack.length) ;; update (fun m =>
      match m.stack with
      | a :: b :: rest => { m with code := m.code.tail, stack := (a + b) :: rest }
      | s => { m with code := m.code.tail, stack := s })
  | .halt => update fun m => { m with code := [] }

/-- Execute the instruction at the head of the code, if any. The `choiceAll`
witness is the instruction to run; the guard pins it to the actual head. -/
def step : Action VM :=
  choiceAll fun i => guard (fun m => m.code.head? = some i) ;; execInstr i

/-- To run a specific head instruction it suffices to exhibit it as the
`choiceAll` witness. -/
theorem rel_step_of_head {m m' : VM} {i : Instr} (h : m.code.head? = some i)
    (h' : rel (execInstr i) m m') : rel step m m' := by
  refine ⟨i, ?_⟩
  show rel (seq (guard (fun m : VM => m.code.head? = some i)) (execInstr i)) m m'
  simp only [seq, rel_bind_action, rel_guard]
  exact ⟨m, ⟨h, rfl⟩, h'⟩

/-! ## Generic safety: the code never grows

Every instruction consumes the head of the code (or clears it), so the code can
never grow — for *every* program. The per-instruction fact is isolated first,
because there `grind`/`omega` only needs the `code` component; the main theorem
is then a one-liner over the `choiceAll` dispatch. -/
theorem execInstr_code_shrinks {i : Instr} {m m' : VM} (h : rel (execInstr i) m m') :
    m'.code.length ≤ m.code.length := by
  cases i with
  | push n =>
    simp only [execInstr, rel_update] at h
    rw [h]
    simp only [List.length_tail]
    omega
  | add =>
    simp only [execInstr, seq, rel_bind_action, rel_guard, rel_update] at h
    obtain ⟨m, ⟨-, rfl⟩, h⟩ := h
    rw [h]
    -- the guard `2 ≤ stack.length` makes the two stack cases below the only ones
    cases m.stack with
    | nil => simp
    | cons a rest =>
      cases rest with
      | nil => simp
      | cons b rest' =>
        simp only [List.length_tail]
        omega
  | halt =>
    simp only [execInstr, rel_update] at h
    rw [h]
    simp

theorem code_never_grows (k : Nat) : Preserves step (fun m : VM => m.code.length ≤ k) := by
  unfold Preserves
  intro s hs s' hstep
  simp only [step, rel_choiceAll] at hstep
  obtain ⟨i, hstep⟩ := hstep
  simp only [seq, rel_bind_action, rel_guard] at hstep
  obtain ⟨u, ⟨-, rfl⟩, hrel⟩ := hstep
  exact Nat.le_trans (execInstr_code_shrinks hrel) hs

/-! ## Instruction semantics, as reusable lemmas -/

theorem rel_push {n : Nat} {code : List Instr} {stack : List Nat} :
    rel (execInstr (.push n)) ⟨.push n :: code, stack⟩ ⟨code, n :: stack⟩ := by
  simp only [execInstr, rel_update, List.tail_cons]

/-- `add` pops two operands and pushes their sum. -/
theorem rel_add {a b : Nat} {rest : List Nat} {code : List Instr} :
    rel (execInstr .add) ⟨.add :: code, a :: b :: rest⟩ ⟨code, (a + b) :: rest⟩ := by
  simp only [execInstr, seq, rel_bind_action, rel_guard, rel_update]
  refine ⟨⟨.add :: code, a :: b :: rest⟩, ⟨?_, rfl⟩, ?_⟩
  · simp only [List.length_cons]; omega
  · rfl

/-! ## A concrete run: 2 + 3 = 5 -/

theorem run1 : rel step ⟨[.push 2, .push 3, .add], []⟩ ⟨[.push 3, .add], [2]⟩ :=
  rel_step_of_head (i := .push 2) rfl (by simpa using rel_push (n := 2))

theorem run2 : rel step ⟨[.push 3, .add], [2]⟩ ⟨[.add], [3, 2]⟩ :=
  rel_step_of_head (i := .push 3) rfl (by simpa using rel_push (n := 3) (stack := [2]))

theorem run3 : rel step ⟨[.add], [3, 2]⟩ ⟨[], [5]⟩ :=
  rel_step_of_head (i := .add) rfl (by simpa using rel_add (a := 3) (b := 2) (rest := []) (code := []))

/-- The whole program computes `2 + 3 = 5`. -/
theorem run_2_plus_3 : Reach step ⟨[.push 2, .push 3, .add], []⟩ ⟨[], [5]⟩ :=
  Reach.step (Reach.step (Reach.single run1) run2) run3

/-- The computed value is observable by reachability alone (no `halt` needed). -/
theorem run_reaches_five :
    ∃ m, Reach step ⟨[.push 2, .push 3, .add], []⟩ m ∧ m.stack = [5] :=
  ⟨_, run_2_plus_3, rfl⟩

end Examples.Machine
