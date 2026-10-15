/-
Examples.Paxos
==============

The core safety argument of **simple (single-decree) Paxos**, mechanised on top
of `LeanAction`.

The development follows Lamport's decomposition of Paxos into a *voting*
algorithm plus a *proposer*.  Concretely it is a re-implementation of the
`Voting` module of the TLA+ `Paxos` specification, whose safety proof is the
mathematical heart of Paxos:

* **Acceptors** own a promise number `maxBal` and a vote history `votes`
  (`votes a b v` = "acceptor `a` has voted for value `v` in ballot `b`").
* `increaseMaxBal a b`  — an acceptor promises never to vote below `b`.
* `voteFor a b v`       — an acceptor votes for `v` in ballot `b`, but only if
  `v` comes with a phase-2a certificate `ShowsSafeAt Q b v` from a quorum `Q`,
  and no other acceptor has voted differently in `b`.

The inductive invariant is

    Inv(s)  :=  VotesSafe(s) ∧ OneValuePerBallot(s)

and the safety theorem is that any two chosen ballots carry the same value.

The invariants, in the order in which they are useful:

1. `OneValuePerBallot`  — no two acceptors vote for different values in the
                          same ballot.
2. `VotesSafe`          — every cast vote is *safe at its ballot*: for every
                          lower ballot, nothing other than the voted value can
                          ever be chosen there (`NoneOtherChoosableAt`).
3. `showsSafeAt_safe`   — the phase-2a certificate implies safety
                          (Lamport's `ShowsSafety`).
4. `chosen_agree`       — `VotesSafe` + `OneValuePerBallot` give agreement
                          (Lamport's `VotesSafeImpliesConsistency`).

**Ballots.**  A ballot is a *positive* natural, `Ballot := {n : Nat // 0 < n}`.
The TLA+ encoding uses `maxBal : Acceptor → Ballot ∪ {-1}` and additionally
carries a `TypeOK` invariant saying "ballot `0`/`-1` is never voted in".  Here
that fact is a *typing* fact instead: `votes a b v` is only well-formed for
`b : Ballot`, so no state predicate is needed and `TypeOK` vanishes.  The
"no promise yet" bottom is the plain `0 : Nat` in `maxBal`.

**Genericity.**  The acceptor set and the quorum rule are not hard-wired.  We
work over an arbitrary acceptor type `A` equipped with a `QuorumSystem A`
instance — a predicate `Quorum` on acceptor sets together with the two facts
Paxos needs, quorum intersection and quorum non-emptiness.  All arithmetic of
"majority" is pushed into instances:

* `instQuorumFin3` — majority on three acceptors (the classic example);
* `unanimous A`    — on *any* non-empty `A`, "everybody agrees" is a quorum,
  which yields Paxos over `Fin n` for every `n ≥ 1` (`paxos_safe_unanimous`).

The protocol, the invariant, and every proof below are thus parametric in the
number of acceptors — only the instance changes.

**Notation.**  A state predicate takes the state as an *explicit* first
argument and lives in `namespace St`, so it reads either `SafeAt s b v` or, in
the "s-subject" style used throughout, `s.SafeAt b v`.  The state is kept
explicit on purpose: Paxos proofs constantly relate two states (`s` and
`s.castVote a b v`), and an implicit state would be uninferable there.

**Automation.**  The action semantics is unfolded with the library's pipeline,
`simp only [named action, inv] at *` followed by `action_simp`; `grind` then
discharges the first-order obligations (`inv_init` and the `OneValuePerBallot`
conjunct of each step).  The `VotesSafe` conjunct is deliberately *not* left to
`grind`: it needs its quorum witness (`∃ Q, …`) re-established across the state
update, and the phase-2a certificate needs a minimal-ballot case split.  Those
steps are the explicit lemmas `safeAt_setMaxBal` / `safeAt_castVote` and
`showsSafeAt_safe`, which `preserves_*` then applies.
-/
import LeanAction

open LeanAction

universe u

namespace Examples.Paxos

/-! ## Quorum systems -/

/-- A *quorum system* on the acceptor type `A`: a predicate on acceptor sets
together with the two structural facts Paxos needs.  Quorum intersection is the
only place the arithmetic of "majority" is used, and it is exactly TLA+'s
`QuorumAssumption`. -/
class QuorumSystem (A : Type u) where
  /-- Which sets of acceptors count as quorums. -/
  IsQuorum : (A → Prop) → Prop
  /-- Any two quorums intersect. -/
  inter : ∀ {Q Q' : A → Prop}, IsQuorum Q → IsQuorum Q' → ∃ a, Q a ∧ Q' a
  /-- Every quorum is non-empty. -/
  nonempty : ∀ {Q : A → Prop}, IsQuorum Q → ∃ a, Q a

/-- `Q` is a quorum. -/
def Quorum {A : Type u} [QuorumSystem A] (Q : A → Prop) : Prop := QuorumSystem.IsQuorum Q

/-- **Majority on three acceptors**: any two of the three. -/
def fin3Quorum (Q : Fin 3 → Prop) : Prop :=
  (Q 0 ∧ Q 1) ∨ (Q 0 ∧ Q 2) ∨ (Q 1 ∧ Q 2)

theorem fin3Quorum_inter {Q Q' : Fin 3 → Prop} (h : fin3Quorum Q) (h' : fin3Quorum Q') :
    ∃ a, Q a ∧ Q' a := by
  unfold fin3Quorum at *
  rcases h with h | h | h <;> rcases h' with h' | h' | h' <;> grind

theorem fin3Quorum_nonempty {Q : Fin 3 → Prop} (h : fin3Quorum Q) : ∃ a, Q a := by
  unfold fin3Quorum at h
  rcases h with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h1, _⟩
  · exact ⟨0, h0⟩
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩

instance instQuorumFin3 : QuorumSystem (Fin 3) where
  IsQuorum := fin3Quorum
  inter := fin3Quorum_inter
  nonempty := fin3Quorum_nonempty

/-- **Unanimity**: on any non-empty acceptor set, "every acceptor agrees" is a
quorum system.  Instantiating at `Fin n` gives Paxos over an arbitrary number
of acceptors, uniformly.  It is registered with low priority so that a more
specific quorum system (such as `instQuorumFin3`) wins when one exists. -/
instance (priority := 100) unanimous (A : Type u) [Nonempty A] : QuorumSystem A where
  IsQuorum Q := ∀ a, Q a
  inter := by
    intro Q Q' h h'
    obtain ⟨a⟩ := ‹Nonempty A›
    exact ⟨a, h a, h' a⟩
  nonempty := by
    intro Q h
    obtain ⟨a⟩ := ‹Nonempty A›
    exact ⟨a, h a⟩

variable {A : Type u} [DecidableEq A] [QuorumSystem A]

/-! ## State and the "voting" vocabulary -/

/-- **Ballots** are the *positive* naturals.  Making this a subtype (rather than
`Nat` with `0` as a "bottom" sentinel) embeds "ballot `0` is never voted in"
into the type, so it needs no state invariant (`TypeOK` in TLA+). -/
abbrev Ballot := { n : Nat // 0 < n }

/-- Acceptor state: the highest ballot promised (`0` = none yet), plus the whole
vote history over real ballots. -/
structure St (A : Type u) where
  maxBal : A → Nat
  votes : A → Ballot → Nat → Prop

namespace St

/-- `a` voted `v` in ballot `b`. -/
def VotedFor (s : St A) (a : A) (b : Ballot) (v : Nat) : Prop := s.votes a b v

/-- `a` has cast no vote in ballot `b`. -/
def DidNotVoteAt (s : St A) (a : A) (b : Ballot) : Prop := ∀ v, ¬ s.votes a b v

/-- `a` has promised ballot `b` (or a higher one), so it will never vote below
`b` (TLA+'s `maxBal[a] ≥ b`). -/
def Promised (s : St A) (a : A) (b : Ballot) : Prop := (b : Nat) ≤ s.maxBal a

/-- `a` can no longer vote in ballot `b`: it promised a strictly higher ballot
and never voted in `b`. -/
def CannotVoteAt (s : St A) (a : A) (b : Ballot) : Prop :=
  (b : Nat) < s.maxBal a ∧ s.DidNotVoteAt a b

/-- No value other than `v` can ever be chosen in ballot `b`: some quorum is
either fully committed to `v` at `b`, or is unable to vote in `b` at all. -/
def NoneOtherChoosableAt (s : St A) (b : Ballot) (v : Nat) : Prop :=
  ∃ Q, Quorum Q ∧ ∀ a, Q a → s.VotedFor a b v ∨ s.CannotVoteAt a b

/-- Nobody in `Q` cast a vote in any ballot below `b`. -/
def NoVotesBelow (s : St A) (Q : A → Prop) (b : Ballot) : Prop :=
  ∀ d : Ballot, d < b → ∀ a, Q a → s.DidNotVoteAt a d

/-- Nobody in `Q` cast a vote in any ballot strictly between `lo` and `hi`. -/
def NoVotesBetween (s : St A) (Q : A → Prop) (lo hi : Ballot) : Prop :=
  ∀ d : Ballot, lo < d → d < hi → ∀ a, Q a → s.DidNotVoteAt a d

/-- Some member of `Q` voted for `v` in ballot `c`. -/
def VotedInQuorum (s : St A) (Q : A → Prop) (c : Ballot) (v : Nat) : Prop :=
  ∃ a, Q a ∧ s.VotedFor a c v

/-- **Safety of a value at a ballot**: every lower ballot can only produce `v`. -/
def SafeAt (s : St A) (b : Ballot) (v : Nat) : Prop :=
  ∀ c : Ballot, c < b → s.NoneOtherChoosableAt c v

/-- Every vote an acceptor has cast is safe at the ballot it was cast in. -/
def VotesSafe (s : St A) : Prop := ∀ a b v, s.VotedFor a b v → s.SafeAt b v

/-- No two acceptors vote for different values in the same ballot. -/
def OneValuePerBallot (s : St A) : Prop :=
  ∀ a1 a2 b v1 v2, s.VotedFor a1 b v1 → s.VotedFor a2 b v2 → v1 = v2

/-- A value is chosen in a ballot when a quorum voted for it there. -/
def ChosenAt (s : St A) (b : Ballot) (v : Nat) : Prop :=
  ∃ Q, Quorum Q ∧ ∀ a, Q a → s.VotedFor a b v

/-- **The phase-2a certificate** (Lamport's `ShowsSafeAt`): the evidence, from
the phase-1b responses of a quorum `Q`, that a proposer may safely put `v` into
ballot `b`.

Read it as: *the highest vote `Q` cast below `b` is for `v`* — or `Q` cast no
vote below `b` at all.  Concretely it says:

* every member of `Q` has already promised at least `b`
  (`b ≤ s.maxBal a`, so it will not vote below `b` again); and
* either `Q` cast no vote below `b` (`s.NoVotesBelow Q b`), or there is a
  highest such ballot `c < b`, carrying a `Q`-vote for `v`
  (`s.VotedInQuorum Q c v`) and with no `Q`-vote in the gap above it
  (`s.NoVotesBetween Q c b`).

(This is TLA+'s definition with the `c = -1` sentinel replaced by an explicit
disjunct.) -/
def ShowsSafeAt (s : St A) (Q : A → Prop) (b : Ballot) (v : Nat) : Prop :=
  (∀ a, Q a → s.Promised a b) ∧
  (s.NoVotesBelow Q b ∨ ∃ c, c < b ∧ s.VotedInQuorum Q c v ∧ s.NoVotesBetween Q c b)

end St

open St

/-! ## The two stateless lemmas -/

omit [DecidableEq A] in
/-- **`ShowsSafety`.**  A phase-2a certificate really does certify safety:
assuming the two invariants, `s.ShowsSafeAt Q b v` implies `s.SafeAt b v`.

Below the certificate ballot `c` we appeal to `VotesSafe` for the member that
voted `v` at `c`; at and above `c` the quorum `Q` itself witnesses that nothing
else can be chosen.  (No `TypeOK` is needed: `c` ranges over real ballots.) -/
theorem showsSafeAt_safe {s : St A} (hVS : s.VotesSafe) (hOV : s.OneValuePerBallot)
    {Q : A → Prop} (hQ : Quorum Q) {b : Ballot} {v : Nat}
    (h : s.ShowsSafeAt Q b v) : s.SafeAt b v := by
  obtain ⟨hbal, hcert⟩ := h
  intro c' hc'
  rcases hcert with hnone | ⟨c, hcb, hcv, hno⟩
  · -- nobody in `Q` voted below `b`: `Q` witnesses every lower ballot
    refine ⟨Q, hQ, fun a ha => Or.inr ⟨?_, ?_⟩⟩
    · have hb : (b : Nat) ≤ s.maxBal a := hbal a ha
      have hc'n : (c' : Nat) < (b : Nat) := hc'; omega
    · exact hnone c' hc' a ha
  · -- somebody voted `v` at `c`; ballots below `c` come from `VotesSafe`
    obtain ⟨a₀, ha₀Q, ha₀v⟩ := hcv
    by_cases hlt : (c' : Nat) < (c : Nat)
    · exact hVS a₀ c v ha₀v c' hlt
    · have hle : (c : Nat) ≤ (c' : Nat) := Nat.le_of_not_lt hlt
      refine ⟨Q, hQ, fun a ha => ?_⟩
      by_cases hvotes : ∃ w, s.votes a c' w
      · -- `a` voted in `c'`; `OneValuePerBallot` forces the value `v`
        obtain ⟨w, hw⟩ := hvotes
        have hcc' : c' = c := by
          rcases Nat.lt_or_eq_of_le hle with h | h
          · exact (hno c' h hc' a ha w hw).elim
          · exact (Subtype.ext h).symm
        subst hcc'
        exact Or.inl (hOV a a₀ c' w v hw ha₀v ▸ hw)
      · -- `a` cast no vote in `c'` and promised above it
        have hno' : ∀ w, ¬ s.votes a c' w := fun w hw => hvotes ⟨w, hw⟩
        exact Or.inr ⟨by
          have hb : (b : Nat) ≤ s.maxBal a := hbal a ha
          have hc'n : (c' : Nat) < (b : Nat) := hc'; omega, hno'⟩

omit [DecidableEq A] in
/-- **The proposer's phase-2a rule.**  If every member of the quorum `Q` has
promised `b`, all of `Q`'s votes lie at ballots `≤ c`, and some member voted
`v` at `c < b`, then `v` is certified at `b`.  This is exactly the rule "pick
the value of the highest-numbered reported vote". -/
theorem showsSafeAt_of_maxVote {s : St A} {Q : A → Prop} (_hQ : Quorum Q)
    {b c : Ballot} {v : Nat} (hbal : ∀ a, Q a → s.Promised a b)
    (hmax : ∀ a d w, Q a → s.VotedFor a d w → (d : Nat) ≤ (c : Nat))
    (hcv : ∃ a, Q a ∧ s.VotedFor a c v) (hcb : (c : Nat) < (b : Nat)) :
    s.ShowsSafeAt Q b v :=
  ⟨hbal, Or.inr ⟨c, hcb, hcv, fun d hcd _ a ha w hw => by
    have hcdn : (c : Nat) < (d : Nat) := hcd
    have := hmax a d w ha hw; omega⟩⟩

omit [DecidableEq A] in
/-- **`VotesSafeImpliesConsistency`.**  Any two chosen ballots agree. -/
theorem chosen_agree {s : St A} (hVS : s.VotesSafe) (hOV : s.OneValuePerBallot)
    {b : Ballot} {v : Nat} {b' : Ballot} {v' : Nat}
    (hb : s.ChosenAt b v) (hb' : s.ChosenAt b' v') : v = v' := by
  by_cases heqb : (b : Nat) = (b' : Nat)
  · have hbb' : b = b' := Subtype.ext heqb
    subst hbb'
    obtain ⟨Q, hQ, hQv⟩ := hb
    obtain ⟨Q', hQ', hQ'v⟩ := hb'
    obtain ⟨a, haQ, haQ'⟩ := QuorumSystem.inter hQ hQ'
    exact hOV a a b v v' (hQv a haQ) (hQ'v a haQ')
  · rcases Nat.lt_or_gt_of_ne heqb with hlt | hgt
    · -- `b < b'`: the vote in `b'` is safe, so `b` cannot produce anything else
      obtain ⟨Q, hQ, hQv⟩ := hb
      obtain ⟨Q', hQ', hQ'v⟩ := hb'
      obtain ⟨a', ha'⟩ := QuorumSystem.nonempty hQ'
      have hsafe : s.NoneOtherChoosableAt b v' :=
        hVS a' b' v' (hQ'v a' ha') b hlt
      obtain ⟨Q'', hQ'', hQ''v⟩ := hsafe
      obtain ⟨a, haQ, haQ''⟩ := QuorumSystem.inter hQ hQ''
      rcases hQ''v a haQ'' with hv' | hc
      · exact hOV a a b v v' (hQv a haQ) hv'
      · exact absurd (hQv a haQ) (hc.2 v)
    · exact (chosen_agree hVS hOV hb' hb).symm
termination_by b.1

/-! ## The state machine -/

namespace St

/-- Record that acceptor `a` promises ballot `b`. -/
def setMaxBal (s : St A) (a : A) (b : Ballot) : St A :=
  { s with maxBal := fun a' => if a' = a then (b : Nat) else s.maxBal a' }

/-- Record a vote of `a` for `v` in ballot `b` (and raise its promise). -/
def castVote (s : St A) (a : A) (b : Ballot) (v : Nat) : St A :=
  { maxBal := fun a' => if a' = a then (b : Nat) else s.maxBal a'
    votes := fun a' b' v' => s.votes a' b' v' ∨ (a' = a ∧ b' = b ∧ v' = v) }

omit [QuorumSystem A] in
@[simp] theorem setMaxBal_maxBal_same (s : St A) (a : A) (b : Ballot) :
    (s.setMaxBal a b).maxBal a = (b : Nat) := by simp [setMaxBal]

omit [QuorumSystem A] in
@[simp] theorem setMaxBal_maxBal_noteq {s : St A} {a a' : A} (b : Ballot)
    (h : a' ≠ a) : (s.setMaxBal a b).maxBal a' = s.maxBal a' := by simp [setMaxBal, h]

omit [QuorumSystem A] in
@[simp] theorem setMaxBal_votes (s : St A) (a : A) (b : Ballot) :
    (s.setMaxBal a b).votes = s.votes := rfl

omit [QuorumSystem A] in
@[simp] theorem castVote_maxBal_same (s : St A) (a : A) (b : Ballot) (v : Nat) :
    (s.castVote a b v).maxBal a = (b : Nat) := by simp [castVote]

omit [QuorumSystem A] in
@[simp] theorem castVote_maxBal_noteq {s : St A} {a a' : A} (b : Ballot) (v : Nat)
    (h : a' ≠ a) : (s.castVote a b v).maxBal a' = s.maxBal a' := by simp [castVote, h]

omit [QuorumSystem A] in
@[simp] theorem castVote_votes (s : St A) (a : A) (b : Ballot) (v : Nat) (a' : A)
    (b' : Ballot) (v' : Nat) :
    (s.castVote a b v).votes a' b' v' ↔
      s.votes a' b' v' ∨ (a' = a ∧ b' = b ∧ v' = v) := by simp [castVote]

end St

/-- An acceptor raises its promise. -/
def increaseMaxBal (a : A) (b : Ballot) : Action (St A) :=
  guard (fun s => s.maxBal a < (b : Nat)) ;; update (fun s => s.setMaxBal a b)

/-- An acceptor votes, provided the proposal carries a phase-2a certificate. -/
def voteFor (a : A) (b : Ballot) (v : Nat) : Action (St A) :=
  guard (fun s =>
    s.maxBal a ≤ (b : Nat) ∧
    (∀ w, ¬ s.votes a b w) ∧
    (∀ a' w, a' ≠ a → s.votes a' b w → w = v) ∧
    (∃ Q, Quorum Q ∧ s.ShowsSafeAt Q b v)) ;;
  update (fun s => s.castVote a b v)

def increase : Action (St A) := choiceAll (fun i : A × Ballot => increaseMaxBal i.1 i.2)

def vote : Action (St A) := choiceAll (fun i : A × Ballot × Nat => voteFor i.1 i.2.1 i.2.2)

/-- One step: either an acceptor raises its promise or it votes. -/
def next : Action (St A) := increase <|> vote

def init : Nondet (St A) := fun s =>
  (∀ a, s.maxBal a = 0) ∧ (∀ a b v, ¬ s.votes a b v)

namespace St

/-- The inductive invariant: votes are safe, and one value per ballot. -/
def Inv (s : St A) : Prop := s.VotesSafe ∧ s.OneValuePerBallot

end St

def M : Module (St A) := ⟨init, next⟩

/-! ## Preservation of the invariant -/

/-- Raising a promise preserves `SafeAt` (votes are unchanged, `maxBal` grows). -/
theorem safeAt_setMaxBal {s : St A} {a : A} {b b' : Ballot} {v' : Nat}
    (hguard : s.maxBal a ≤ (b : Nat)) (h : s.SafeAt b' v') :
    (s.setMaxBal a b).SafeAt b' v' := by
  intro c hc
  obtain ⟨Q, hQ, hQv⟩ := h c hc
  refine ⟨Q, hQ, fun a'' ha'' => ?_⟩
  rcases hQv a'' ha'' with hv | ⟨hlt, hnv⟩
  · exact Or.inl (by simpa [VotedFor, setMaxBal] using hv)
  · refine Or.inr ⟨?_, ?_⟩
    · simp only [setMaxBal] at hlt ⊢; grind
    · simpa [DidNotVoteAt, setMaxBal] using hnv

/-- Casting a vote preserves `SafeAt`, provided the new vote's ballot is at
least the caster's promise: the new ballot cannot occur strictly below `b'`. -/
theorem safeAt_castVote {s : St A} {a : A} {b b' : Ballot} {v v' : Nat}
    (hbal : s.maxBal a ≤ (b : Nat)) (h : s.SafeAt b' v') :
    (s.castVote a b v).SafeAt b' v' := by
  intro c hc
  obtain ⟨Q, hQ, hQv⟩ := h c hc
  refine ⟨Q, hQ, fun a'' ha'' => ?_⟩
  rcases hQv a'' ha'' with hv | ⟨hlt, hnv⟩
  · exact Or.inl (by simp only [VotedFor, castVote_votes]; exact Or.inl hv)
  · refine Or.inr ⟨?_, ?_⟩
    · simp only [castVote] at hlt ⊢; grind
    · intro w hw
      simp only [castVote_votes] at hw
      rcases hw with hw | ⟨rfl, hcb, rfl⟩
      · exact hnv w hw
      · subst hcb; omega

theorem preserves_increaseMaxBal (a : A) (b : Ballot) :
    Preserves (increaseMaxBal a b) St.Inv := by
  unfold Preserves
  intro s hs s' hstep
  -- the library pipeline: expose the named action, then `action_simp` unfolds it
  simp only [increaseMaxBal, St.Inv, VotesSafe, OneValuePerBallot, VotedFor] at *
  action_simp
  obtain ⟨hguard, hs'⟩ := hstep
  subst hs'
  constructor
  · exact fun a' b' v' hv' => safeAt_setMaxBal (Nat.le_of_lt hguard) (hs.1 a' b' v' hv')
  · simp only [setMaxBal] at *
    grind

theorem preserves_voteFor (a : A) (b : Ballot) (v : Nat) :
    Preserves (voteFor a b v) St.Inv := by
  unfold Preserves
  intro s hs s' hstep
  simp only [voteFor, St.Inv, VotesSafe, OneValuePerBallot, VotedFor] at *
  action_simp
  obtain ⟨hbal, hnew, hagree, hcert, hs'⟩ := hstep
  subst hs'
  obtain ⟨Q, hQ, hcert'⟩ := hcert
  have hsafe : s.SafeAt b v := showsSafeAt_safe hs.1 hs.2 hQ hcert'
  constructor
  · intro a' b' v' hv'
    simp only [castVote_votes] at hv'
    rcases hv' with hold | ⟨rfl, rfl, rfl⟩
    · exact safeAt_castVote hbal (hs.1 a' b' v' hold)
    · exact safeAt_castVote hbal hsafe
  · simp only [castVote_votes, Subtype.ext_iff] at *
    grind

theorem inv_step : Preserves (next (A := A)) (St.Inv (A := A)) := by
  intro s hs s' hstep
  simp only [next, increase, vote, rel_orElse, rel_choiceAll] at hstep
  rcases hstep with ⟨⟨a, b⟩, h⟩ | ⟨⟨a, b, v⟩, h⟩
  · exact preserves_increaseMaxBal a b s hs s' h
  · exact preserves_voteFor a b v s hs s' h

omit [DecidableEq A] in
theorem inv_init : (init (A := A)) ⊆ₙ (St.Inv (A := A)) := by
  intro s hs
  simp only [init, St.Inv, VotesSafe, OneValuePerBallot, VotedFor] at hs ⊢
  grind

/-! ## Consensus safety -/

namespace St

/-- Whatever is chosen, is chosen consistently: any two chosen ballots agree. -/
def Consistent (s : St A) : Prop :=
  ∀ b v b' v', s.ChosenAt b v → s.ChosenAt b' v' → v = v'

end St

/-- **Simple Paxos is safe**, for an *arbitrary* acceptor type and quorum
system.  In every reachable state any two chosen ballots carry the same value. -/
theorem paxos_safe : (M (A := A)).Safe (Consistent (A := A)) :=
  Module.safe_of_invariant (M := M) (I := St.Inv) inv_init inv_step
    (fun _ hs _ _ _ _ hb hb' => chosen_agree hs.1 hs.2 hb hb')

namespace St

/-- A value is chosen (in some ballot). -/
def Chosen (s : St A) (v : Nat) : Prop := ∃ b, s.ChosenAt b v

end St

omit [DecidableEq A] in
theorem chosen_unique {s : St A} (hs : s.Inv) {v v' : Nat}
    (h : s.Chosen v) (h' : s.Chosen v') : v = v' := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  exact chosen_agree hs.1 hs.2 hb hb'

/-- The chosen-value form of the safety theorem. -/
theorem paxos_chosen_unique :
    (M (A := A)).Safe (fun s => ∀ v v', s.Chosen v → s.Chosen v' → v = v') :=
  paxos_safe.mono (fun s hs v v' h h' => by
    obtain ⟨b, hb⟩ := h
    obtain ⟨b', hb'⟩ := h'
    exact hs b v b' v' hb hb')

omit [DecidableEq A] [QuorumSystem A] in
/-- The phase-2a certificate is trivial for a ballot in which nobody has voted
yet, provided the quorum has promised at least that ballot. -/
theorem certificate_no_votes {s : St A} {b : Ballot} {v : Nat} {Q : A → Prop}
    (hnovote : ∀ a d w, ¬ s.votes a d w) (hbal : ∀ a, Q a → s.Promised a b) :
    s.ShowsSafeAt Q b v :=
  ⟨hbal, Or.inl (fun d _ a _ w hw => hnovote a d w hw)⟩

/-! ## Genericity: any number of acceptors

The theorems above are parametric in `A` and in the quorum system.  Here are two
extremes of the acceptor count. -/

/-- Paxos over exactly three acceptors with majority quorums (the instance
`instQuorumFin3` is found automatically). -/
example : (M (A := Fin 3)).Safe (Consistent (A := Fin 3)) := paxos_safe

/-- Paxos over *any* non-empty acceptor set `A` with unanimity quorums — in
particular over `Fin n` for every `n ≥ 1`.  The quorum system is the
`unanimous` instance, synthesised from `Nonempty A`. -/
theorem paxos_safe_unanimous (A : Type u) [DecidableEq A] [Nonempty A] :
    (M (A := A)).Safe (Consistent (A := A)) := paxos_safe

/-- Paxos over five acceptors, unanimity quorums. -/
example : (M (A := Fin 5)).Safe (Consistent (A := Fin 5)) := paxos_safe_unanimous (Fin 5)

end Examples.Paxos
