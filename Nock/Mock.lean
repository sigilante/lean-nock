import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Comp
open Noun

/-!
# `+mock`: why the jet contract must be three-valued

Virtualized Nock (`+mock`) turns a deterministic crash into a value: the toon
`[%2 trace]`.  Divergence stays divergence, and a nondeterministic bail
(`%intr`, `%meme`, …) fails the whole event, so Hoon code sees nothing.  A jet
that exits where its formula diverges is therefore observable from ordinary
Hoon code.

This module models a jetted call and virtualization, and proves both halves of
the manuscript's argument:

* `two_valued_unsound` — a jet can satisfy the naïve two-valued contract
  (agree on every value) and still be observably wrong under `+mock`.  The
  witness is the manuscript's own: the canonical count-up `dec`, which
  diverges at `0`, jetted by native decrement, which exits at `0`.
* `three_valued_sound` — a jet satisfying the three-valued contract is
  indistinguishable from its formula, under `+mock` or otherwise.

`word_jet_sound` closes the loop: every Λ word, jetted by its C model, meets
the three-valued contract.  The guarded `dec` is sound where the unguarded one
is not, and the guards are what make the difference.

Scope: `+mock` also services scry (opcode 12), which is not modeled and does
not bear on the argument.
-/

/-- What a jet can do: return, bail deterministically (`%exit`), bail
    nondeterministically (the event fails), or punt to the formula. -/
inductive JetOut
  | val  : Noun → JetOut
  | exit : JetOut
  | bail : JetOut
  | punt : JetOut
  deriving DecidableEq, Repr

/-- A jetted call of formula `F` on `S`, as seen from inside Nock.  A
    nondeterministic bail has no in-Nock outcome: the event fails. -/
inductive JetEval (j : Noun → JetOut) (S F : Noun) : Outcome → Prop where
  | val {v} : j S = .val v → JetEval j S F (.val v)
  | exit    : j S = .exit → JetEval j S F .exit
  | punt {o} : j S = .punt → NockEval S F o → JetEval j S F o

/-- `+mock` over an evaluation: a value `v` observes as `[0 v]`, a
    deterministic crash as `[2 ~]` — itself a value.  No outcome, no
    observation. -/
inductive Mock (E : Outcome → Prop) : Noun → Prop where
  | val {v} : E (.val v) → Mock E (cell (atom 0) v)
  | exit    : E .exit → Mock E (cell (atom 2) (atom 0))

/-- The naïve contract: the jet returns `v` exactly when the formula does.
    Every other behavior — crash or divergence — counts as one "bottom". -/
def TwoValued (F : Noun) (j : Noun → JetOut) : Prop :=
  ∀ S v, NockEval S F (.val v) ↔ j S = .val v

/-- The three-valued contract, as the paper states it: on every subject the
    jet either punts, or Equations (2a)–(2c) all hold.  `bail` stands for every
    non-returning jet behavior — a nondeterministic bail or divergence — since
    neither is observable from inside Nock.  Clause (c) is implied by (a) and
    (b) once punting is excluded; it is kept to mirror the paper. -/
def ThreeValued (F : Noun) (j : Noun → JetOut) : Prop :=
  ∀ S, j S ≠ .punt →
    (∀ v, NockEval S F (.val v) ↔ j S = .val v) ∧
    (NockEval S F .exit ↔ j S = .exit) ∧
    (Diverges S F → j S = .bail)

-- ---------------------------------------------------------------------------
-- Soundness of the three-valued contract
-- ---------------------------------------------------------------------------

/-- **The three-valued contract is sound.**  A jet meeting it has exactly the
    formula's outcomes, as seen from inside Nock. -/
theorem three_valued_sound {F : Noun} {j : Noun → JetOut} (h : ThreeValued F j)
    (S : Noun) (o : Outcome) : JetEval j S F o ↔ NockEval S F o := by
  cases hj : j S with
  | punt =>
    constructor
    · intro hJ
      cases hJ with
      | val hv => rw [hj] at hv; cases hv
      | exit he => rw [hj] at he; cases he
      | punt _ hn => exact hn
    · exact JetEval.punt hj
  | val v =>
    obtain ⟨ha, -, -⟩ := h S (by rw [hj]; exact fun e => by cases e)
    have hF : NockEval S F (.val v) := (ha v).2 hj
    constructor
    · intro hJ
      cases hJ with
      | val hv => rw [hj] at hv; cases hv; exact hF
      | exit he => rw [hj] at he; cases he
      | punt hp _ => rw [hj] at hp; cases hp
    · intro hn
      have := NockEval.deterministic hn hF
      subst this
      exact JetEval.val hj
  | exit =>
    obtain ⟨-, hb, -⟩ := h S (by rw [hj]; exact fun e => by cases e)
    have hF : NockEval S F .exit := hb.2 hj
    constructor
    · intro hJ
      cases hJ with
      | val hv => rw [hj] at hv; cases hv
      | exit _ => exact hF
      | punt hp _ => rw [hj] at hp; cases hp
    · intro hn
      have := NockEval.deterministic hn hF
      subst this
      exact JetEval.exit hj
  | bail =>
    obtain ⟨ha, hb, -⟩ := h S (by rw [hj]; exact fun e => by cases e)
    constructor
    · intro hJ
      cases hJ with
      | val hv => rw [hj] at hv; cases hv
      | exit he => rw [hj] at he; cases he
      | punt hp _ => rw [hj] at hp; cases hp
    · intro hn
      cases o with
      | val v => have := (ha v).1 hn; rw [hj] at this; cases this
      | exit  => have := hb.1 hn; rw [hj] at this; cases this

/-- ... hence indistinguishable under `+mock`. -/
theorem three_valued_mock {F : Noun} {j : Noun → JetOut} (h : ThreeValued F j)
    (S x : Noun) : Mock (JetEval j S F) x ↔ Mock (NockEval S F) x := by
  have e : JetEval j S F = NockEval S F :=
    funext fun o => propext (three_valued_sound h S o)
  rw [e]

-- ---------------------------------------------------------------------------
-- Unsoundness of the two-valued contract
-- ---------------------------------------------------------------------------

/-- Native decrement, as a jet on a bare atom: `n+1 ↦ n`, and a deterministic
    bail at `0` and on a cell — the natural C routine. -/
def natDec : Noun → JetOut
  | atom (n + 1) => .val (atom n)
  | atom 0       => .exit
  | cell _ _     => .exit

/-- Native decrement meets the two-valued contract for the canonical
    count-up `dec`: they agree on every value. -/
theorem natDec_twoValued : TwoValued countUp natDec := by
  intro S v
  cases S with
  | cell x y =>
    constructor
    · intro h; exact (countUp_cell_diverges x y _ h).elim
    · intro h; cases h
  | atom n =>
    cases n with
    | zero =>
      constructor
      · intro h; exact (countUp_zero_diverges _ h).elim
      · intro h; cases h
    | succ n =>
      constructor
      · intro h
        have := NockEval.deterministic h (countUp_correct n)
        cases this
        rfl
      · intro h
        cases h
        exact countUp_correct n

/-- ... but not the three-valued one: at `0` the formula diverges and the jet
    exits. -/
theorem natDec_not_threeValued : ¬ ThreeValued countUp natDec := by
  intro h
  have := (h (atom 0) (fun e => by cases e)).2.2 countUp_zero_diverges
  cases this

/-- **The two-valued contract is unsound.**  There is a formula and a jet that
    agree on every value, yet `+mock` tells them apart: on `0` the jetted call
    observes `[2 ~]`, and the formula observes nothing, because it diverges.
    This is the `+dec` incident as a theorem. -/
theorem two_valued_unsound :
    ∃ (F : Noun) (j : Noun → JetOut), TwoValued F j ∧
      ∃ S x, Mock (JetEval j S F) x ∧ ¬ Mock (NockEval S F) x :=
  ⟨countUp, natDec, natDec_twoValued, atom 0, cell (atom 2) (atom 0),
    Mock.exit (JetEval.exit rfl),
    fun h => by
      cases h with
      | exit he => exact countUp_zero_diverges _ he⟩

-- ---------------------------------------------------------------------------
-- Λ words meet the three-valued contract
-- ---------------------------------------------------------------------------

/-- The C model of a word, as a jet: it returns or exits, never bails or
    punts. -/
def wordJet (w : Word) (S : Noun) : JetOut :=
  match cw w S with
  | .val v => .val v
  | .exit  => .exit

/-- **Every Λ word, jetted by its C model, meets the three-valued contract.**
    The guards emitted by Λ make each formula crash-total, so there is no
    divergence for a jet to mishandle. -/
theorem word_jet_sound (w : Word) : ThreeValued (phi w) (wordJet w) := by
  intro S _
  have hl := leaf_correct w S
  refine ⟨fun v => ?_, ?_, fun hd => (word_crash_total w S hd).elim⟩
  · constructor
    · intro hv
      have := NockEval.deterministic hv hl
      simp only [wordJet, ← this]
    · intro hj
      simp only [wordJet] at hj
      cases hc : cw w S with
      | val u => rw [hc] at hj hl; cases hj; exact hl
      | exit  => rw [hc] at hj; cases hj
  · constructor
    · intro he
      have := NockEval.deterministic he hl
      simp only [wordJet, ← this]
    · intro hj
      simp only [wordJet] at hj
      cases hc : cw w S with
      | val u => rw [hc] at hj; cases hj
      | exit  => rw [hc] at hl; exact hl
