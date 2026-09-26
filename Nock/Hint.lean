import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Term
import Nock.CEval
import Nock.Backward
import Nock.Composition
open Noun

/-!
# Hint transparency

Jets are registered by opcode-11 `%fast` hints wrapped around cores.  The
manuscript's deployment section claims that `Λ_N` may wrap its output in such
hints "without any change to the proof".  This module states exactly when that
is true.

A **static** hint `[11 t f]` (atom tag) is unconditionally transparent.

A **dynamic** hint `[11 [t c] f]` — the form `%fast` takes, where `c` computes
the clue — is transparent **only if the clue formula `c` produces a value** on
the subject.  Nock evaluates `c` first and strictly: if `c` crashes, the hinted
formula crashes whatever `f` does (`hint_not_transparent`), and if `c` diverges
so does the hinted formula.  A constant clue `[1 k]` always produces a value, so
constant-clue hints are unconditionally transparent (`composition_hint_const`).
-/

private theorem no_val_exit {s f v} (hv : NockEval s f (.val v))
    (he : NockEval s f .exit) : False := by
  have := NockEval.deterministic hv he; simp at this

-- ---------------------------------------------------------------------------
-- Static hints
-- ---------------------------------------------------------------------------

/-- A static hint `[11 t f]` is transparent, for every outcome. -/
theorem hint_static_transparent (tag : Nat) (a f : Noun) (o : Outcome) :
    NockEval a (cell (atom 11) (cell (atom tag) f)) o ↔ NockEval a f o := by
  constructor
  · intro h
    cases h with
    | crash_malformed hm => simp [Malformed] at hm
    | op11_static hf => exact hf
  · exact NockEval.op11_static

theorem hint_static_diverges (tag : Nat) (a f : Noun) :
    Diverges a (cell (atom 11) (cell (atom tag) f)) ↔ Diverges a f := by
  simp only [Diverges, hint_static_transparent]

-- ---------------------------------------------------------------------------
-- Dynamic hints
-- ---------------------------------------------------------------------------

/-- A dynamic hint `[11 [t c] f]` is transparent **provided its clue formula
    `c` produces a value** on the subject. -/
theorem hint_dynamic_transparent (tag c a f : Noun) {r : Noun}
    (hc : NockEval a c (.val r)) (o : Outcome) :
    NockEval a (cell (atom 11) (cell (cell tag c) f)) o ↔ NockEval a f o := by
  constructor
  · intro h
    cases h with
    | crash_malformed hm => simp [Malformed] at hm
    | op11_dynamic _ hf => exact hf
    | op11_dyn_crash hce => exact (no_val_exit hc hce).elim
  · exact NockEval.op11_dynamic hc

theorem hint_dynamic_diverges (tag c a f : Noun) {r : Noun}
    (hc : NockEval a c (.val r)) :
    Diverges a (cell (atom 11) (cell (cell tag c) f)) ↔ Diverges a f := by
  simp only [Diverges, hint_dynamic_transparent tag c a f hc]

/-- **The side condition is necessary.**  A dynamic hint whose clue crashes
    turns a formula that returns a value into one that crashes: here `f = [1 0]`
    returns `0`, but `[11 [t [0 0]] f]` crashes because the clue `[0 0]` does. -/
theorem hint_not_transparent (tag a : Noun) :
    NockEval a (cell (atom 1) (atom 0)) (.val (atom 0)) ∧
    NockEval a (cell (atom 11) (cell (cell tag (cell (atom 0) (atom 0)))
      (cell (atom 1) (atom 0)))) .exit :=
  ⟨NockEval.op1, NockEval.op11_dyn_crash (NockEval.op0_crash (fasO_zero a))⟩

-- ---------------------------------------------------------------------------
-- Consequences for the composition theorem
-- ---------------------------------------------------------------------------

/-- The composition theorem survives any dynamic hint whose clue produces a
    value on the subject. -/
theorem composition_hint (t : Term) (tag c S : Noun) {r : Noun}
    (hc : NockEval S c (.val r)) (o : Outcome) :
    NockEval S (cell (atom 11) (cell (cell tag c) (NT t))) o ↔ CEval t S o :=
  (hint_dynamic_transparent tag c S (NT t) hc o).trans (composition_term t S o)

/-- A constant clue `[1 k]` always produces a value, so the composition theorem
    survives such a hint unconditionally — values, crashes, and divergence. -/
theorem composition_hint_const (t : Term) (tag k S : Noun) (o : Outcome) :
    NockEval S (cell (atom 11) (cell (cell tag (cell (atom 1) k)) (NT t))) o ↔
      CEval t S o :=
  composition_hint t tag (cell (atom 1) k) S NockEval.op1 o

theorem composition_hint_diverges (t : Term) (tag c S : Noun) {r : Noun}
    (hc : NockEval S c (.val r)) :
    Diverges S (cell (atom 11) (cell (cell tag c) (NT t))) ↔ CDiverges t S :=
  (hint_dynamic_diverges tag c S (NT t) hc).trans (composition_diverges t S)
