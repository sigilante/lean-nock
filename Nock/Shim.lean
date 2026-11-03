import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.HoonOne
import Nock.DecDiverges
import Nock.Comp

namespace Nock
open Noun

/-!
# The gate shim

A Hoon gate is a core `[battery [sample context]]`; a `Word` operates on a
stack `[top rest]`.  `liftGate` bridges them: build the core with the stack top
as sample, fire arm 2, cons the result back onto `rest`.

The point of this module is the pair at the bottom.  `liftGate` is **strict in
the gate's outcome** — the result has to be consed onto `rest`, so there is
nothing to cons if the gate never produces anything.  Hoon's compiled `++dec`
diverges on a cell argument (`dec_cell_diverges`), so its naive lift diverges
too, and is therefore *provably not denotable as a `Word`*.

That is the guard-emission rule doing its job.  `phi .dec` is denotable
precisely because Λ emits domain guards ahead of the partial operation — and,
per `TABLE-REPORT.md` §C, emits them at the right axis.  The model is not
failing to accommodate `decBat`; it is correctly refusing an unguarded formula.
-/

-- Determinism-pruning idiom (local; the copies in DecDiverges are private).

private theorem no_val_exit {s f v} (hv : NockEval s f (.val v))
    (he : NockEval s f .exit) : False := by
  have := NockEval.deterministic hv he; simp at this

private theorem det_val {s f} {u v : Noun} (h1 : NockEval s f (.val u))
    (h2 : NockEval s f (.val v)) : u = v := by
  have := NockEval.deterministic h1 h2; simpa using this

-- ---------------------------------------------------------------------------
-- Definitions
-- ---------------------------------------------------------------------------

/-- A Hoon gate core: `[battery [sample context]]`. -/
def mkGate (bat sam ctx : Noun) : Noun := cell bat (cell sam ctx)

/-- Lift a gate to a stack word.  On `S = [a rest]`: build `[bat [a ctx]]`,
    fire arm 2, cons the result onto `rest`.

      [[9 2 [[1 bat] [[0 2] [1 ctx]]]] [0 3]] -/
def liftGate (bat ctx : Noun) : Noun :=
  cell (cell (atom 9) (cell (atom 2)
         (cell (cell (atom 1) bat) (cell (cell (atom 0) (atom 2)) (cell (atom 1) ctx)))))
       (cell (atom 0) (atom 3))

/-- How a gate's outcome lifts to a stack outcome. -/
def liftOut (r : Noun) : Outcome → Outcome
  | .val v => .val (cell v r)
  | .exit  => .exit

/-- The core-building subformula of `liftGate`. -/
private def gateBuild (bat ctx : Noun) : Noun :=
  cell (cell (atom 1) bat) (cell (cell (atom 0) (atom 2)) (cell (atom 1) ctx))

private theorem liftGate_parts (bat ctx : Noun) :
    liftGate bat ctx =
      cell (cell (atom 9) (cell (atom 2) (gateBuild bat ctx))) (cell (atom 0) (atom 3)) := rfl

/-- On a stack `[a rest]`, the build subformula evaluates to the gate core. -/
private theorem gateBuild_eval (bat ctx a r : Noun) :
    NockEval (cell a r) (gateBuild bat ctx) (.val (mkGate bat a ctx)) :=
  NockEval.autocons NockEval.op1
    (NockEval.autocons (NockEval.op0 (fasO_head a r)) NockEval.op1)

-- ---------------------------------------------------------------------------
-- The calling theorem
-- ---------------------------------------------------------------------------

/-- **The calling theorem.**  Outcome-polymorphic: it carries the value case and
    the crash case at once, because `liftGate`'s autocons is strict in its left
    operand and `op9` passes its tail outcome through unchanged. -/
theorem liftGate_correct (bat ctx a r : Noun) (o : Outcome)
    (h : NockEval (mkGate bat a ctx) bat o) :
    NockEval (cell a r) (liftGate bat ctx) (liftOut r o) := by
  have hleft : NockEval (cell a r)
      (cell (atom 9) (cell (atom 2) (gateBuild bat ctx))) o :=
    NockEval.op9 (gateBuild_eval bat ctx a r) (fasO_head bat (cell a ctx)) h
  cases o with
  | val v => exact NockEval.autocons hleft (NockEval.op0 (fasO_tail a r))
  | exit  => exact NockEval.autocons_crashL hleft

-- ---------------------------------------------------------------------------
-- Hoon's `++dec`, naively lifted: agrees on the total domain, diverges off it
-- ---------------------------------------------------------------------------

theorem liftGate_decBat_agrees (n : Nat) (r ctx : Noun) :
    NockEval (cell (atom (n + 1)) r) (liftGate decBat ctx) (.val (cell (atom n) r)) :=
  liftGate_correct decBat ctx (atom (n + 1)) r _ (dec_correct n ctx)

theorem liftGate_decBat_underflow (r ctx : Noun) :
    NockEval (cell (atom 0) r) (liftGate decBat ctx) .exit :=
  liftGate_correct decBat ctx (atom 0) r _ (dec_underflow ctx)

/-- On a cell argument the naive lift **diverges**: `liftGate` is strict in the
    gate's outcome, and `decBat` has none. -/
theorem liftGate_decBat_cell_diverges (x y r ctx : Noun) :
    Diverges (cell (cell x y) r) (liftGate decBat ctx) := by
  -- First: the left operand alone admits no derivation.
  have hleft : ∀ o, ¬ NockEval (cell (cell x y) r)
      (cell (atom 9) (cell (atom 2) (gateBuild decBat ctx))) o := by
    intro o h
    cases h with
    | crash_malformed hm => simp [Malformed] at hm
    | op9_crash hc => exact no_val_exit (gateBuild_eval decBat ctx (cell x y) r) hc
    | @op9_badaxis _ _ _ core hc hnone =>
      have hcore : core = mkGate decBat (cell x y) ctx :=
        det_val hc (gateBuild_eval decBat ctx (cell x y) r)
      subst hcore
      rw [show fasO (atom 2) (mkGate decBat (cell x y) ctx) = some decBat from
        fasO_head _ _] at hnone
      simp at hnone
    | @op9 _ _ _ core arm _ hc harm hbody =>
      have hcore : core = mkGate decBat (cell x y) ctx :=
        det_val hc (gateBuild_eval decBat ctx (cell x y) r)
      subst hcore
      rw [show fasO (atom 2) (mkGate decBat (cell x y) ctx) = some decBat from
        fasO_head _ _] at harm
      have harm' : arm = decBat := by simpa using harm.symm
      subst harm'
      exact dec_cell_diverges x y ctx _ hbody
  -- Then: every constructor of the outer autocons needs the left operand.
  intro o h
  rw [liftGate_parts] at h
  cases h with
  | crash_malformed hm => simp [Malformed] at hm
  | autocons h1 _ => exact hleft _ h1
  | autocons_crashL h1 => exact hleft _ h1
  | autocons_crashR h1 _ => exact hleft _ h1

/-- **The refusal.**  Hoon's `++dec`, naively lifted, is not denotable as a
    `Word`.  `phi .dec` is denotable precisely because Λ emitted the domain
    guards.  The model is not failing to accommodate `decBat`; it is correctly
    refusing an unguarded formula. -/
theorem liftGate_decBat_not_a_word (x y r ctx : Noun) :
    ¬ ∃ w : Word, phi w = liftGate decBat ctx :=
  not_denotable_of_diverges (liftGate_decBat_cell_diverges x y r ctx)

end Nock
