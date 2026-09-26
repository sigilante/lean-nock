import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.HoonOne
import Nock.Shim
import Nock.Term
import Nock.CEval
import Nock.Backward
import Nock.Composition
open Noun

/-!
# Deployment: a compiled term packaged as a Hoon gate

Runtimes dispatch jets on cores `[battery payload]`, firing arm 2 with the gate
sample at axis 6.  `Λ`'s convention is a stack `[top rest]`.  This module
packages any compiled term as a one-armed gate core and proves the packaging
preserves the composition theorem on values, crashes, and divergence.

This is the converse direction to `Nock.Shim`: `liftGate` calls a Hoon gate
from inside a stack program, while `gateArm` exposes a stack program *as* a
Hoon gate.

The arm, fired against the core `[gateArm t [sam ctx]]`, is

    [7 [[0 6] [1 0]] [7 Λ_N(t) [0 2]]]

- **load** `[[0 6] [1 0]]`: build the initial stack `[sam ~]` from the sample;
- run the compiled term;
- **unload** `[0 2]`: return the top of the final stack.

The shim is opcode-0 plumbing, one autocons, and two opcode-7 compositions; no
loop, so it adds no proof obligation beyond the lemmas below.  The C side's
load/unload must implement the same shim — that is `CGate`.  Note that unload
crashes when the final stack is empty (an atom): `unloadOut`.
-/

private theorem no_val_exit {s f v} (hv : NockEval s f (.val v))
    (he : NockEval s f .exit) : False := by
  have := NockEval.deterministic hv he; simp at this

private theorem det_val {s f} {u v : Noun} (h1 : NockEval s f (.val u))
    (h2 : NockEval s f (.val v)) : u = v := by
  have := NockEval.deterministic h1 h2; simpa using this

-- ---------------------------------------------------------------------------
-- Definitions
-- ---------------------------------------------------------------------------

/-- Load: `[[0 6] [1 0]]`, the sample pushed onto the empty stack. -/
def gateLoad : Noun := cell (cell (atom 0) (atom 6)) (cell (atom 1) (atom 0))

/-- Unload: `[0 2]`, the top of the final stack. -/
def gateUnload : Noun := cell (atom 0) (atom 2)

/-- The single arm (hence the whole battery) of the gate emitted for `t`. -/
def gateArm (t : Term) : Noun :=
  cell (atom 7) (cell gateLoad (cell (atom 7) (cell (NT t) gateUnload)))

/-- The C side's unload: return the top of the final stack; an empty (atom)
    stack has no top and crashes. -/
def unloadOut : Outcome → Outcome
  | .val (cell top _) => .val top
  | .val (atom _)     => .exit
  | .exit             => .exit

/-- The C side of a gate call: load `[sam ~]`, run the term, unload. -/
def CGate (t : Term) (sam : Noun) (o : Outcome) : Prop :=
  ∃ oS, CEval t (cell sam (atom 0)) oS ∧ unloadOut oS = o

/-- C-side divergence of a gate call. -/
def CGateDiverges (t : Term) (sam : Noun) : Prop := ∀ o, ¬ CGate t sam o

-- ---------------------------------------------------------------------------
-- Shim lemmas
-- ---------------------------------------------------------------------------

theorem gateLoad_eval (bat sam ctx : Noun) :
    NockEval (mkGate bat sam ctx) gateLoad (.val (cell sam (atom 0))) :=
  NockEval.autocons (NockEval.op0 (fasO_six bat sam ctx)) NockEval.op1

theorem gateUnload_eval (S : Noun) :
    NockEval S gateUnload (unloadOut (.val S)) := by
  cases S with
  | atom n   => exact NockEval.op0_crash (fasO_two_atom n)
  | cell a b => exact NockEval.op0 (fasO_head a b)

/-- **Battery identity.**  The battery of the emitted core is `gateArm t`,
    whatever the sample and context: the dispatch key is a function of the
    source term alone. -/
theorem gate_battery (t : Term) (sam ctx : Noun) :
    fasO (atom 2) (mkGate (gateArm t) sam ctx) = some (gateArm t) :=
  fasO_head _ _

-- ---------------------------------------------------------------------------
-- The gate theorem
-- ---------------------------------------------------------------------------

theorem gate_sound {t : Term} {sam ctx : Noun} {oS : Outcome}
    (hc : CEval t (cell sam (atom 0)) oS) :
    NockEval (mkGate (gateArm t) sam ctx) (gateArm t) (unloadOut oS) := by
  have hN := ceval_sound hc
  refine NockEval.op7 (gateLoad_eval _ sam ctx) ?_
  cases oS with
  | val S' => exact NockEval.op7 hN (gateUnload_eval S')
  | exit   => exact NockEval.op7_crash hN

theorem gate_complete {t : Term} {sam ctx : Noun} {o : Outcome}
    (h : NockEval (mkGate (gateArm t) sam ctx) (gateArm t) o) : CGate t sam o := by
  have hload := gateLoad_eval (gateArm t) sam ctx
  cases h with
  | crash_malformed hm => simp [Malformed, gateArm] at hm
  | op7_crash hl => exact (no_val_exit hload hl).elim
  | op7 hl hr =>
    have := det_val hl hload; subst this
    cases hr with
    | crash_malformed hm => simp [Malformed] at hm
    | op7_crash hn => exact ⟨.exit, nockeval_complete hn, rfl⟩
    | op7 hn hu =>
      exact ⟨_, nockeval_complete hn,
        NockEval.deterministic (gateUnload_eval _) hu⟩

/-- **The gate theorem.**  Packaging a compiled term as a one-armed gate core
    preserves agreement with the C model (with the same load/unload shim), on
    values and crashes. -/
theorem gate_term (t : Term) (sam ctx : Noun) (o : Outcome) :
    NockEval (mkGate (gateArm t) sam ctx) (gateArm t) o ↔ CGate t sam o := by
  constructor
  · exact gate_complete
  · rintro ⟨oS, hc, rfl⟩; exact gate_sound hc

/-- ... and on divergence. -/
theorem gate_diverges (t : Term) (sam ctx : Noun) :
    Diverges (mkGate (gateArm t) sam ctx) (gateArm t) ↔ CGateDiverges t sam := by
  simp only [Diverges, CGateDiverges, gate_term]

/-- Firing arm 2 of the emitted core, `[9 2 0 1]` — the way a runtime invokes
    a gate it holds. -/
theorem gate_fire (t : Term) (sam ctx : Noun) (o : Outcome) :
    NockEval (mkGate (gateArm t) sam ctx)
      (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) o ↔ CGate t sam o := by
  rw [← gate_term]
  constructor
  · intro h
    cases h with
    | crash_malformed hm => simp [Malformed] at hm
    | op9_crash hc => exact (no_val_exit (NockEval.op0 (fasO_one _)) hc).elim
    | op9_badaxis hc hnone =>
      have := det_val hc (NockEval.op0 (fasO_one _)); subst this
      rw [gate_battery] at hnone; simp at hnone
    | op9 hc harm hbody =>
      have := det_val hc (NockEval.op0 (fasO_one _)); subst this
      rw [gate_battery] at harm; cases harm
      exact hbody
  · intro h
    exact NockEval.op9 (NockEval.op0 (fasO_one _)) (gate_battery t sam ctx) h

/-- A Hoon-style call with argument `arg`, `[9 2 [10 [6 [1 arg]] [0 1]]]`
    (via `callGate_gate_eval`), inherits the gate theorem. -/
theorem gate_call (t : Term) (sam ctx arg : Noun) {oS : Outcome}
    (hc : CEval t (cell arg (atom 0)) oS) :
    NockEval (mkGate (gateArm t) sam ctx)
      (C [atom 9, atom 2,
          C [atom 10, C [atom 6, C [atom 1, arg]], C [atom 0, atom 1]]])
      (unloadOut oS) :=
  callGate_gate_eval (gateArm t) sam ctx arg (gate_sound (ctx := ctx) hc)
