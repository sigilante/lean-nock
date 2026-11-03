import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Shim
import Nock.Gate
import Nock.Rec

namespace Nock
open Noun

/-!
# Deployment of programs with named definitions

`Nock.Gate` packages a call-free term as a one-armed gate core.  This module
does the same for a whole program — a definition table plus `main` — so the
deployment theorems cover recursion too.  The arm is the same shim around the
program formula `progF D m`:

    [7 [[0 6] [1 0]] [7 progF(D, m) [0 2]]]

The shim argument is independent of what runs inside it, so it is proved once
for an arbitrary formula `F` with an exact C-side characterization, then
instantiated with `program_term`.
-/

private theorem no_val_exit {s f v} (hv : NockEval s f (.val v))
    (he : NockEval s f .exit) : False := by
  have := NockEval.deterministic hv he; simp at this

private theorem det_val {s f} {u v : Noun} (h1 : NockEval s f (.val u))
    (h2 : NockEval s f (.val v)) : u = v := by
  have := NockEval.deterministic h1 h2; simpa using this

/-- The gate arm around an arbitrary stack formula `F`. -/
def gateArmOf (F : Noun) : Noun :=
  cell (atom 7) (cell gateLoad (cell (atom 7) (cell F gateUnload)))

/-- The shim, for any formula `F` whose outcomes are exactly `R`'s. -/
private theorem gateArmOf_term {F : Noun} {R : Noun → Outcome → Prop}
    (hR : ∀ S o, NockEval S F o ↔ R S o) (sam ctx : Noun) (o : Outcome) :
    NockEval (mkGate (gateArmOf F) sam ctx) (gateArmOf F) o ↔
      ∃ oS, R (cell sam (atom 0)) oS ∧ unloadOut oS = o := by
  have hload := gateLoad_eval (gateArmOf F) sam ctx
  constructor
  · intro h
    cases h with
    | crash_malformed hm => simp [Malformed, gateArmOf] at hm
    | op7_crash hl => exact (no_val_exit hload hl).elim
    | op7 hl hr =>
      have := det_val hl hload; subst this
      cases hr with
      | crash_malformed hm => simp [Malformed] at hm
      | op7_crash hn => exact ⟨.exit, (hR _ _).1 hn, rfl⟩
      | op7 hn hu =>
        exact ⟨_, (hR _ _).1 hn, NockEval.deterministic (gateUnload_eval _) hu⟩
  · rintro ⟨oS, hc, rfl⟩
    have hN := (hR _ _).2 hc
    refine NockEval.op7 hload ?_
    cases oS with
    | val S' => exact NockEval.op7 hN (gateUnload_eval S')
    | exit   => exact NockEval.op7_crash hN

/-- The gate arm emitted for a whole program. -/
def gateArmP (D : List RTerm) (m : RTerm) : Noun := gateArmOf (progF D m)

/-- The C side of a program's gate call: load `[sam ~]`, run `main`, unload. -/
def CGateP (D : List RTerm) (m : RTerm) (sam : Noun) (o : Outcome) : Prop :=
  ∃ oS, REval D m (cell sam (atom 0)) oS ∧ unloadOut oS = o

/-- **The program gate theorem.**  A program with named definitions, packaged
    as a one-armed gate core, agrees with the C model on values and crashes. -/
theorem gate_program (D : List RTerm) (m : RTerm) (sam ctx : Noun) (o : Outcome) :
    NockEval (mkGate (gateArmP D m) sam ctx) (gateArmP D m) o ↔ CGateP D m sam o :=
  gateArmOf_term (program_term D m) sam ctx o

/-- ... and on divergence. -/
theorem gate_program_diverges (D : List RTerm) (m : RTerm) (sam ctx : Noun) :
    Diverges (mkGate (gateArmP D m) sam ctx) (gateArmP D m) ↔
      ∀ o, ¬ CGateP D m sam o := by
  simp only [Diverges, gate_program]

/-- Battery identity: the dispatch key is a function of the program alone. -/
theorem gate_program_battery (D : List RTerm) (m : RTerm) (sam ctx : Noun) :
    fasO (atom 2) (mkGate (gateArmP D m) sam ctx) = some (gateArmP D m) :=
  fasO_head _ _

/-- Firing arm 2 of the emitted core, `[9 2 0 1]`. -/
theorem gate_program_fire (D : List RTerm) (m : RTerm) (sam ctx : Noun) (o : Outcome) :
    NockEval (mkGate (gateArmP D m) sam ctx)
      (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) o ↔ CGateP D m sam o := by
  rw [← gate_program]
  constructor
  · intro h
    cases h with
    | crash_malformed hm => simp [Malformed] at hm
    | op9_crash hc => exact (no_val_exit (NockEval.op0 (fasO_one _)) hc).elim
    | op9_badaxis hc hnone =>
      have := det_val hc (NockEval.op0 (fasO_one _)); subst this
      rw [gate_program_battery] at hnone; simp at hnone
    | op9 hc harm hbody =>
      have := det_val hc (NockEval.op0 (fasO_one _)); subst this
      rw [gate_program_battery] at harm; cases harm
      exact hbody
  · intro h
    exact NockEval.op9 (NockEval.op0 (fasO_one _)) (gate_program_battery D m sam ctx) h

end Nock
