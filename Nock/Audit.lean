import Lean
import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.HoonOne
import Nock.DecDiverges
import Nock.Comp
import Nock.Shim
import Nock.Term
import Nock.CEval
import Nock.Backward
import Nock.Composition
import Nock.Hint
import Nock.Gate
import Nock.Rec
import Nock.GateRec
import Nock.Mock
import Nock.Order

/-!
# The audit manifest — build-enforced

Two jobs, both structural rather than clerical:

1. **Axiom footprints are checked at `lake build` time.**  `#print axioms` only
   *prints*; a drifting footprint would scroll past in the log.  The commands
   below `throwError`, so a regression **fails the build**.

2. **The manifest is the freeze list.**  Every name here is cited (or citable)
   by the companion manuscript, so it is API.  A rename or deletion fails
   elaboration on the spot.

## Why this exists

`decg_succ` — a *private* lemma in a Class C leaf proof — once discharged
`atom 0 ≠ atom (n+1)` with `simp`, which pulled in `Classical.choice`.  That
propagated up through `leaf_correct` into `composition`, silently weakening a
footprint the project had already published.  Nothing broke; a printed claim
merely became false.

Adding a `Word` constructor rebuilds `leaf_correct`'s proof term and
re-derives every downstream footprint.  The next planned work adds words.  So
the audit lands **before** the next word does: this is precisely the moment
when relying on vigilance is relying on the thing we have watched fail.
-/

open Lean Elab Command

namespace Nock.Audit

/-- Lean 4's standard foundations.  Nothing in the proof chain may exceed this. -/
def allowedProofChain : List Name := [``propext, ``Quot.sound]

/-- The runtime/prover bridge additionally trusts the compiler, via
    `native_decide`.  That is the entire content of the quarantine. -/
def allowedBridge : List Name :=
  [``propext, ``Quot.sound, `Lean.ofReduceBool, `Lean.trustCompiler]

private def auditAgainst (allowed : List Name) (ids : Array Ident) : CommandElabM Unit := do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError
        "AUDIT FAILURE for {n}\n  \
         disallowed axioms: {bad.toList}\n  \
         full footprint:    {axs.toList}\n  \
         allowed here:      {allowed}\n\
         If this is an intended change, update Nock/Audit.lean deliberately — \
         do not widen the allow-list to make a build pass."

/-- Fails the build unless every named constant's axiom footprint is contained
    in `{propext, Quot.sound}`.  Also catches `sorryAx`, which is not allowed. -/
elab "#audit_clean " ids:ident+ : command => auditAgainst allowedProofChain ids

/-- As `#audit_clean`, but additionally tolerating the two compiler axioms that
    `native_decide` introduces.  Only `Nock/RuntimeBridge.lean` may use this. -/
elab "#audit_bridge " ids:ident+ : command => auditAgainst allowedBridge ids

end Nock.Audit

open Nock.Audit

-- ---------------------------------------------------------------------------
-- THE MANIFEST.  Every name below is API: cited or citable by the manuscript.
-- ---------------------------------------------------------------------------

-- Primitives and the lemma library
#audit_clean wut_atom wut_cell lusO_atom lusO_cell tisN_refl tisN_neq
#audit_clean tisN_cell_atom tisN_atom_cell
#audit_clean fasO_one fasO_head fasO_tail fasO_zero
#audit_clean fasO_rec_even fasO_rec_odd
#audit_clean fasO_four fasO_five fasO_six fasO_seven
#audit_clean haxO_one haxO_zero haxO_rec_even haxO_rec_odd
#audit_clean haxO_two haxO_three haxO_six

-- Phase 2: the fuel interpreter, determinism, divergence
#audit_clean nockF_sound nockF_mono nockF_complete
#audit_clean NockEval.deterministic diverges_iff_fuel

-- Phase 3: Hoon's ++dec, ++add, ++sub
#audit_clean callGate_gate_eval
#audit_clean dec_loop_inv dec_correct dec_underflow
#audit_clean add_correct sub_correct

-- Phase 3.5: dec's complete ⊥ profile
#audit_clean dec_loop_cell_diverges dec_cell_diverges

-- Phase 4a/4c: words, leaf contracts, composition over the free monoid
#audit_clean leaf_correct composition composition_agree
#audit_clean word_crash_total not_denotable_of_diverges

-- The gate shim, and the excluded witness
#audit_clean liftGate_correct liftGate_decBat_agrees liftGate_decBat_underflow
#audit_clean liftGate_decBat_cell_diverges liftGate_decBat_not_a_word

-- Phase 4b: the Class D composition theorem
#audit_clean NT_ofProg ceval_sound nockeval_complete ceval_det
#audit_clean composition_term composition_diverges
#audit_clean ceval_ofProg composition_ofProg

-- Deployment: hint transparency (opcode 11, `%fast` registration)
#audit_clean hint_static_transparent hint_static_diverges
#audit_clean hint_dynamic_transparent hint_dynamic_diverges hint_not_transparent
#audit_clean composition_hint composition_hint_const composition_hint_diverges

-- Deployment: the term packaged as a one-armed gate core
#audit_clean gateLoad_eval gateUnload_eval gate_battery
#audit_clean gate_sound gate_complete gate_term gate_diverges gate_fire gate_call

-- The canonical count-up `dec`, unguarded: its complete profile
#audit_clean countUp_correct countUp_loop_diverges countUp_diverges
#audit_clean countUp_zero_diverges countUp_cell_diverges

-- Named definitions: self- and mutually recursive words
#audit_clean fasO_armAx reval_sound rback_fuel
#audit_clean rcomposition rcomposition_diverges program_term program_diverges
#audit_clean reval_blk_nil program_ofTerm

-- `while` as a recursive definition
#audit_clean while_as_call while_as_program

-- Deployment of programs with named definitions
#audit_clean gate_program gate_program_diverges gate_program_battery gate_program_fire

-- `+mock`: the two-valued contract is unsound, the three-valued one sound
#audit_clean three_valued_sound three_valued_mock
#audit_clean natDec_twoValued natDec_not_threeValued two_valued_unsound
#audit_clean word_jet_sound

-- Evaluation order, pinned to Vere and NockVM (opcode 10: tree before patch)
#audit_clean order_autocons_diverges order_autocons_crashes
#audit_clean order_op2_diverges order_op2_crashes order_op5_diverges order_op5_crashes
#audit_clean order_op10_diverges order_op10_crashes order_op11_diverges order_op11_crashes
