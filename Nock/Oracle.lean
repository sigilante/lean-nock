import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Comp
import Nock.Term
import Nock.Notation

namespace Nock
open Noun

/-!
# Class D oracle — fueled model of the C semantics

**Nothing in the proof chain may import this module.**  `Main.lean` may.

The quarantine invariant is **import direction**, not import disjointness: this
module legitimately imports `Word`, `phi`, `cw` from `Nock.Comp`, and the
proofs import those too.  What must never happen is a proof-chain module
importing *this* one.  Same discipline as `Nock/RuntimeBridge.lean`:

    grep -rn "import Nock.Oracle" Nock/     # only Main.lean, never Nock/*.lean

`CsemF` is a **fueled** interpreter of the C side.  Its `none` means *fuel
exhausted only* — never a semantic verdict.  It exists to put the manuscript's
Class D compilation schemas on trial *before* they are proved, exactly as the
280-noun sweep did for Tables A and B and as the 48-subject sweep did for
Table C.  It is not, and must never become, part of any theorem's trust base.

`Term` and `NT` now live in `Nock/Term.lean` (proof chain); this module imports
them.  That is the direction the quarantine permits: the oracle may import the
proof chain, never the reverse.

## Verdict of the trial

676 runs (26 programs × 26 subjects) at five fuel schedules from
`(nockF 500, CsemF 200)` to `(nockF 60000, CsemF 20000)`.  At every schedule:
**0 mismatches, 0 asymmetries.**  See `TABLE-REPORT.md` §D.

The schemas are therefore **confirmed (oracle)**, not **discharged (kernel)**.
Discharge awaits the Phase 4b simulation-pair theorems.
-/

namespace Oracle

/-- §4 of DEFENDANT-CLASSD — the fueled C-side model, transcribed from the C
    listings.  `none` = fuel exhausted, never a semantic verdict.  Loobean means
    exactly `atom 0` or `atom 1`; everything else crashes. -/
def CsemF : Nat → Term → Noun → Option Outcome
  | 0, _, _ => none
  | _+1, .nil, S => some (.val S)
  | k+1, .seq w p, S =>
      match cw w S with
      | .val S' => CsemF k p S'
      | .exit   => some .exit
  | k+1, .ifte q₁ q₂ p, S =>
      match S with
      | atom _            => some .exit                -- pop on an atom stack bails
      | cell (atom 0) S'  =>
          match CsemF k q₁ S' with
          | none => none | some .exit => some .exit
          | some (.val S'') => CsemF k p S''
      | cell (atom 1) S'  =>
          match CsemF k q₂ S' with
          | none => none | some .exit => some .exit
          | some (.val S'') => CsemF k p S''
      | cell _ _          => some .exit                -- non-loobean flag
  | k+1, .while t b p, S =>
      match CsemF k t S with
      | none => none
      | some .exit => some .exit
      | some (.val T) =>
        match T with
        | atom _           => some .exit               -- no flag to pop
        | cell (atom 0) S' =>
            match CsemF k b S' with
            | none => none | some .exit => some .exit
            | some (.val S'') => CsemF k (.while t b p) S''
        | cell (atom 1) S' => CsemF k p S'             -- exit; run the continuation
        | cell _ _         => some .exit               -- non-loobean flag

-- ---------------------------------------------------------------------------
-- The trial harness
-- ---------------------------------------------------------------------------

def prog (ws : List Word) (k : Term) : Term := ws.foldr Term.seq k

/-- Test generators.  Note `T_eq` is net-0 arity: it *consumes* the stack top,
    so it is not a divergence generator.  `T_dupdupEq` is net-+1 and preserves
    the stack, so `while(T_dupdupEq, ε)` diverges.  See TABLE-REPORT.md §D. -/
def T_celq     : Term := prog [.dup, .celq] .nil
def T_eq       : Term := prog [.dup, .eq] .nil
def T_incEq    : Term := prog [.dup, .inc, .eq] .nil
def T_dupdupEq : Term := prog [.dup, .dup, .eq] .nil
def T_drop     : Term := prog [.drop] .nil
def T_cellFlag : Term := prog [.dup, .dup, .cons] .nil
def T_atom2Flag: Term := prog [.dup, .inc, .inc] .nil

def A0 : Noun := atom 7
def A1 : Noun := cell (atom 1) (atom 2)
def A2 : Noun := cell A1 (atom 3)
def A3 : Noun := cell A2 (atom 4)
def stk (a : Noun) : Noun := cell a (atom 0)
def stk2 (a : Noun) (c : Nat) : Noun := cell a (cell (atom c) (atom 0))

/-- The iteration-exact body: descend the spine, decrement a counter via the
    Class C `dec` word.  An off-by-one on either side flips a crash into a
    value, so this probe is fuel-independent. -/
def bodyCount : Term := prog [.head, .swap, .dec, .swap] .nil

def progs : List (String × Term) :=
  [("P1",  .while T_celq (prog [.head] .nil) .nil),
   ("P2",  .ifte (prog [.celq] .nil) (prog [.dup] .nil) .nil),
   ("P3a", .ifte .nil .nil .nil),
   ("P3b", .while T_drop .nil .nil),
   ("P4",  .while T_eq (prog [.head] .nil) .nil),
   ("P4'", .while T_celq bodyCount .nil),
   ("P5m", .while T_eq .nil .nil),
   ("P5x", .while T_dupdupEq .nil .nil),
   ("P5y", .while T_dupdupEq (prog [.dup, .drop] .nil) .nil),
   ("P6a", .while T_celq (.while T_celq (prog [.head] .nil) .nil) .nil),
   ("P6b", .ifte (.while T_celq (prog [.head] .nil) .nil) .nil .nil),
   ("P6c", .while T_celq (prog [.head] .nil) (prog [.celq] .nil)),
   ("P6d", .ifte (prog [.celq] .nil) (prog [.dup] .nil) (prog [.celq] .nil)),
   ("P6e", .while T_incEq .nil (prog [.celq] .nil)),
   ("P6f", .while T_celq (prog [.head] .nil) (prog [.inc] .nil)),
   ("P6g", .while T_cellFlag .nil .nil),
   ("P6h", .while T_atom2Flag .nil .nil),
   ("P7",  .while T_eq (prog [.head] .nil) (prog [.celq] .nil)),
   ("P7'", .while T_celq bodyCount (prog [.inc] .nil)),
   ("P8",  .while T_celq (prog [.head] .nil) (prog [.dup, .celq] .nil)),
   ("P9",  .ifte (.while T_celq (prog [.head] .nil) .nil) (prog [.drop] .nil) (prog [.celq] .nil)),
   ("P10", .while T_celq (.ifte (prog [.head] .nil) (prog [.head] .nil) .nil) .nil),
   ("P11", .while (.ifte (prog [.dup,.celq] .nil) (prog [.dup,.celq] .nil) .nil)
                  (prog [.head] .nil) .nil),
   ("P12", prog [.dup, .celq, .drop] .nil),
   ("P13", .while T_celq (prog [.head] .nil) (prog [.dec] .nil)),
   ("P14", .ifte .nil (prog [.dec] .nil) (prog [.inc] .nil))]

def subjects : List Noun :=
  [atom 0, atom 1, atom 2, atom 9,
   cell (atom 0) (atom 0), cell (atom 1) (atom 0), cell (atom 2) (atom 0),
   cell (atom 0) (atom 5), cell (atom 1) (cell (atom 6) (atom 0)),
   stk A0, stk A1, stk A2, stk A3,
   cell A1 (cell (atom 3) (atom 0)), cell A2 (cell (atom 0) (atom 0)),
   stk2 A0 0, stk2 A1 0, stk2 A1 1, stk2 A2 1, stk2 A2 2,
   stk2 A3 0, stk2 A3 2, stk2 A3 3, stk2 A3 5,
   cell (cell (atom 1) (atom 2)) (cell (cell (atom 3) (atom 4)) (atom 0)),
   cell (atom 3) (cell (atom 4) (cell (atom 5) (atom 0)))]

inductive Cls | agree | mismatch | asym | bothNone
  deriving DecidableEq, Repr

def classify (l r : Option Outcome) : Cls :=
  match l, r with
  | none,   none   => .bothNone
  | some a, some b => if a = b then .agree else .mismatch
  | _,      _      => .asym

/-- `(agree, bothNone, mismatch, asymmetric)` over the full 676-run cross
    product at the given fuel schedule.  A conviction is any nonzero entry in
    the last two components. -/
def sweep (nf cf : Nat) : Nat × Nat × Nat × Nat :=
  let rs := progs.flatMap fun (_, t) => subjects.map fun S =>
    classify (nockF nf S (NT t)) (CsemF cf t S)
  ((rs.filter (· = .agree)).length, (rs.filter (· = .bothNone)).length,
   (rs.filter (· = .mismatch)).length, (rs.filter (· = .asym)).length)

-- Regression check: the acquittal, re-run at build time.
-- Expect (632, 44, 0, 0) — the 44 two-sided `none` are P5x and P5y, which
-- are designed to diverge, and do so on both sides at every fuel tried.
#eval sweep 4000 1500

end Oracle

end Nock
