import Nock.Basic
import Nock.Proofs
open Noun

/-!
# NockEval: Inductive Relational Semantics for Nock 4K

`NockEval subject formula outcome` holds iff running `formula` against
`subject` produces `outcome` according to the Nock 4K specification.

## Three-valued outcomes

Nock computations do one of three things: return a noun, crash, or diverge.
Only the first two are `Outcome` constructors:

- **value** — `Outcome.val n`
- **crash** — `Outcome.exit`
- **divergence** — *absence of a derivation*.  There is no constructor for
  it; `Diverges a f := ∀ o, ¬ NockEval a f o` (see `Nock.Fuel`).

An earlier version of this relation folded crashes into values, because the
primitives `fas`/`hax`/`lus`/`tis` handled crash arms with `panic!`, which
is `Inhabited.default = atom 0` in Lean's logic.  That made
`NockEval a [0 0] (atom 0)` derivable for every `a` — the relation
certified that a crashing axis lookup returns zero.  The `Option`-valued
primitives of `Nock.Basic` plus `Outcome.exit` close that hole.

## Evaluation order

Evaluation is **strict, in the order of Vere and NockVM**: left to right,
except that opcode 10 evaluates its tree `d` before its patch `c`.  A crash in
an earlier operand hides later operands, and so does a divergence.  The Nock
specification leaves this order open; it decides which bottom a formula
reaches when one operand crashes and another diverges (see `Nock.Order`).
The crash-propagation constructors below encode exactly this order; there are
deliberately no symmetric variants, which is what makes the relation
deterministic.

Tail-position subcomputations pass their `Outcome` through unchanged (the
`o` parameter).  Only an intermediate result that the rule itself consumes
needs a `.val` hypothesis plus a matching explicit crash constructor.

## Opcode readings

For opcode 6 (if-then-else) we give the high-level semantic reading
(test evaluates to loobean 0 → branch c; to 1 → branch d; anything else →
crash) rather than the macro expansion in the spec.  Equivalence to the
macro form is out of scope.

For opcode 9 (gate call) we unfold one step of the spec:
  *[a 9 b c] = *[*[a c] 2 [0 1] 0 b]
             = *[core /[b core]]     where core = *[a c]
which is the form all gate-call proofs actually use.

For opcode 11 (hint) both cases discard the hint:
  static  (*[a 11 t   c]  = *[a c])
  dynamic (*[a 11 [t c] d] = *[[*[a c] *[a d]] 0 3] = *[a d])
-/

/-- A Nock computation either produces a noun or crashes.  Divergence is
    modelled by the absence of a `NockEval` derivation, not by a constructor. -/
inductive Outcome
  | val  : Noun → Outcome
  | exit : Outcome
  deriving DecidableEq, Repr

/-- A formula is malformed — and so crashes immediately, whatever the
    subject — if it is a bare atom, or a cell whose opcode is unknown or
    whose argument has the wrong shape for that opcode. -/
def Malformed : Noun → Bool
  | atom _ => true                       -- atom formula crashes
  | cell (cell _ _) _ => false           -- autocons: always well-formed
  | cell (atom k) t =>
    match k, t with
    | 0, _ => false
    | 1, _ => false
    | 2, cell _ _ => false | 2, _ => true
    | 3, _ => false
    | 4, _ => false
    | 5, cell _ _ => false | 5, _ => true
    | 6, cell _ (cell _ _) => false | 6, _ => true
    | 7, cell _ _ => false | 7, _ => true
    | 8, cell _ _ => false | 8, _ => true
    | 9, cell _ _ => false | 9, _ => true
    | 10, cell (cell _ _) _ => false | 10, _ => true
    | 11, cell _ _ => false | 11, _ => true
    | _, _ => true                       -- opcode ≥ 12

inductive NockEval : Noun → Noun → Outcome → Prop where
  -- malformed formulas crash deterministically
  | crash_malformed {a f} (h : Malformed f = true) :
      NockEval a f .exit

  -- *[a [b c] d] = [*[a b c] *[a d]]   (auto-cons)
  | autocons {a b c fol r1 r2} :
      NockEval a (cell b c) (.val r1) →
      NockEval a fol (.val r2) →
      NockEval a (cell (cell b c) fol) (.val (cell r1 r2))
  | autocons_crashL {a b c fol} :
      NockEval a (cell b c) .exit →
      NockEval a (cell (cell b c) fol) .exit
  | autocons_crashR {a b c fol r1} :
      NockEval a (cell b c) (.val r1) →
      NockEval a fol .exit →
      NockEval a (cell (cell b c) fol) .exit

  -- *[a 0 b] = /[b a]                   (slot)
  | op0 {a fol r} (h : fasO fol a = some r) :
      NockEval a (cell (atom 0) fol) (.val r)
  | op0_crash {a fol} (h : fasO fol a = none) :
      NockEval a (cell (atom 0) fol) .exit

  -- *[a 1 b] = b                        (constant)
  | op1 {a fol} :
      NockEval a (cell (atom 1) fol) (.val fol)

  -- *[a 2 b c] = *[*[a b] *[a c]]       (eval)
  | op2 {a b c r1 r2 o} :
      NockEval a b (.val r1) →
      NockEval a c (.val r2) →
      NockEval r1 r2 o →
      NockEval a (cell (atom 2) (cell b c)) o
  | op2_crashL {a b c} :
      NockEval a b .exit →
      NockEval a (cell (atom 2) (cell b c)) .exit
  | op2_crashR {a b c r1} :
      NockEval a b (.val r1) →
      NockEval a c .exit →
      NockEval a (cell (atom 2) (cell b c)) .exit

  -- *[a 3 b] = ?*[a b]                  (cell test)
  | op3 {a fol r} :
      NockEval a fol (.val r) →
      NockEval a (cell (atom 3) fol) (.val (wut r))
  | op3_crash {a fol} :
      NockEval a fol .exit →
      NockEval a (cell (atom 3) fol) .exit

  -- *[a 4 b] = +*[a b]                  (increment; crashes on a cell)
  | op4 {a fol r v} :
      NockEval a fol (.val r) →
      lusO r = some v →
      NockEval a (cell (atom 4) fol) (.val v)
  | op4_cell {a fol r} :
      NockEval a fol (.val r) →
      lusO r = none →
      NockEval a (cell (atom 4) fol) .exit
  | op4_crash {a fol} :
      NockEval a fol .exit →
      NockEval a (cell (atom 4) fol) .exit

  -- *[a 5 b c] = =[*[a b] *[a c]]       (equality test)
  | op5 {a b c r1 r2} :
      NockEval a b (.val r1) →
      NockEval a c (.val r2) →
      NockEval a (cell (atom 5) (cell b c)) (.val (tisN r1 r2))
  | op5_crashL {a b c} :
      NockEval a b .exit →
      NockEval a (cell (atom 5) (cell b c)) .exit
  | op5_crashR {a b c r1} :
      NockEval a b (.val r1) →
      NockEval a c .exit →
      NockEval a (cell (atom 5) (cell b c)) .exit

  -- *[a 6 b c d]: semantic if-then-else; crashes on a non-loobean test
  | op6_then {a b c d o} :
      NockEval a b (.val (atom 0)) →
      NockEval a c o →
      NockEval a (cell (atom 6) (cell b (cell c d))) o
  | op6_else {a b c d o} :
      NockEval a b (.val (atom 1)) →
      NockEval a d o →
      NockEval a (cell (atom 6) (cell b (cell c d))) o
  | op6_nonloob {a b c d r} :
      NockEval a b (.val r) →
      r ≠ atom 0 → r ≠ atom 1 →
      NockEval a (cell (atom 6) (cell b (cell c d))) .exit
  | op6_crash {a b c d} :
      NockEval a b .exit →
      NockEval a (cell (atom 6) (cell b (cell c d))) .exit

  -- *[a 7 b c] = *[*[a b] c]            (compose)
  | op7 {a b c r1 o} :
      NockEval a b (.val r1) →
      NockEval r1 c o →
      NockEval a (cell (atom 7) (cell b c)) o
  | op7_crash {a b c} :
      NockEval a b .exit →
      NockEval a (cell (atom 7) (cell b c)) .exit

  -- *[a 8 b c] = *[[*[a b] a] c]        (push)
  | op8 {a b c r1 o} :
      NockEval a b (.val r1) →
      NockEval (cell r1 a) c o →
      NockEval a (cell (atom 8) (cell b c)) o
  | op8_crash {a b c} :
      NockEval a b .exit →
      NockEval a (cell (atom 8) (cell b c)) .exit

  -- *[a 9 b c] = *[core /[b core]]      (gate call, core = *[a c])
  | op9 {a b c core arm o} :
      NockEval a c (.val core) →
      fasO b core = some arm →
      NockEval core arm o →
      NockEval a (cell (atom 9) (cell b c)) o
  | op9_badaxis {a b c core} :
      NockEval a c (.val core) →
      fasO b core = none →
      NockEval a (cell (atom 9) (cell b c)) .exit
  | op9_crash {a b c} :
      NockEval a c .exit →
      NockEval a (cell (atom 9) (cell b c)) .exit

  -- *[a 10 [b c] d] = #[b *[a c] *[a d]]  (edit-at-axis)
  -- Evaluate the tree d first, then the patch c — the order of Vere and NockVM.
  | op10 {a b c d r1 r2 v} :
      NockEval a d (.val r2) →
      NockEval a c (.val r1) →
      haxO b r1 r2 = some v →
      NockEval a (cell (atom 10) (cell (cell b c) d)) (.val v)
  | op10_badaxis {a b c d r1 r2} :
      NockEval a d (.val r2) →
      NockEval a c (.val r1) →
      haxO b r1 r2 = none →
      NockEval a (cell (atom 10) (cell (cell b c) d)) .exit
  | op10_crashTree {a b c d} :
      NockEval a d .exit →
      NockEval a (cell (atom 10) (cell (cell b c) d)) .exit
  | op10_crashPatch {a b c d r2} :
      NockEval a d (.val r2) →
      NockEval a c .exit →
      NockEval a (cell (atom 10) (cell (cell b c) d)) .exit

  -- *[a 11 t c] = *[a c]                (static hint: atom tag, no-op)
  | op11_static {a t c o} :
      NockEval a c o →
      NockEval a (cell (atom 11) (cell (atom t) c)) o
  -- *[a 11 [t c] d]: the hint computation must produce a value, then d in tail
  | op11_dynamic {a t c d r1 o} :
      NockEval a c (.val r1) →
      NockEval a d o →
      NockEval a (cell (atom 11) (cell (cell t c) d)) o
  | op11_dyn_crash {a t c d} :
      NockEval a c .exit →
      NockEval a (cell (atom 11) (cell (cell t c) d)) .exit

-- ---------------------------------------------------------------------------
-- Basic sanity examples
-- ---------------------------------------------------------------------------

-- *[42 1 99] = 99
example : NockEval (atom 42) (cell (atom 1) (atom 99)) (.val (atom 99)) :=
  NockEval.op1

-- *[a 0 1] = a   (slot 1 = identity)
example (a : Noun) : NockEval a (cell (atom 0) (atom 1)) (.val a) :=
  NockEval.op0 (fasO_one a)

-- *[a 4 0 1] = +a  (increment the subject), when the subject is an atom
example (n : Nat) :
    NockEval (atom n) (cell (atom 4) (cell (atom 0) (atom 1))) (.val (atom (1 + n))) :=
  NockEval.op4 (NockEval.op0 (fasO_one (atom n))) (lusO_atom n)

-- *[[bat [sam ctx]] 10 [6 [1 arg]] [0 1]] = [bat [arg ctx]]   (sample edit)
example (bat sam ctx arg : Noun) :
    NockEval (cell bat (cell sam ctx))
             (cell (atom 10) (cell (cell (atom 6) (cell (atom 1) arg)) (cell (atom 0) (atom 1))))
             (.val (cell bat (cell arg ctx))) :=
  NockEval.op10 (NockEval.op0 (fasO_one _)) NockEval.op1
    (haxO_six arg bat sam ctx)

-- ---------------------------------------------------------------------------
-- Crash sanity examples — the point of the Outcome refactor.
-- Each of these was previously derivable with result `atom 0`.
-- ---------------------------------------------------------------------------

-- Axis 0 crashes.  (`fasO` is a well-founded recursion, so it does not
-- reduce by `rfl`; the named lemma `fasO_zero` supplies the equation.)
example (a : Noun) : NockEval a (cell (atom 0) (atom 0)) .exit :=
  NockEval.op0_crash (fasO_zero a)

-- Increment of a cell crashes.
example : NockEval (atom 0)
    (cell (atom 4) (cell (atom 1) (cell (atom 1) (atom 2)))) .exit :=
  NockEval.op4_cell NockEval.op1 rfl

-- A bare atom is not a formula.
example (a : Noun) (n : Nat) : NockEval a (atom n) .exit :=
  NockEval.crash_malformed rfl

-- Opcode 12 does not exist.
example (a fol : Noun) : NockEval a (cell (atom 12) fol) .exit :=
  NockEval.crash_malformed rfl

-- A crash in the head operand of `7` hides the tail: *[a 7 [0 0] c] crashes
-- whatever `c` is, even if `c` alone would diverge or succeed.
example (a c : Noun) :
    NockEval a (cell (atom 7) (cell (cell (atom 0) (atom 0)) c)) .exit :=
  NockEval.op7_crash (NockEval.op0_crash (fasO_zero a))
