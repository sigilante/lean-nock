import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Notation
open Noun

/-!
# Words, leaf contracts, and the composition theorem

## Scope

This file mechanizes the **Nock side and the composition schema** of the
co-derivation pipeline.  The C side is a **shallow model**: `cw : Word → Noun
→ Outcome` is a Lean function standing in for a C routine.  What is proved is

> the compiled Nock formula agrees with the *modeled* semantics of the C
> routine, for every word and every subject noun.

The gap between the model `cw` and any actual C implementation is deliberately
outside this development; it is the trusted base of the companion paper.  This
file does **not** claim verified C, a verified compiler to C, or verified jets.
The accurate claim is: *the composition schema is kernel-checked; the C
routines are modeled, not compiled.*

`cw .dec` will look like a jet.  It is not.  **`cw` is the contract interface:
the shared denotation that both the Nock formula and the C routine are
separately obligated to meet.**  The leaf theorem discharges the Nock side's
obligation, kernel-checked.  The C side's obligation to the same denotation is
the trusted base, on paper, exactly where the manuscript says it lives.  `cw`
is not an implementation of anything; it is Equation 1's meeting point made
into a Lean term.

## Crash-totality is enforced, not assumed

`leaf_correct` supplies a derivation at *every* subject, so no `phi w` can
diverge (`word_crash_total`).  A formula that diverges anywhere is therefore
not denotable as a `Word` (`not_denotable_of_diverges`).  This is the paper's
guard-emission rule — Λ emits domain guards ahead of every partial operation —
surfacing as a type-level invariant.  Divergence enters the language
exclusively through `while`.

The rule is non-vacuous: `Nock/Shim.lean` exhibits the excluded witness.
Hoon's compiled `++dec`, naively lifted, diverges on a cell argument and so is
provably not a `Word`.

## Stack convention

The subject is the stack, `S = [top rest]`.  In an effect comment `( a b — … )`
the **rightmost element is the top**, so `( a b — b a )` reads a subject
`[b [a rest]]`.

## Argument order in `eq`

`phi .eq` evaluates `[0 6]` before `[0 2]`, so the model is `tisN a b` with the
deeper element first.  `tisN` is symmetric in value, but the leaf proof closes
definitionally only in this order.
-/

inductive Word
  | dup | drop | swap | over | cons | head | tail   -- Class A
  | inc | eq | celq                                 -- Class B  (celq = cel?)
  | dec | add | sub                                 -- Class C
  deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- Class C: guarded `dec`
--
-- `countUp` is the manuscript's canonical loop, verbatim.  Its core is
-- `[bat [b a]]`: axis 2 = battery, 6 = counter, 7 = argument.  It is built for
-- a BARE ATOM argument and diverges on a cell.
--
-- The guards are the manuscript's, corrected: they sit at axis 1, not axis 2.
-- As printed (axis 2) they read the wrong noun under the lift — see
-- TABLE-REPORT.md §C.  The `dec` row of Table C is discharged by `leaf_dec`.
-- ---------------------------------------------------------------------------

def countUp : Noun :=
  n! "[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] [9 2 [0 2] [4 0 6] 0 7]] 9 2 0 1]"

/-- The loop battery of `countUp`. -/
def countUpBat : Noun :=
  n! "[6 [5 [0 7] 4 0 6] [0 6] [9 2 [0 2] [4 0 6] 0 7]]"

/-- The loop core: `[countUpBat [b a]]`. -/
def countUpCore (b : Nat) (a : Noun) : Noun :=
  cell countUpBat (cell (atom b) a)

/-- Λ-emitted domain guards, at axis 1 (the argument guarded-dec receives).

      [6 [3 0 1] [0 0] [6 [5 [1 0] 0 1] [0 0] <count-up>]] -/
def decGuarded : Noun :=
  cell (atom 6) (cell (n! "[3 0 1]")
    (cell (n! "[0 0]")
      (cell (atom 6) (cell (n! "[5 [1 0] 0 1]") (cell (n! "[0 0]") countUp)))))

/-- Lift a unary atom operation to a stack word: run `g` on the top, cons the
    result back onto the rest.  The manuscript's lift, unchanged.

    The depth guard is free: on a bare-atom stack `fasO (atom 2) (atom _) = none`,
    so `op7`'s left operand crashes. -/
def liftUnary (g : Noun) : Noun :=
  cell (cell (atom 7) (cell (cell (atom 0) (atom 2)) g)) (cell (atom 0) (atom 3))

-- ---------------------------------------------------------------------------
-- Class C: guarded `add` and `sub`
--
-- Both are binary.  `liftBinary` hands the operation the pair `[a b]` built
-- from a stack `[b [a rest]]` (b on top), and conses the result onto `rest`.
-- `guardPair` is the Λ-emitted domain guard: it crashes unless both operands
-- are atoms.  Behind the guards:
--
-- * `add` is an **inc-loop**: count `c` up from 0 to `b`, incrementing an
--   accumulator that starts at `a`.  Opcode 4 only; one loop.
-- * `sub` is a **dec-loop**: while `b ≠ 0`, decrement both operands, each by
--   the guarded `dec` above (a nested loop).  When `b > a`, `a` reaches 0
--   first and the guarded `dec` crashes — so the `b > a` crash of Table C is
--   inherited from the `dec` guard rather than tested separately.
-- ---------------------------------------------------------------------------

/-- Guard both elements of a pair `[a b]` to be atoms, then run `k`.

      [6 [3 0 2] [0 0] [6 [3 0 3] [0 0] k]] -/
def guardPair (k : Noun) : Noun :=
  cell (atom 6) (cell (n! "[3 0 2]")
    (cell (n! "[0 0]")
      (cell (atom 6) (cell (n! "[3 0 3]") (cell (n! "[0 0]") k)))))

/-- Lift a binary operation on a pair `[a b]` to a stack word on
    `[b [a rest]]`: build the pair, run `g`, cons the result onto `rest`.

      [[7 [[0 6] 0 2] g] 0 7]

    The depth guard is free: on a stack of depth < 2, `[0 6]` crashes. -/
def liftBinary (g : Noun) : Noun :=
  cell (cell (atom 7) (cell (cell (cell (atom 0) (atom 6)) (cell (atom 0) (atom 2))) g))
       (cell (atom 0) (atom 7))

/-- The `add` loop battery.  Core `[bat [c [acc b]]]`: axis 6 = counter,
    14 = accumulator, 15 = bound.  Return `acc` when `c = b`, else bump both. -/
def wAddBat : Noun :=
  n! "[6 [5 [0 6] 0 15] [0 14] [9 2 [0 2] [4 0 6] [4 0 14] 0 15]]"

/-- The loop core `[wAddBat [c [acc b]]]`. -/
def wAddCore (c acc b : Nat) : Noun :=
  cell wAddBat (cell (atom c) (cell (atom acc) (atom b)))

/-- On a pair `[a b]`: push counter 0, push the battery, fire.

      [8 [1 0] 8 [1 wAddBat] 9 2 0 1] -/
def wAddLoop : Noun :=
  cell (atom 8) (cell (n! "[1 0]")
    (cell (atom 8) (cell (cell (atom 1) wAddBat) (n! "[9 2 0 1]"))))

def addGuarded : Noun := guardPair wAddLoop

/-- The `sub` loop's core rebuild: `[bat [dec(a) dec(b)]]`, each `dec` the
    guarded one.  `[[0 2] [7 [0 6] <guarded-dec>] 7 [0 7] <guarded-dec>]` -/
def wSubRebuild : Noun :=
  cell (n! "[0 2]")
    (cell (cell (atom 7) (cell (n! "[0 6]") decGuarded))
          (cell (atom 7) (cell (n! "[0 7]") decGuarded)))

/-- The `sub` loop battery.  Core `[bat [a b]]`: return `a` when `b = 0`,
    else decrement both and fire again.

      [6 [5 [1 0] 0 7] [0 6] [9 2 wSubRebuild]] -/
def wSubBat : Noun :=
  cell (atom 6) (cell (n! "[5 [1 0] 0 7]")
    (cell (n! "[0 6]") (cell (atom 9) (cell (atom 2) wSubRebuild))))

/-- The loop core `[wSubBat [a b]]`. -/
def wSubCore (a b : Nat) : Noun := cell wSubBat (cell (atom a) (atom b))

/-- On a pair `[a b]`: push the battery, fire.  `[8 [1 wSubBat] 9 2 0 1]` -/
def wSubLoop : Noun :=
  cell (atom 8) (cell (cell (atom 1) wSubBat) (n! "[9 2 0 1]"))

def subGuarded : Noun := guardPair wSubLoop

/-- Nock formulas, transcribed verbatim from the paper's Tables A and B. -/
def phi : Word → Noun
  | .dup  => cell (cell (atom 0) (atom 2)) (cell (atom 0) (atom 1))
      -- [[0 2] 0 1]          ( a — a a )
  | .drop => cell (atom 0) (atom 3)
      -- [0 3]                ( a — )
  | .swap => cell (cell (atom 0) (atom 6))
                  (cell (cell (atom 0) (atom 2)) (cell (atom 0) (atom 7)))
      -- [[0 6] [0 2] 0 7]    ( a b — b a )
  | .over => cell (cell (atom 0) (atom 6)) (cell (atom 0) (atom 1))
      -- [[0 6] 0 1]          ( a b — a b a )
  | .cons => cell (cell (cell (atom 0) (atom 6)) (cell (atom 0) (atom 2)))
                  (cell (atom 0) (atom 7))
      -- [[[0 6] 0 2] 0 7]    ( h t — [h t] )
  | .head => cell (cell (atom 0) (atom 4)) (cell (atom 0) (atom 3))
      -- [[0 4] 0 3]          ( c — h )
  | .tail => cell (cell (atom 0) (atom 5)) (cell (atom 0) (atom 3))
      -- [[0 5] 0 3]          ( c — t )
  | .inc  => cell (cell (atom 4) (cell (atom 0) (atom 2)))
                  (cell (atom 0) (atom 3))
      -- [[4 0 2] 0 3]        ( a — a+1 )
  | .eq   => cell (cell (atom 5) (cell (cell (atom 0) (atom 6))
                                       (cell (atom 0) (atom 2))))
                  (cell (atom 0) (atom 7))
      -- [[5 [0 6] 0 2] 0 7]  ( a b — ? )
  | .celq => cell (cell (atom 3) (cell (atom 0) (atom 2)))
                  (cell (atom 0) (atom 3))
      -- [[3 0 2] 0 3]        ( a — ? )
  | .dec  => liftUnary decGuarded
      -- [[7 [0 2] <guarded-dec>] 0 3]   ( a — a-1 )
  | .add  => liftBinary addGuarded
      -- [[7 [[0 6] 0 2] <guarded-inc-loop>] 0 7]   ( a b — a+b )
  | .sub  => liftBinary subGuarded
      -- [[7 [[0 6] 0 2] <guarded-dec-loop>] 0 7]   ( a b — a-b )

/-- The shallow C model.  Total over **all** nouns; the `.exit` cases are the
    ⊥-domain column of the paper's tables, stated over arbitrary nouns rather
    than relative to a stack invariant. -/
def cw : Word → Noun → Outcome
  | .dup,  cell a r          => .val (cell a (cell a r))
  | .dup,  atom _            => .exit
  | .drop, cell _ r          => .val r
  | .drop, atom _            => .exit
  | .swap, cell b (cell a r) => .val (cell a (cell b r))
  | .swap, cell _ (atom _)   => .exit
  | .swap, atom _            => .exit
  | .over, cell b (cell a r) => .val (cell a (cell b (cell a r)))
  | .over, cell _ (atom _)   => .exit
  | .over, atom _            => .exit
  | .cons, cell t (cell h r) => .val (cell (cell h t) r)
  | .cons, cell _ (atom _)   => .exit
  | .cons, atom _            => .exit
  | .head, cell (cell h _) r => .val (cell h r)
  | .head, cell (atom _) _   => .exit
  | .head, atom _            => .exit
  | .tail, cell (cell _ t) r => .val (cell t r)
  | .tail, cell (atom _) _   => .exit
  | .tail, atom _            => .exit
  | .inc,  cell (atom n) r   => .val (cell (atom (1 + n)) r)
  | .inc,  cell (cell _ _) _ => .exit
  | .inc,  atom _            => .exit
  | .eq,   cell b (cell a r) => .val (cell (tisN a b) r)
  | .eq,   cell _ (atom _)   => .exit
  | .eq,   atom _            => .exit
  | .celq, cell a r          => .val (cell (wut a) r)
  | .celq, atom _            => .exit
  -- Table C row for `dec`.  NORMATIVE — transcribed, not fitted to a proof.
  | .dec,  atom _              => .exit                    -- depth < 1
  | .dec,  cell (atom 0) _     => .exit                    -- underflow
  | .dec,  cell (cell _ _) _   => .exit                    -- cell argument
  | .dec,  cell (atom (n+1)) r => .val (cell (atom n) r)
  -- Table C rows for `add` and `sub`, on `[b [a r]]` (b on top).
  | .add,  atom _                          => .exit    -- depth < 2
  | .add,  cell _ (atom _)                 => .exit    -- depth < 2
  | .add,  cell (cell _ _) (cell _ _)      => .exit    -- b is a cell
  | .add,  cell (atom _) (cell (cell _ _) _) => .exit  -- a is a cell
  | .add,  cell (atom b) (cell (atom a) r) => .val (cell (atom (a + b)) r)
  | .sub,  atom _                          => .exit    -- depth < 2
  | .sub,  cell _ (atom _)                 => .exit    -- depth < 2
  | .sub,  cell (cell _ _) (cell _ _)      => .exit    -- b is a cell
  | .sub,  cell (atom _) (cell (cell _ _) _) => .exit  -- a is a cell
  | .sub,  cell (atom b) (cell (atom a) r) =>
      if b ≤ a then .val (cell (atom (a - b)) r) else .exit   -- b > a crashes

-- ---------------------------------------------------------------------------
-- Leaf contracts: one per word.  Each is a *single* statement carrying the
-- value clause and the crash clause at once, since `cw w S` is by definition
-- whichever of the two applies.  Exclusivity comes free from
-- `NockEval.deterministic`.
-- ---------------------------------------------------------------------------

private theorem leaf_dup (S : Noun) : NockEval S (phi .dup) (cw .dup S) := by
  cases S with
  | atom n => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_two_atom n))
  | cell a r =>
    exact NockEval.autocons (NockEval.op0 (fasO_head a r)) (NockEval.op0 (fasO_one _))

private theorem leaf_drop (S : Noun) : NockEval S (phi .drop) (cw .drop S) := by
  cases S with
  | atom n => exact NockEval.op0_crash (fasO_three_atom n)
  | cell a r => exact NockEval.op0 (fasO_tail a r)

private theorem leaf_swap (S : Noun) : NockEval S (phi .swap) (cw .swap S) := by
  cases S with
  | atom n => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_six_atom n))
  | cell b t =>
    cases t with
    | atom m => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_six_atomtail b m))
    | cell a r =>
      exact NockEval.autocons (NockEval.op0 (fasO_six b a r))
        (NockEval.autocons (NockEval.op0 (fasO_head b (cell a r)))
                           (NockEval.op0 (fasO_seven b a r)))

private theorem leaf_over (S : Noun) : NockEval S (phi .over) (cw .over S) := by
  cases S with
  | atom n => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_six_atom n))
  | cell b t =>
    cases t with
    | atom m => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_six_atomtail b m))
    | cell a r =>
      exact NockEval.autocons (NockEval.op0 (fasO_six b a r)) (NockEval.op0 (fasO_one _))

private theorem leaf_cons (S : Noun) : NockEval S (phi .cons) (cw .cons S) := by
  cases S with
  | atom n =>
    exact NockEval.autocons_crashL
      (NockEval.autocons_crashL (NockEval.op0_crash (fasO_six_atom n)))
  | cell t s =>
    cases s with
    | atom m =>
      exact NockEval.autocons_crashL
        (NockEval.autocons_crashL (NockEval.op0_crash (fasO_six_atomtail t m)))
    | cell h r =>
      exact NockEval.autocons
        (NockEval.autocons (NockEval.op0 (fasO_six t h r))
                           (NockEval.op0 (fasO_head t (cell h r))))
        (NockEval.op0 (fasO_seven t h r))

private theorem leaf_head (S : Noun) : NockEval S (phi .head) (cw .head S) := by
  cases S with
  | atom n => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_four_atom n))
  | cell c r =>
    cases c with
    | atom m => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_four_atomhead m r))
    | cell h t =>
      exact NockEval.autocons (NockEval.op0 (fasO_four h t r))
                              (NockEval.op0 (fasO_tail (cell h t) r))

private theorem leaf_tail (S : Noun) : NockEval S (phi .tail) (cw .tail S) := by
  cases S with
  | atom n => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_five_atom n))
  | cell c r =>
    cases c with
    | atom m => exact NockEval.autocons_crashL (NockEval.op0_crash (fasO_five_atomhead m r))
    | cell h t =>
      exact NockEval.autocons (NockEval.op0 (fasO_five h t r))
                              (NockEval.op0 (fasO_tail (cell h t) r))

private theorem leaf_inc (S : Noun) : NockEval S (phi .inc) (cw .inc S) := by
  cases S with
  | atom n =>
    exact NockEval.autocons_crashL (NockEval.op4_crash (NockEval.op0_crash (fasO_two_atom n)))
  | cell a r =>
    cases a with
    | atom m =>
      exact NockEval.autocons
        (NockEval.op4 (NockEval.op0 (fasO_head (atom m) r)) (lusO_atom m))
        (NockEval.op0 (fasO_tail (atom m) r))
    | cell u v =>
      exact NockEval.autocons_crashL
        (NockEval.op4_cell (NockEval.op0 (fasO_head (cell u v) r)) (lusO_cell u v))

private theorem leaf_eq (S : Noun) : NockEval S (phi .eq) (cw .eq S) := by
  cases S with
  | atom n => exact NockEval.autocons_crashL (NockEval.op5_crashL (NockEval.op0_crash (fasO_six_atom n)))
  | cell b t =>
    cases t with
    | atom m =>
      exact NockEval.autocons_crashL
        (NockEval.op5_crashL (NockEval.op0_crash (fasO_six_atomtail b m)))
    | cell a r =>
      exact NockEval.autocons
        (NockEval.op5 (NockEval.op0 (fasO_six b a r))
                      (NockEval.op0 (fasO_head b (cell a r))))
        (NockEval.op0 (fasO_seven b a r))

private theorem leaf_celq (S : Noun) : NockEval S (phi .celq) (cw .celq S) := by
  cases S with
  | atom n =>
    exact NockEval.autocons_crashL (NockEval.op3_crash (NockEval.op0_crash (fasO_two_atom n)))
  | cell a r =>
    exact NockEval.autocons (NockEval.op3 (NockEval.op0 (fasO_head a r)))
                            (NockEval.op0 (fasO_tail a r))

-- ── Class C: the guarded `dec` leaf ────────────────────────────────────────

private def cuCond : Noun := n! "[5 [0 7] 4 0 6]"
private def cuThen : Noun := n! "[0 6]"
private def cuRebuild : Noun := n! "[[0 2] [4 0 6] 0 7]"
private def cuElse : Noun := cell (atom 9) (cell (atom 2) cuRebuild)

private theorem countUpBat_parts :
    countUpBat = cell (atom 6) (cell cuCond (cell cuThen cuElse)) := rfl

private theorem countUp_parts :
    countUp = cell (atom 8) (cell (cell (atom 1) (atom 0))
      (cell (atom 8) (cell (cell (atom 1) countUpBat)
        (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1))))))) := rfl

private theorem cu_slot6 (b : Nat) (a : Noun) :
    NockEval (countUpCore b a) cuThen (.val (atom b)) :=
  NockEval.op0 (fasO_six countUpBat (atom b) a)

private theorem cu_slot7 (b : Nat) (a : Noun) :
    NockEval (countUpCore b a) (cell (atom 0) (atom 7)) (.val a) :=
  NockEval.op0 (fasO_seven countUpBat (atom b) a)

private theorem cu_cond (b : Nat) (a : Noun) :
    NockEval (countUpCore b a) cuCond (.val (tisN a (atom (1 + b)))) :=
  NockEval.op5 (cu_slot7 b a) (NockEval.op4 (cu_slot6 b a) (lusO_atom b))

/-- The recursion rebuilds the core by autocons — no `haxO` edit. -/
private theorem cu_rebuild (b : Nat) (a : Noun) :
    NockEval (countUpCore b a) cuRebuild (.val (countUpCore (b + 1) a)) := by
  have h : NockEval (countUpCore b a) cuRebuild
      (.val (cell countUpBat (cell (atom (1 + b)) a))) :=
    NockEval.autocons (NockEval.op0 (fasO_head _ _))
      (NockEval.autocons (NockEval.op4 (cu_slot6 b a) (lusO_atom b)) (cu_slot7 b a))
  simpa [countUpCore, Nat.add_comm] using h

private theorem tisN_cu_true (b : Nat) : tisN (atom (b + 1)) (atom (1 + b)) = atom 0 := by
  simp [tisN, Nat.add_comm]

private theorem tisN_cu_false (b n : Nat) (h : b + 1 < n) :
    tisN (atom n) (atom (1 + b)) = atom 1 := by
  refine tisN_neq _ _ ?_
  intro hc; simp at hc; omega

/-- Loop invariant for the manuscript's canonical `<count-up>`. -/
private theorem countUp_loop (b n : Nat) (hb : b < n) :
    NockEval (countUpCore b (atom n)) countUpBat (.val (atom (n - 1))) := by
  obtain ⟨d, hd⟩ : ∃ d, n = b + 1 + d := ⟨n - b - 1, by omega⟩
  subst hd
  induction d generalizing b with
  | zero =>
    simp only [Nat.add_zero, show b + 1 - 1 = b from by omega]
    rw [countUpBat_parts]
    refine NockEval.op6_then ?_ (cu_slot6 b (atom (b + 1)))
    have h := cu_cond b (atom (b + 1))
    rwa [tisN_cu_true] at h
  | succ d ih =>
    simp only [show b + 1 + (d + 1) - 1 = b + 1 + d from by omega]
    rw [countUpBat_parts]
    refine NockEval.op6_else ?_ ?_
    · have h := cu_cond b (atom (b + 1 + (d + 1)))
      rwa [tisN_cu_false b (b + 1 + (d + 1)) (by omega)] at h
    · show NockEval (countUpCore b (atom (b + 1 + (d + 1)))) cuElse (.val (atom (b + 1 + d)))
      refine NockEval.op9 (cu_rebuild b _) (fasO_head _ _) ?_
      rw [show b + 1 + (d + 1) = (b + 1) + 1 + d from by omega]
      have := ih (b + 1) (by omega)
      rwa [show (b + 1) + 1 + d - 1 = b + 1 + d from by omega] at this

/-- `<count-up>` is correct — on a **bare atom**.  (On a stack subject it
    diverges; that is the Reading-B refutation in TABLE-REPORT.md §C.3.) -/
theorem countUp_correct (n : Nat) :
    NockEval (atom (n + 1)) countUp (.val (atom n)) := by
  rw [countUp_parts]
  refine NockEval.op8 NockEval.op1 ?_
  refine NockEval.op8 NockEval.op1 ?_
  show NockEval (countUpCore 0 (atom (n + 1)))
    (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) (.val (atom n))
  refine NockEval.op9 (core := countUpCore 0 (atom (n + 1))) (arm := countUpBat)
    (NockEval.op0 (fasO_one _)) (fasO_head _ _) ?_
  have h := countUp_loop 0 (n + 1) (by omega)
  simpa using h

/-- Guard 1 fires: a cell argument crashes.  With the guards at axis 1 this
    reads the argument itself; the printed axis 2 read its *head*. -/
private theorem decg_cell (x y : Noun) : NockEval (cell x y) decGuarded .exit := by
  refine NockEval.op6_then ?_ (NockEval.op0_crash (fasO_zero _))
  have h : NockEval (cell x y) (cell (atom 3) (cell (atom 0) (atom 1)))
      (.val (wut (cell x y))) := NockEval.op3 (NockEval.op0 (fasO_one _))
  rwa [wut_cell] at h

/-- Guard 2 fires: underflow crashes. -/
private theorem decg_zero : NockEval (atom 0) decGuarded .exit := by
  refine NockEval.op6_else ?_ ?_
  · have h : NockEval (atom 0) (cell (atom 3) (cell (atom 0) (atom 1)))
        (.val (wut (atom 0))) := NockEval.op3 (NockEval.op0 (fasO_one _))
    rwa [wut_atom] at h
  · refine NockEval.op6_then ?_ (NockEval.op0_crash (fasO_zero _))
    have h0 : NockEval (atom 0) (cell (atom 1) (atom 0)) (.val (atom 0)) := NockEval.op1
    have h1 : NockEval (atom 0) (cell (atom 0) (atom 1)) (.val (atom 0)) :=
      NockEval.op0 (fasO_one _)
    have h := NockEval.op5 h0 h1
    rwa [tisN_refl] at h

/-- Both guards pass: the loop runs on a genuine bare atom. -/
private theorem decg_succ (n : Nat) :
    NockEval (atom (n + 1)) decGuarded (.val (atom n)) := by
  refine NockEval.op6_else ?_ ?_
  · have h : NockEval (atom (n + 1)) (cell (atom 3) (cell (atom 0) (atom 1)))
        (.val (wut (atom (n + 1)))) := NockEval.op3 (NockEval.op0 (fasO_one _))
    rwa [wut_atom] at h
  · refine NockEval.op6_else ?_ (countUp_correct n)
    have h0 : NockEval (atom (n + 1)) (cell (atom 1) (atom 0)) (.val (atom 0)) := NockEval.op1
    have h1 : NockEval (atom (n + 1)) (cell (atom 0) (atom 1)) (.val (atom (n + 1))) :=
      NockEval.op0 (fasO_one _)
    have h := NockEval.op5 h0 h1
    rwa [show tisN (atom 0) (atom (n + 1)) = atom 1 from
      tisN_neq _ _ (by intro hc; injection hc with hc; omega)] at h

/-- **Table C's `dec` row, discharged by the kernel.**  The lift is the
    manuscript's; the guards are the manuscript's corrected to axis 1. -/
private theorem leaf_dec (S : Noun) : NockEval S (phi .dec) (cw .dec S) := by
  cases S with
  | atom n =>
    exact NockEval.autocons_crashL (NockEval.op7_crash (NockEval.op0_crash (fasO_two_atom n)))
  | cell a r =>
    cases a with
    | cell x y =>
      exact NockEval.autocons_crashL
        (NockEval.op7 (NockEval.op0 (fasO_head _ _)) (decg_cell x y))
    | atom m =>
      cases m with
      | zero =>
        exact NockEval.autocons_crashL
          (NockEval.op7 (NockEval.op0 (fasO_head _ _)) decg_zero)
      | succ n =>
        exact NockEval.autocons
          (NockEval.op7 (NockEval.op0 (fasO_head _ _)) (decg_succ n))
          (NockEval.op0 (fasO_tail _ _))

-- ── The canonical <count-up>, unguarded: divergence at 0 and on a cell ─────

private theorem no_val_exit {s f v} (hv : NockEval s f (.val v))
    (he : NockEval s f .exit) : False := by
  have := NockEval.deterministic hv he; simp at this

private theorem det_val {s f} {u v : Noun} (h1 : NockEval s f (.val u))
    (h2 : NockEval s f (.val v)) : u = v := by
  have := NockEval.deterministic h1 h2; simpa using this

/-- If the loop test never succeeds, no derivation reaches the loop battery or
    its else-arm.  Generalized over the counter and over the two formulas the
    recursion alternates between (the DecDiverges pattern). -/
private theorem countUp_loop_aux (a : Noun)
    (hne : ∀ j : Nat, tisN a (atom (1 + j)) = atom 1) :
    ∀ {s f : Noun} {o : Outcome}, NockEval s f o →
      ∀ k : Nat, s = countUpCore k a → (f = countUpBat ∨ f = cuElse) → False := by
  intro s f o h
  induction h with
  | @crash_malformed _ ff hm =>
    intro _ _ hf
    rcases hf with rfl | rfl <;> exact absurd hm (by decide)
  | @op6_then _ bb c d oo h1 _ _ _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp only [countUpBat_parts, Noun.cell.injEq] at hf
      obtain ⟨-, hb, -, -⟩ := hf
      subst hb; subst hs
      have canon := cu_cond k a
      rw [hne k] at canon
      have := NockEval.deterministic h1 canon; simp at this
    · simp [cuElse] at hf
  | @op6_else _ bb c d oo _ _ _ ih2 =>
    intro k hs hf
    rcases hf with hf | hf
    · simp only [countUpBat_parts, Noun.cell.injEq] at hf
      obtain ⟨-, -, -, hd⟩ := hf
      subst hd
      exact ih2 k hs (Or.inr rfl)
    · simp [cuElse] at hf
  | @op6_nonloob _ bb c d r h1 _ hne1 _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp only [countUpBat_parts, Noun.cell.injEq] at hf
      obtain ⟨-, hb, -, -⟩ := hf
      subst hb; subst hs
      have canon := cu_cond k a
      rw [hne k] at canon
      exact hne1 (det_val h1 canon)
    · simp [cuElse] at hf
  | @op6_crash _ bb c d h1 _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp only [countUpBat_parts, Noun.cell.injEq] at hf
      obtain ⟨-, hb, -, -⟩ := hf
      subst hb; subst hs
      exact no_val_exit (cu_cond k a) h1
    · simp [cuElse] at hf
  | @op9 _ bax c core arm oo h1 h2 _ _ ih3 =>
    intro k hs hf
    rcases hf with hf | hf
    · simp [countUpBat_parts] at hf
    · simp only [cuElse, Noun.cell.injEq] at hf
      obtain ⟨-, hbax, hc⟩ := hf
      subst hbax; subst hc; subst hs
      have hcore : core = countUpCore (k + 1) a := det_val h1 (cu_rebuild k a)
      subst hcore
      rw [show fasO (atom 2) (countUpCore (k + 1) a) = some countUpBat from
        fasO_head _ _] at h2
      have harm : arm = countUpBat := by simpa using h2.symm
      subst harm
      exact ih3 (k + 1) rfl (Or.inl rfl)
  | @op9_badaxis _ bax c core h1 h2 _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp [countUpBat_parts] at hf
    · simp only [cuElse, Noun.cell.injEq] at hf
      obtain ⟨-, hbax, hc⟩ := hf
      subst hbax; subst hc; subst hs
      have hcore : core = countUpCore (k + 1) a := det_val h1 (cu_rebuild k a)
      subst hcore
      rw [show fasO (atom 2) (countUpCore (k + 1) a) = some countUpBat from
        fasO_head _ _] at h2
      simp at h2
  | @op9_crash _ bax c h1 _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp [countUpBat_parts] at hf
    · simp only [cuElse, Noun.cell.injEq] at hf
      obtain ⟨-, -, hc⟩ := hf
      subst hc; subst hs
      exact no_val_exit (cu_rebuild k a) h1
  | _ =>
    intro _ _ hf
    rcases hf with hf | hf <;> simp [countUpBat_parts, cuElse] at hf

/-- The count-up loop, from any counter, never terminates when its test can
    never succeed. -/
theorem countUp_loop_diverges (k : Nat) (a : Noun)
    (hne : ∀ j : Nat, tisN a (atom (1 + j)) = atom 1) :
    Diverges (countUpCore k a) countUpBat :=
  fun _ h => countUp_loop_aux a hne h k rfl (Or.inl rfl)

/-- `<count-up>` diverges on any argument its test can never match. -/
theorem countUp_diverges (a : Noun)
    (hne : ∀ j : Nat, tisN a (atom (1 + j)) = atom 1) :
    Diverges a countUp := by
  intro o h
  rw [countUp_parts] at h
  have h0 : NockEval a (cell (atom 1) (atom 0)) (.val (atom 0)) := NockEval.op1
  cases h with
  | crash_malformed hm => exact absurd hm (by decide)
  | op8_crash hb => exact no_val_exit h0 hb
  | @op8 _ _ _ r1 _ hb hrest =>
    have hr1 : r1 = atom 0 := det_val hb h0
    subst hr1
    have h1 : NockEval (cell (atom 0) a) (cell (atom 1) countUpBat) (.val countUpBat) :=
      NockEval.op1
    cases hrest with
    | crash_malformed hm => exact absurd hm (by decide)
    | op8_crash hb2 => exact no_val_exit h1 hb2
    | @op8 _ _ _ r2 _ hb2 hfire =>
      have hr2 : r2 = countUpBat := det_val hb2 h1
      subst hr2
      have hfire' : NockEval (countUpCore 0 a)
          (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) o := hfire
      cases hfire' with
      | crash_malformed hm => exact absurd hm (by decide)
      | op9_crash hc => exact no_val_exit (NockEval.op0 (fasO_one _)) hc
      | @op9_badaxis _ _ _ core hc hnone =>
        have hcore : core = countUpCore 0 a := det_val hc (NockEval.op0 (fasO_one _))
        subst hcore
        rw [show fasO (atom 2) (countUpCore 0 a) = some countUpBat from
          fasO_head _ _] at hnone
        simp at hnone
      | @op9 _ _ _ core arm _ hc harm hloop =>
        have hcore : core = countUpCore 0 a := det_val hc (NockEval.op0 (fasO_one _))
        subst hcore
        rw [show fasO (atom 2) (countUpCore 0 a) = some countUpBat from
          fasO_head _ _] at harm
        have harm' : arm = countUpBat := by simpa using harm.symm
        subst harm'
        exact countUp_loop_diverges 0 a hne o hloop

/-- **The printed `dec` diverges at `0`.**  The counter starts at 0 and the
    test compares the argument with `counter + 1`, which is never 0. -/
theorem countUp_zero_diverges : Diverges (atom 0) countUp :=
  countUp_diverges (atom 0) (fun j =>
    tisN_neq _ _ (fun hc => by injection hc with hc; omega))

/-- **The printed `dec` diverges on a cell.**  A cell never equals an atom. -/
theorem countUp_cell_diverges (x y : Noun) : Diverges (cell x y) countUp :=
  countUp_diverges (cell x y) (fun j => tisN_cell_atom x y (1 + j))

-- ── Class C: `add` and `sub` ───────────────────────────────────────────────

/-- On a stack `[b [a r]]`, `[[0 6] 0 2]` builds the pair `[a b]`. -/
private theorem pair_eval (b a r : Noun) :
    NockEval (cell b (cell a r))
      (cell (cell (atom 0) (atom 6)) (cell (atom 0) (atom 2))) (.val (cell a b)) :=
  NockEval.autocons (NockEval.op0 (fasO_six b a r)) (NockEval.op0 (fasO_head b (cell a r)))

private theorem liftBinary_val {g b a r v : Noun} (h : NockEval (cell a b) g (.val v)) :
    NockEval (cell b (cell a r)) (liftBinary g) (.val (cell v r)) :=
  NockEval.autocons (NockEval.op7 (pair_eval b a r) h) (NockEval.op0 (fasO_seven b a r))

private theorem liftBinary_exit {g b a r : Noun} (h : NockEval (cell a b) g .exit) :
    NockEval (cell b (cell a r)) (liftBinary g) .exit :=
  NockEval.autocons_crashL (NockEval.op7 (pair_eval b a r) h)

private theorem liftBinary_atom (g : Noun) (n : Nat) :
    NockEval (atom n) (liftBinary g) .exit :=
  NockEval.autocons_crashL (NockEval.op7_crash
    (NockEval.autocons_crashL (NockEval.op0_crash (fasO_six_atom n))))

private theorem liftBinary_shallow (g b : Noun) (m : Nat) :
    NockEval (cell b (atom m)) (liftBinary g) .exit :=
  NockEval.autocons_crashL (NockEval.op7_crash
    (NockEval.autocons_crashL (NockEval.op0_crash (fasO_six_atomtail b m))))

/-- `[3 0 ax]` on a subject whose axis `ax` holds `v`. -/
private theorem cellq_eval {S v : Noun} {ax : Nat} (h : fasO (atom ax) S = some v) :
    NockEval S (cell (atom 3) (cell (atom 0) (atom ax))) (.val (wut v)) :=
  NockEval.op3 (NockEval.op0 h)

/-- The guard's first test fires: the left operand is a cell. -/
private theorem guardPair_cellL (x y b k : Noun) :
    NockEval (cell (cell x y) b) (guardPair k) .exit := by
  have h := cellq_eval (ax := 2) (fasO_head (cell x y) b)
  rw [wut_cell] at h
  exact NockEval.op6_then h (NockEval.op0_crash (fasO_zero _))

/-- The guard's second test fires: the right operand is a cell. -/
private theorem guardPair_cellR (m : Nat) (x y k : Noun) :
    NockEval (cell (atom m) (cell x y)) (guardPair k) .exit := by
  have h1 := cellq_eval (ax := 2) (fasO_head (atom m) (cell x y))
  rw [wut_atom] at h1
  have h2 := cellq_eval (ax := 3) (fasO_tail (atom m) (cell x y))
  rw [wut_cell] at h2
  exact NockEval.op6_else h1 (NockEval.op6_then h2 (NockEval.op0_crash (fasO_zero _)))

/-- Both operands are atoms: the guard passes control to `k`, outcome intact. -/
private theorem guardPair_pass {m n : Nat} {k : Noun} {o : Outcome}
    (h : NockEval (cell (atom m) (atom n)) k o) :
    NockEval (cell (atom m) (atom n)) (guardPair k) o := by
  have h1 := cellq_eval (ax := 2) (fasO_head (atom m) (atom n))
  rw [wut_atom] at h1
  have h2 := cellq_eval (ax := 3) (fasO_tail (atom m) (atom n))
  rw [wut_atom] at h2
  exact NockEval.op6_else h1 (NockEval.op6_else h2 h)

-- `add`: the inc-loop

private theorem wAdd_slot14 (c acc b : Nat) :
    fasO (atom 14) (wAddCore c acc b) = some (atom acc) := by simp [wAddCore, fasO]

private theorem wAdd_slot15 (c acc b : Nat) :
    fasO (atom 15) (wAddCore c acc b) = some (atom b) := by simp [wAddCore, fasO]

private theorem wAddBat_parts :
    wAddBat = cell (atom 6) (cell (n! "[5 [0 6] 0 15]") (cell (n! "[0 14]")
      (cell (atom 9) (cell (atom 2) (n! "[[0 2] [4 0 6] [4 0 14] 0 15]"))))) := rfl

private theorem wAdd_rebuild (c acc b : Nat) :
    NockEval (wAddCore c acc b) (n! "[[0 2] [4 0 6] [4 0 14] 0 15]")
      (.val (wAddCore (c + 1) (acc + 1) b)) := by
  have h : NockEval (wAddCore c acc b) (n! "[[0 2] [4 0 6] [4 0 14] 0 15]")
      (.val (cell wAddBat (cell (atom (1 + c)) (cell (atom (1 + acc)) (atom b))))) :=
    NockEval.autocons (NockEval.op0 (fasO_head _ _))
      (NockEval.autocons
        (NockEval.op4 (NockEval.op0 (fasO_six _ _ _)) (lusO_atom c))
        (NockEval.autocons
          (NockEval.op4 (NockEval.op0 (wAdd_slot14 c acc b)) (lusO_atom acc))
          (NockEval.op0 (wAdd_slot15 c acc b))))
  simpa [wAddCore, Nat.add_comm] using h

/-- Loop invariant: with `d` iterations to go, the loop adds `d`. -/
private theorem wAdd_loop (d : Nat) : ∀ c acc b : Nat, b = c + d →
    NockEval (wAddCore c acc b) wAddBat (.val (atom (acc + d))) := by
  induction d with
  | zero =>
    intro c acc b hb
    simp only [Nat.add_zero] at hb ⊢
    rw [hb, wAddBat_parts]
    have hcond : NockEval (wAddCore c acc c) (n! "[5 [0 6] 0 15]") (.val (atom 0)) := by
      have h := NockEval.op5 (NockEval.op0 (fasO_six wAddBat (atom c) (cell (atom acc) (atom c))))
        (NockEval.op0 (wAdd_slot15 c acc c))
      rwa [tisN_refl] at h
    exact NockEval.op6_then hcond (NockEval.op0 (wAdd_slot14 c acc c))
  | succ d ih =>
    intro c acc b hb
    rw [wAddBat_parts]
    have hcond : NockEval (wAddCore c acc b) (n! "[5 [0 6] 0 15]") (.val (atom 1)) := by
      have h := NockEval.op5 (NockEval.op0 (fasO_six wAddBat (atom c) (cell (atom acc) (atom b))))
        (NockEval.op0 (wAdd_slot15 c acc b))
      rwa [tisN_neq _ _ (fun hc => by injection hc with hc; omega)] at h
    refine NockEval.op6_else hcond ?_
    refine NockEval.op9 (wAdd_rebuild c acc b) (fasO_head _ _) ?_
    have := ih (c + 1) (acc + 1) b (by omega)
    rwa [show acc + 1 + d = acc + (d + 1) from by omega] at this

/-- The guarded inc-loop computes `a + b` on a pair of atoms. -/
private theorem addGuarded_atoms (a b : Nat) :
    NockEval (cell (atom a) (atom b)) addGuarded (.val (atom (a + b))) := by
  refine guardPair_pass ?_
  refine NockEval.op8 NockEval.op1 (NockEval.op8 NockEval.op1 ?_)
  show NockEval (wAddCore 0 a b)
    (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) (.val (atom (a + b)))
  exact NockEval.op9 (NockEval.op0 (fasO_one _)) (fasO_head _ _)
    (wAdd_loop b 0 a b (by omega))

/-- **Table C's `add` row, discharged by the kernel.** -/
private theorem leaf_add (S : Noun) : NockEval S (phi .add) (cw .add S) := by
  cases S with
  | atom n => exact liftBinary_atom _ n
  | cell b t =>
    cases t with
    | atom m => exact liftBinary_shallow _ b m
    | cell a r =>
      cases b with
      | cell bx byy =>
        cases a with
        | cell x y => exact liftBinary_exit (guardPair_cellL x y _ _)
        | atom m   => exact liftBinary_exit (guardPair_cellR m bx byy _)
      | atom nb =>
        cases a with
        | cell x y => exact liftBinary_exit (guardPair_cellL x y _ _)
        | atom na  => exact liftBinary_val (addGuarded_atoms na nb)

-- `sub`: the dec-loop, over the guarded `dec`

private theorem wSubBat_parts :
    wSubBat = cell (atom 6) (cell (n! "[5 [1 0] 0 7]")
      (cell (n! "[0 6]") (cell (atom 9) (cell (atom 2) wSubRebuild)))) := rfl

/-- Loop invariant: the dec-loop computes `a - b` when `b ≤ a`, and crashes
    (through the guarded `dec` at 0) when `b > a`. -/
private theorem wSub_loop (b : Nat) : ∀ a : Nat,
    NockEval (wSubCore a b) wSubBat
      (if b ≤ a then .val (atom (a - b)) else .exit) := by
  induction b with
  | zero =>
    intro a
    rw [if_pos (Nat.zero_le a), Nat.sub_zero, wSubBat_parts]
    have hcond : NockEval (wSubCore a 0) (n! "[5 [1 0] 0 7]") (.val (atom 0)) := by
      have h := NockEval.op5 (a := wSubCore a 0) (NockEval.op1 (fol := atom 0))
        (NockEval.op0 (fasO_seven wSubBat (atom a) (atom 0)))
      rwa [tisN_refl] at h
    exact NockEval.op6_then hcond (NockEval.op0 (fasO_six _ _ _))
  | succ k ih =>
    intro a
    rw [wSubBat_parts]
    have hcond : NockEval (wSubCore a (k + 1)) (n! "[5 [1 0] 0 7]") (.val (atom 1)) := by
      have h := NockEval.op5 (a := wSubCore a (k + 1)) (NockEval.op1 (fol := atom 0))
        (NockEval.op0 (fasO_seven wSubBat (atom a) (atom (k + 1))))
      rwa [tisN_neq _ _ (fun hc => by injection hc with hc; omega)] at h
    refine NockEval.op6_else hcond ?_
    cases a with
    | zero =>
      rw [if_neg (by omega)]
      refine NockEval.op9_crash ?_
      exact NockEval.autocons_crashR (NockEval.op0 (fasO_head _ _))
        (NockEval.autocons_crashL
          (NockEval.op7 (NockEval.op0 (fasO_six _ _ _)) decg_zero))
    | succ m =>
      have hre : NockEval (wSubCore (m + 1) (k + 1)) wSubRebuild (.val (wSubCore m k)) :=
        NockEval.autocons (NockEval.op0 (fasO_head _ _))
          (NockEval.autocons
            (NockEval.op7 (NockEval.op0 (fasO_six _ _ _)) (decg_succ m))
            (NockEval.op7 (NockEval.op0 (fasO_seven _ _ _)) (decg_succ k)))
      refine NockEval.op9 hre (fasO_head _ _) ?_
      have hk := ih m
      rcases Nat.lt_or_ge m k with hlt | hge
      · rw [if_neg (by omega)] at hk
        rw [if_neg (by omega)]
        exact hk
      · rw [if_pos hge] at hk
        rw [if_pos (by omega), show m + 1 - (k + 1) = m - k from by omega]
        exact hk

/-- The guarded dec-loop on a pair of atoms. -/
private theorem subGuarded_atoms (a b : Nat) :
    NockEval (cell (atom a) (atom b)) subGuarded
      (if b ≤ a then .val (atom (a - b)) else .exit) := by
  refine guardPair_pass ?_
  refine NockEval.op8 NockEval.op1 ?_
  show NockEval (wSubCore a b)
    (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) _
  exact NockEval.op9 (NockEval.op0 (fasO_one _)) (fasO_head _ _) (wSub_loop b a)

/-- **Table C's `sub` row, discharged by the kernel.** -/
private theorem leaf_sub (S : Noun) : NockEval S (phi .sub) (cw .sub S) := by
  cases S with
  | atom n => exact liftBinary_atom _ n
  | cell b t =>
    cases t with
    | atom m => exact liftBinary_shallow _ b m
    | cell a r =>
      cases b with
      | cell bx byy =>
        cases a with
        | cell x y => exact liftBinary_exit (guardPair_cellL x y _ _)
        | atom m   => exact liftBinary_exit (guardPair_cellR m bx byy _)
      | atom nb =>
        cases a with
        | cell x y => exact liftBinary_exit (guardPair_cellL x y _ _)
        | atom na  =>
          have h := subGuarded_atoms na nb
          show NockEval (cell (atom nb) (cell (atom na) r)) (phi .sub)
            (if nb ≤ na then .val (cell (atom (na - nb)) r) else .exit)
          rcases Nat.lt_or_ge na nb with hlt | hge
          · rw [if_neg (by omega)] at h ⊢
            exact liftBinary_exit h
          · rw [if_pos hge] at h ⊢
            exact liftBinary_val h

/-- **Leaf correctness.**  For every word and every subject noun, the compiled
    Nock formula evaluates to exactly the outcome the C model specifies —
    value where the model returns, crash where the model crashes. -/
theorem leaf_correct (w : Word) (S : Noun) : NockEval S (phi w) (cw w S) := by
  cases w
  · exact leaf_dup S
  · exact leaf_drop S
  · exact leaf_swap S
  · exact leaf_over S
  · exact leaf_cons S
  · exact leaf_head S
  · exact leaf_tail S
  · exact leaf_inc S
  · exact leaf_eq S
  · exact leaf_celq S
  · exact leaf_dec S
  · exact leaf_add S
  · exact leaf_sub S

-- ---------------------------------------------------------------------------
-- The two compilers and the composition theorem
-- ---------------------------------------------------------------------------

abbrev Prog := List Word

/-- Compile a word list to a single Nock formula by right-nested `op7`. -/
def N : Prog → Noun
  | []     => cell (atom 0) (atom 1)                    -- [0 1]
  | w :: p => cell (atom 7) (cell (phi w) (N p))        -- [7 φ_w N(p)]

/-- Run a word list through the C model, threading the stack.  Explicit
    `match`, no `Outcome.bind` instance — consistent with `nockF`, and it keeps
    the induction syntactic. -/
def Csem : Prog → Noun → Outcome
  | [],     S => .val S
  | w :: p, S =>
    match cw w S with
    | .val S' => Csem p S'
    | .exit   => .exit

/-- **Composition.**  The compiled formula for a word list evaluates, on any
    stack, to exactly what running the list through the C model produces.

    Crash propagation is inherited from `op7`'s left-to-right strictness: once
    a word crashes, the rest of the program is never evaluated on either side. -/
theorem composition (p : Prog) (S : Noun) : NockEval S (N p) (Csem p S) := by
  induction p generalizing S with
  | nil => exact NockEval.op0 (fasO_one S)
  | cons w p ih =>
    simp only [N, Csem]
    cases hcw : cw w S with
    | val S' =>
      have hl := leaf_correct w S
      rw [hcw] at hl
      exact NockEval.op7 hl (ih S')
    | exit =>
      have hl := leaf_correct w S
      rw [hcw] at hl
      exact NockEval.op7_crash hl

/-- **Agreement.**  Any outcome derivable for the compiled formula *is* the
    model's outcome.  Combines `composition` with determinism, so the schema
    admits nothing else — including no spurious crash and no spurious value. -/
theorem composition_agree (p : Prog) (S : Noun) {o : Outcome}
    (h : NockEval S (N p) o) : o = Csem p S :=
  NockEval.deterministic h (composition p S)

-- ---------------------------------------------------------------------------
-- Sanity examples
-- ---------------------------------------------------------------------------

-- "dup inc": duplicate, then increment the copy — [n r] → [n+1 [n r]]
example (n : Nat) (r : Noun) :
    NockEval (cell (atom n) r) (N [.dup, .inc])
             (.val (cell (atom (1 + n)) (cell (atom n) r))) := by
  simpa [Csem, cw] using composition [.dup, .inc] (cell (atom n) r)

-- A crash hides the tail: `swap` on a depth-1 stack crashes, so the following
-- `drop` is never evaluated — on either side of the correspondence.
example (n : Nat) :
    NockEval (cell (atom n) (atom 0)) (N [.swap, .drop]) .exit := by
  simpa [Csem, cw] using composition [.swap, .drop] (cell (atom n) (atom 0))

-- ---------------------------------------------------------------------------
-- Crash-totality, free from `leaf_correct`
-- ---------------------------------------------------------------------------

/-- **Every `Word` denotes a crash-total formula.**  `leaf_correct` supplies a
    derivation at every subject, so no subject diverges.  This is the paper's
    guard-emission rule as an enforced invariant rather than a convention. -/
theorem word_crash_total (w : Word) (S : Noun) : ¬ Diverges S (phi w) :=
  fun hd => hd _ (leaf_correct w S)

/-- **The refusal.**  A formula that diverges anywhere is not denotable as a
    `Word`.  Not a limitation of the model — the model correctly rejecting an
    unguarded formula. -/
theorem not_denotable_of_diverges {f S : Noun} (hd : Diverges S f) :
    ¬ ∃ w : Word, phi w = f := by
  rintro ⟨w, rfl⟩
  exact word_crash_total w S hd

