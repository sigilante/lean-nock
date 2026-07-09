import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
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
  deriving DecidableEq, Repr

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
