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
  | dec                                             -- Class C
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
private theorem countUp_correct (n : Nat) :
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

