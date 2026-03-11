import Nock.Basic
import Nock.Eval
import Nock.Notation
open Noun

/-!
# Hoon %one Core — Nock Formulas

Nock formulas compiled from Hoon's standard library arms, obtained via
`!=` (zapwut) in the Hoon dojo.  Atom thousands-separators (dots) removed.

Convention: `C [a, b, c, d]` = `cell a (cell b (cell c d))`, mirroring
Hoon's right-associative bracket notation.
-/

-- Right-associative cell list: mirrors `[a b c]` = `[a [b c]]` in Hoon/Nock.
private def C : List Noun → Noun
  | []      => panic! "C: empty list"
  | [x]     => x
  | x :: xs => cell x (C xs)

/-- Call a Hoon gate on an argument.
    Replaces sample (axis 6) with `arg`, then fires arm 2. -/
def callGate (gate : Noun) (arg : Noun) : Noun :=
  nock gate
    (C [atom 9, atom 2,
        C [atom 10, C [atom 6, C [atom 1, arg]],
           C [atom 0, atom 1]]])

/-! ## `++dec` — decrement -/

/-- The Nock formula for `++dec`, compiled from:
    ```hoon
    ~/  %dec
    |=  a=@
    ~_  leaf+"decrement-underflow"
    ?<  =(0 a)
    =+  b=0
    |-  ^-  @
    ?:  =(a +(b))  b
    $(b +(b))
    ``` -/
def decFormula : Noun :=
  -- "decrement-underflow" string encoded as a list of atom bytes
  let errStr : Noun :=
    C [atom 1, atom 1,
       atom 100, atom 101, atom 99, atom 114, atom 101, atom 109,
       atom 101, atom 110, atom 116, atom 45, atom 117, atom 110,
       atom 100, atom 101, atom 114, atom 102, atom 108, atom 111,
       atom 119, atom 0]
  -- The error hint formula wrapping the underflow message
  let errHint : Noun :=
    C [atom 1, C [atom 1, atom 1717658988],
       atom 7, C [atom 0, atom 1],
       atom 8, errStr,
       atom 9, atom 2, atom 0, atom 1]
  -- Static hint cell: [%bell errHint 0 1]
  let hintCell : Noun :=
    C [atom 1851876717, errHint, atom 0, atom 1]
  -- The loop body (quoted): [6 =(a +(b)) b $(b +(b))]
  let loopBody : Noun :=
    C [atom 1, atom 6,
       -- condition: =(a +(b))  — a is at axis 30, b at axis 6
       C [atom 5, C [atom 0, atom 30], atom 4, atom 0, atom 6],
       -- then: return b
       C [atom 0, atom 6],
       -- else: recurse with b ← +(b)
       atom 9, atom 2, atom 10,
       C [atom 6, atom 4, atom 0, atom 6],
       atom 0, atom 1]
  -- The gate body: underflow guard + push b=0 + push loop + fire
  let gateBody : Noun :=
    C [atom 1, atom 11, hintCell,
       atom 6, C [atom 5, C [atom 1, atom 0], atom 0, atom 6],
       C [atom 0, atom 0],
       atom 8, C [atom 1, atom 0],
       atom 8, loopBody,
       atom 9, atom 2, atom 0, atom 1]
  -- Outer structure: [8 [1 0] gateBody 0 1] — push default sample 0
  let inner : Noun :=
    C [atom 8, C [atom 1, atom 0], gateBody, atom 0, atom 1]
  -- Jet hint: [%dec 1 6514020 [0 7] 0]  (1953718630 = %dec as an atom)
  let jetHint : Noun :=
    C [atom 1953718630, atom 1, atom 6514020, C [atom 0, atom 7], atom 0]
  -- Top-level: [7 inner 11 jetHint 0 1]
  C [atom 7, inner, atom 11, jetHint, atom 0, atom 1]

/-- The `++dec` gate, obtained by running `decFormula` against a trivial subject. -/
def decGate : Noun := nock (atom 0) decFormula

section DecEval

-- Keep n small: dec loops n times (O(n) Nock steps)
#eval callGate decGate (atom 3)   -- expect: atom 2
#eval callGate decGate (atom 1)   -- expect: atom 0

end DecEval

/-! ### Kernel-transparent forms of the dec gate

    `decGate` is computed by `nock` (`partial def`), so the Lean kernel
    cannot inspect its structure.  We pin it down with explicit `n!` literals
    and verify equality via `native_decide`.  This is the bridge between the
    opaque runtime and the transparent proof terms. -/

/-- Battery of the `++dec` gate (axis 2 of `decGate`), as a kernel-visible term. -/
def decBat : Noun :=
  n! "[11 [[1851876717 [[1 [[1 1717658988] [7 [[0 1] [8 [[1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 [2 [0 1]]]]]]]]] [0 1]]] [6 [[5 [[1 0] [0 6]]] [[0 0] [8 [[1 0] [8 [[1 [6 [[5 [[0 30] [4 [0 6]]]] [[0 6] [9 [2 [10 [[6 [4 [0 6]]] [0 1]]]]]]]]] [9 [2 [0 1]]]]]]]]]]]]"

/-- The `++dec` gate as a kernel-visible `n!` term: `[battery [sample context]]`. -/
def decGate' : Noun :=
  n! "[[11 [[1851876717 [[1 [[1 1717658988] [7 [[0 1] [8 [[1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 [2 [0 1]]]]]]]]] [0 1]]] [6 [[5 [[1 0] [0 6]]] [[0 0] [8 [[1 0] [8 [[1 [6 [[5 [[0 30] [4 [0 6]]]] [[0 6] [9 [2 [10 [[6 [4 [0 6]]] [0 1]]]]]]]]] [9 [2 [0 1]]]]]]]]]]]] 0 0]"

/-- The runtime-computed `decGate` equals the kernel-visible `n!` form.
    This assertion bridges the opaque `nock` evaluator and transparent proofs. -/
theorem decGate_eq : decGate = decGate' := by native_decide

/-- The battery extracted from `decGate` equals the explicit `n!` literal. -/
theorem decBat_eq : fas (atom 2) decGate = decBat := by native_decide

/-- Calling gate `[bat [sam ctx]]` with `arg` is equivalent (via NockEval) to
    running the battery against the sample-replaced core `[bat [arg ctx]]`.
    This is the formal gate-call lemma: the hypothesis is what you need to
    prove; the conclusion is what `callGate` does at the formula level. -/
theorem callGate_gate_eval (bat sam ctx arg r : Noun)
    (h : NockEval (cell bat (cell arg ctx)) bat r) :
    NockEval (cell bat (cell sam ctx))
             (C [atom 9, atom 2,
                 C [atom 10, C [atom 6, C [atom 1, arg]],
                    C [atom 0, atom 1]]])
             r := by
  simp only [C]
  -- op9: evaluate [10 [6 [1 arg]] [0 1]] to get the edited core, then run arm 2
  apply NockEval.op9
  · -- Step 1: NockEval gate [10 [6 [1 arg]] [0 1]] (cell bat (cell arg ctx))
    have e1 : NockEval (cell bat (cell sam ctx)) (cell (atom 1) arg) arg :=
      NockEval.op1
    have e2 : NockEval (cell bat (cell sam ctx)) (cell (atom 0) (atom 1))
                       (cell bat (cell sam ctx)) := by
      have h2 := @NockEval.op0 (cell bat (cell sam ctx)) (atom 1)
      rw [fas_one] at h2; exact h2
    have e10 : NockEval (cell bat (cell sam ctx))
                   (cell (atom 10) (cell (cell (atom 6) (cell (atom 1) arg))
                                        (cell (atom 0) (atom 1))))
                   (hax (atom 6) arg (cell bat (cell sam ctx))) :=
      NockEval.op10 e1 e2
    rw [hax_six] at e10; exact e10
  · -- Step 2: NockEval (cell bat (cell arg ctx)) (fas 2 (cell bat (cell arg ctx))) r
    rw [fas_head]; exact h
