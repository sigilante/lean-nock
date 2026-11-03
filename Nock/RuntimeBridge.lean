import Nock.Basic
import Nock.Proofs
import Nock.Notation
import Nock.HoonOne

namespace Nock
open Noun

/-!
# Runtime / prover bridge

**Nothing in the proof chain may import this file.**  `Main.lean` may.

The theorems here depend on `Lean.ofReduceBool` via `native_decide`: they are
checked by *running compiled code*, not by the Lean kernel.  That is an
appropriate trust assumption for a bridge between an opaque runtime evaluator
and the transparent proof terms, but it is not one we want anywhere near
`dec_correct`.  Keeping the `native_decide` uses in a leaf module means
`#print axioms dec_correct` stays free of `ofReduceBool`, and the grep gate

    grep -rn native_decide Nock/

has exactly this file as its only hit.

`decGate` is computed by `partial def nock`, which the Lean kernel cannot
inspect.  `decGate'` and `decBat` (in `Nock.HoonOne`) pin the same nouns down
as kernel-visible `n!` literals.  The theorems below assert the two agree.
-/

/-- Call a Hoon gate on an argument.
    Replaces sample (axis 6) with `arg`, then fires arm 2. -/
def callGate (gate : Noun) (arg : Noun) : Noun :=
  nock gate
    (C [atom 9, atom 2,
        C [atom 10, C [atom 6, C [atom 1, arg]],
           C [atom 0, atom 1]]])

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

/-- The `++dec` gate as a kernel-visible `n!` term: `[battery [sample context]]`. -/
def decGate' : Noun :=
  n! "[[11 [[1851876717 [[1 [[1 1717658988] [7 [[0 1] [8 [[1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 [2 [0 1]]]]]]]]] [0 1]]] [6 [[5 [[1 0] [0 6]]] [[0 0] [8 [[1 0] [8 [[1 [6 [[5 [[0 30] [4 [0 6]]]] [[0 6] [9 [2 [10 [[6 [4 [0 6]]] [0 1]]]]]]]]] [9 [2 [0 1]]]]]]]]]]]] 0 0]"

section DecEval

-- Keep n small: dec loops n times (O(n) Nock steps)
#eval callGate decGate (atom 3)   -- expect: atom 2
#eval callGate decGate (atom 1)   -- expect: atom 0

end DecEval

/-- The runtime-computed `decGate` equals the kernel-visible `n!` form.
    Bridges the opaque `nock` evaluator and the transparent proof terms. -/
theorem decGate_eq : decGate = decGate' := by native_decide

/-- The battery extracted from `decGate` equals the explicit `n!` literal
    `decBat` that `dec_correct` reasons about. -/
theorem decBat_eq : fasO (atom 2) decGate = some decBat := by native_decide

end Nock
