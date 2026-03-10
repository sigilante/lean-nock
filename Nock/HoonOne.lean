import Nock.Basic
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
