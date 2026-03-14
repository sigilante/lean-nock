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

/-! ## `++dec` correctness proof

We prove that the compiled Nock formula for `++dec`, when called with
argument `n + 1`, produces `atom n` via a valid `NockEval` derivation.

### Proof structure

The dec gate's battery (`decBat`) executes:
1. **op11 dynamic hint** — discarded (the `~/` jet hint)
2. **op6 guard** — tests `=(0, sample)`; crashes on zero, continues otherwise
3. **op8 push b=0** — initializes the loop counter
4. **op8 push loopBat** — installs the loop body formula
5. **op9 fire** — enters the loop

The loop core has subject `[loopBat [b [decBat [n ctx]]]]` where:
- axis 2 = loopBat (loop battery)
- axis 6 = b (counter, starts at 0)
- axis 30 = n (original argument, invariant)

Each iteration tests `=(n, +(b))`; if equal, returns `b`; otherwise
recurses with `b ← b+1` via op10 edit + op9 fire.
-/

/-- The loop body formula for `++dec`: tests `=(a, +(b))`, returns `b` if
    equal, otherwise recurses with `b ← +(b)`. -/
def decLoopBat : Noun :=
  n! "[6 [5 [0 30] [4 [0 6]]] [0 6] [9 2 [10 [6 [4 [0 6]]] [0 1]]]]"

/-- The loop core for `++dec`: `[loopBat [b [decBat [n ctx]]]]`. -/
def decLoopCore (b n : Nat) (ctx : Noun) : Noun :=
  cell decLoopBat (cell (atom b) (cell decBat (cell (atom n) ctx)))

-- Structural decomposition of decBat into hint + guard + loop components.
-- These are definitional equalities (verified by rfl or native_decide).

private def decBat_hintF : Noun :=
  n! "[[1 [[1 1717658988] [7 [[0 1] [8 [[1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 [2 [0 1]]]]]]]]] [0 1]]"

private def decBat_guardBody : Noun :=
  n! "[6 [5 [1 0] [0 6]] [[0 0] [8 [1 0] [8 [1 [6 [5 [0 30] [4 [0 6]]] [0 6] [9 2 [10 [6 [4 [0 6]]] [0 1]]]]] [9 2 [0 1]]]]]]"

private def decBat_pushLoop : Noun :=
  n! "[8 [1 0] [8 [1 [6 [5 [0 30] [4 [0 6]]] [0 6] [9 2 [10 [6 [4 [0 6]]] [0 1]]]]] [9 2 [0 1]]]]"

private theorem guardBody_parts : decBat_guardBody = cell (atom 6) (cell
    (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 6))))
    (cell (cell (atom 0) (atom 0)) decBat_pushLoop)) := by native_decide

private theorem pushLoop_parts : decBat_pushLoop = cell (atom 8) (cell (cell (atom 1) (atom 0))
    (cell (atom 8) (cell (cell (atom 1) decLoopBat)
      (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1))))))) := by native_decide

-- Loop invariant helpers

private theorem dec_cond_eval (b n : Nat) (ctx : Noun) :
    NockEval (decLoopCore b n ctx)
      (cell (atom 5) (cell (cell (atom 0) (atom 30)) (cell (atom 4) (cell (atom 0) (atom 6)))))
      (tis (cell (atom n) (lus (atom b)))) := by
  apply NockEval.op5
  · have h := @NockEval.op0 (decLoopCore b n ctx) (atom 30)
    simp [decLoopCore, fas] at h; exact h
  · exact NockEval.op4 (by
      have h := @NockEval.op0 (decLoopCore b n ctx) (atom 6)
      simp [decLoopCore, fas] at h; exact h)

private theorem dec_slot6_eval (b n : Nat) (ctx : Noun) :
    NockEval (decLoopCore b n ctx) (cell (atom 0) (atom 6)) (atom b) := by
  have h := @NockEval.op0 (decLoopCore b n ctx) (atom 6)
  simp [decLoopCore, fas] at h; exact h

private theorem dec_edit_core (b n : Nat) (ctx : Noun) :
    NockEval (decLoopCore b n ctx)
      (cell (atom 10) (cell (cell (atom 6) (cell (atom 4) (cell (atom 0) (atom 6))))
                            (cell (atom 0) (atom 1))))
      (decLoopCore (b + 1) n ctx) := by
  have slot1 : NockEval (decLoopCore b n ctx) (cell (atom 0) (atom 1)) (decLoopCore b n ctx) := by
    have h := @NockEval.op0 (decLoopCore b n ctx) (atom 1)
    simp [decLoopCore, fas] at h; exact h
  have edit := @NockEval.op10 _ (atom 6) _ _ (lus (atom b)) (decLoopCore b n ctx)
    (NockEval.op4 (dec_slot6_eval b n ctx)) slot1
  have : hax (atom 6) (lus (atom b)) (decLoopCore b n ctx) = decLoopCore (b + 1) n ctx := by
    simp [decLoopCore, lus, hax_six, Nat.add_comm]
  rw [this] at edit; exact edit

private theorem tis_eq_true (b : Nat) :
    tis (cell (atom (b + 1)) (lus (atom b))) = atom 0 := by
  simp [lus, tis]; omega

private theorem tis_eq_false (b n : Nat) (h : b + 1 < n) :
    tis (cell (atom n) (lus (atom b))) = atom 1 := by
  simp [lus, tis]; omega

/-- **Dec loop invariant.** Running the loop battery against the loop core
    `[loopBat [b [decBat [n ctx]]]]` where `b < n` produces `atom (n - 1)`.

    Proved by induction on `n - b - 1` (remaining iterations). -/
theorem dec_loop_inv (b n : Nat) (ctx : Noun) (hb : b < n) :
    NockEval (decLoopCore b n ctx) decLoopBat (atom (n - 1)) := by
  obtain ⟨d, hd⟩ : ∃ d, n = b + 1 + d := ⟨n - b - 1, by omega⟩
  subst hd
  induction d generalizing b with
  | zero =>
    -- Base: n = b + 1, condition =(n, +(b)) is true, return b
    simp only [Nat.add_zero, show b + 1 - 1 = b from by omega]
    change NockEval (decLoopCore b (b + 1) ctx)
      (cell (atom 6) (cell _ (cell _ _))) (atom b)
    apply NockEval.op6_then
    · have h := dec_cond_eval b (b + 1) ctx
      rw [tis_eq_true] at h; exact h
    · exact dec_slot6_eval b (b + 1) ctx
  | succ d ih =>
    -- Step: n = b + 2 + d, condition false, recurse with b+1
    simp only [show b + 1 + (d + 1) - 1 = b + 1 + d from by omega]
    change NockEval (decLoopCore b (b + 1 + (d + 1)) ctx)
      (cell (atom 6) (cell _ (cell _ _))) (atom (b + 1 + d))
    apply NockEval.op6_else
    · have h := dec_cond_eval b (b + 1 + (d + 1)) ctx
      rw [tis_eq_false b (b + 1 + (d + 1)) (by omega)] at h; exact h
    · -- Else: [9 2 [10 [6 [4 [0 6]]] [0 1]]] — edit b → b+1, fire
      apply @NockEval.op9 _ (atom 2) _ (decLoopCore (b + 1) (b + 1 + (d + 1)) ctx)
      · exact dec_edit_core b (b + 1 + (d + 1)) ctx
      · rw [show fas (atom 2) (decLoopCore (b+1) (b+1+(d+1)) ctx) = decLoopBat
              from by simp [decLoopCore, fas]]
        have h1 : b + 1 + (d + 1) = (b + 1) + 1 + d := by omega
        rw [h1]
        have := ih (b + 1) (by omega)
        rwa [show (b + 1) + 1 + d - 1 = b + 1 + d from by omega] at this

/-- **Dec correctness.** Running the `++dec` battery against a gate core
    `[decBat [n+1 ctx]]` produces `atom n` via a valid `NockEval` derivation.

    Combined with `callGate_gate_eval`, this proves that calling `++dec`
    on any positive atom computes the correct decrement. -/
theorem dec_correct (n : Nat) (ctx : Noun) :
    NockEval (cell decBat (cell (atom (n + 1)) ctx)) decBat (atom n) := by
  -- Decompose formula via definitional equality (subject stays abstract)
  show NockEval (cell decBat (cell (atom (n + 1)) ctx))
    (cell (atom 11) (cell (cell (atom 1851876717) decBat_hintF) decBat_guardBody)) (atom n)
  -- Step 1: op11_dynamic — discard jet hint
  apply @NockEval.op11_dynamic _ (atom 1851876717) _ _ _ (atom n)
  · simp only [decBat_hintF]
    exact NockEval.autocons NockEval.op1
      (by have h := @NockEval.op0 (cell decBat (cell (atom (n + 1)) ctx)) (atom 1)
          rw [fas_one] at h; exact h)
  · -- Step 2: op6_else — underflow guard (n+1 ≠ 0)
    rw [guardBody_parts]
    apply NockEval.op6_else
    · have h0 : NockEval (cell decBat (cell (atom (n+1)) ctx))
                  (cell (atom 1) (atom 0)) (atom 0) := NockEval.op1
      have h6 : NockEval (cell decBat (cell (atom (n+1)) ctx))
                  (cell (atom 0) (atom 6)) (atom (n + 1)) := by
        have h := @NockEval.op0 (cell decBat (cell (atom (n+1)) ctx)) (atom 6)
        simp [fas] at h; exact h
      have eq := NockEval.op5 h0 h6; simp [tis] at eq; exact eq
    · -- Steps 3-5: push b=0, push loopBat, fire loop
      rw [pushLoop_parts]
      apply NockEval.op8 NockEval.op1  -- push b=0
      apply NockEval.op8 NockEval.op1  -- push loopBat (quoted by [1 loopBat])
      -- Subject is now decLoopCore 0 (n+1) ctx (definitionally)
      show NockEval (decLoopCore 0 (n + 1) ctx)
        (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) (atom n)
      apply @NockEval.op9 _ (atom 2) _ (decLoopCore 0 (n + 1) ctx)
      · -- [0 1] → loop core
        have h := @NockEval.op0 (decLoopCore 0 (n + 1) ctx) (atom 1)
        rw [fas_one] at h; exact h
      · -- fas 2 core = decLoopBat; apply loop invariant
        rw [show fas (atom 2) (decLoopCore 0 (n + 1) ctx) = decLoopBat
              from by simp [decLoopCore, fas]]
        have h := dec_loop_inv 0 (n + 1) ctx (by omega)
        simp at h; exact h

/-! ## `++add` — unsigned addition

The `++add` gate takes a pair `[a b]` and computes `a + b`.  Its loop body
decrements `a` while incrementing `b` until `a` reaches zero:

```hoon
|=  [a=@ b=@]
?:  =(0 a)  b
$(a (dec a), b +(b))
```

The compiled Nock calls `++dec` by axis lookup into the Hoon standard library
context (axis 2398 of axis 8191).  We abstract over this dependency: the
`AddCtx` structure asserts that the dec-calling subformula computes correct
decrements.  This cleanly separates arithmetic correctness from core wiring.
-/

/-- The battery (loop body) formula for `++add`. -/
def addBat : Noun :=
  n! "[6 [5 [1 0] [0 12]] [0 13] [9 2 [10 [6 [[8 [9 2398 [0 8191]] [9 2 [10 [6 [0 28]] [0 2]]]] [4 [0 13]]]] [0 1]]]]"

/-- The add loop core: `[addBat [[a b] ctx]]`. -/
def addLoopCore (a b : Nat) (ctx : Noun) : Noun :=
  cell addBat (cell (cell (atom a) (atom b)) ctx)

/-- The dec-calling subformula within add's loop body.
    Navigates to `++dec` at axis 2398 of axis 8191 in the context,
    then calls it with the current `a` value. -/
def addDecCallF : Noun :=
  n! "[8 [9 2398 [0 8191]] [9 2 [10 [6 [0 28]] [0 2]]]]"

/-- A context supports `++add` if the dec-calling mechanism within the
    add loop core produces correct decrements for any positive `a`. -/
structure AddCtx (ctx : Noun) where
  dec_call : ∀ (a b : Nat), a > 0 →
    NockEval (addLoopCore a b ctx) addDecCallF (atom (a - 1))

/-- **Add loop invariant.** Running the add battery against the loop core
    `[addBat [[a b] ctx]]` produces `atom (a + b)`.

    Proved by induction on `a` (which decreases each iteration).
    The dec-calling mechanism is abstracted via `AddCtx`. -/
theorem add_loop_inv (a b : Nat) (ctx : Noun) (hctx : AddCtx ctx) :
    NockEval (addLoopCore a b ctx) addBat (atom (a + b)) := by
  -- Lift b into the IH by proving ∀ b first
  suffices h : ∀ b, NockEval (addLoopCore a b ctx) addBat (atom (a + b)) from h b
  induction a with
  | zero =>
    -- a = 0: condition =(0, 0) true, return b
    intro b; simp
    change NockEval (addLoopCore 0 b ctx) (cell (atom 6) (cell _ (cell _ _))) (atom b)
    apply NockEval.op6_then
    · have : NockEval (addLoopCore 0 b ctx)
          (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 12))))
          (tis (cell (atom 0) (atom 0))) := by
        apply NockEval.op5; exact NockEval.op1
        have h := @NockEval.op0 (addLoopCore 0 b ctx) (atom 12)
        simp [addLoopCore, fas] at h; exact h
      simp [tis] at this; exact this
    · have h := @NockEval.op0 (addLoopCore 0 b ctx) (atom 13)
      simp [addLoopCore, fas] at h; exact h
  | succ a ih =>
    -- a = k+1: condition false, recurse with [k, b+1]
    intro b
    change NockEval (addLoopCore (a + 1) b ctx)
      (cell (atom 6) (cell _ (cell _ _))) (atom (a + 1 + b))
    apply NockEval.op6_else
    · have : NockEval (addLoopCore (a+1) b ctx)
          (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 12))))
          (tis (cell (atom 0) (atom (a+1)))) := by
        apply NockEval.op5; exact NockEval.op1
        have h := @NockEval.op0 (addLoopCore (a+1) b ctx) (atom 12)
        simp [addLoopCore, fas] at h; exact h
      simp [tis] at this; exact this
    · -- Edit sample to [dec(a+1), +(b)] = [a, b+1], fire battery
      apply @NockEval.op9 _ (atom 2) _ (addLoopCore a (1 + b) ctx)
      · -- op10: build new sample via autocons [dec_call, op4]
        have slot13 : NockEval (addLoopCore (a+1) b ctx)
            (cell (atom 0) (atom 13)) (atom b) := by
          have h := @NockEval.op0 (addLoopCore (a+1) b ctx) (atom 13)
          simp [addLoopCore, fas] at h; exact h
        have dec_a : NockEval (addLoopCore (a+1) b ctx) addDecCallF (atom a) := by
          have h := hctx.dec_call (a + 1) b (by omega); simp at h; exact h
        have new_sam := NockEval.autocons dec_a (NockEval.op4 slot13)
        have slot1 : NockEval (addLoopCore (a+1) b ctx)
            (cell (atom 0) (atom 1)) (addLoopCore (a+1) b ctx) := by
          have h := @NockEval.op0 (addLoopCore (a+1) b ctx) (atom 1)
          simp [addLoopCore, fas] at h; exact h
        have edit := @NockEval.op10 _ (atom 6) _ _
          (cell (atom a) (atom (1 + b))) (addLoopCore (a+1) b ctx) new_sam slot1
        have : hax (atom 6) (cell (atom a) (atom (1 + b))) (addLoopCore (a+1) b ctx) =
            addLoopCore a (1 + b) ctx := by simp [addLoopCore, hax_six]
        rw [this] at edit; exact edit
      · -- Fire: fas 2 core = addBat, apply IH
        rw [show fas (atom 2) (addLoopCore a (1 + b) ctx) = addBat
              from by simp [addLoopCore, fas]]
        have := ih (1 + b)
        rwa [show a + (1 + b) = a + 1 + b from by omega] at this

/-- **Add correctness.** Running the `++add` battery against a gate core
    `[addBat [[m n] ctx]]` produces `atom (m + n)`, given a context where
    the dec-calling mechanism works (`AddCtx`).

    Combined with `callGate_gate_eval`, this proves that calling `++add`
    on any pair of atoms computes the correct sum. -/
theorem add_correct (m n : Nat) (ctx : Noun) (hctx : AddCtx ctx) :
    NockEval (cell addBat (cell (cell (atom m) (atom n)) ctx)) addBat (atom (m + n)) :=
  add_loop_inv m n ctx hctx

/-! ## `++sub` — unsigned subtraction

The `++sub` gate takes a pair `[a b]` and computes `a - b`.  Its loop body
decrements both `a` and `b` until `b` reaches zero:

```hoon
~/  %sub
|=  [a=@ b=@]
~_  leaf+"subtract-underflow"
?:  =(0 b)  a
$(a (dec a), b (dec b))
```

Like `++add`, the compiled Nock calls `++dec` by axis lookup.  We abstract
via `SubCtx`.  The battery wraps the entire loop body in a `~_` hint
(op11_dynamic) which fires on every iteration.

When `b > a`, the gate crashes (attempts `dec 0`).  We model this by
restricting the theorem to `b ≤ a`: no `NockEval` derivation exists for
the crash case.
-/

/-- Dec-calling subformula for `a` (axis 28) within sub's loop. -/
def subDecCallA : Noun :=
  n! "[8 [9 2398 [0 8191]] [9 2 [10 [6 [0 28]] [0 2]]]]"

/-- Dec-calling subformula for `b` (axis 29) within sub's loop. -/
def subDecCallB : Noun :=
  n! "[8 [9 2398 [0 8191]] [9 2 [10 [6 [0 29]] [0 2]]]]"

/-- The inner loop formula for `++sub` (condition + body, without hint wrapper). -/
def subInnerBat : Noun :=
  n! "[6 [5 [1 0] [0 13]] [0 12] [9 2 [10 [6 [[8 [9 2398 [0 8191]] [9 2 [10 [6 [0 28]] [0 2]]]] [8 [9 2398 [0 8191]] [9 2 [10 [6 [0 29]] [0 2]]]]]] [0 1]]]]"

/-- The hint clue formula for `~_ leaf+"subtract-underflow"`. -/
private def subHintClueF : Noun :=
  n! "[[1 [1 1717658988] 7 [0 1] 8 [1 1 115 117 98 116 114 97 99 116 45 117 110 100 101 114 102 108 111 119 0] 9 2 0 1] [0 1]]"

/-- The battery for `++sub`: hint-wrapped loop body.
    Defined structurally so that op11_dynamic decomposition is definitional. -/
def subBat : Noun :=
  cell (atom 11) (cell (cell (atom 1851876717) subHintClueF) subInnerBat)

/-- The sub loop core: `[subBat [[a b] ctx]]`. -/
def subLoopCore (a b : Nat) (ctx : Noun) : Noun :=
  cell subBat (cell (cell (atom a) (atom b)) ctx)

/-- A context supports `++sub` if the dec-calling mechanism produces
    correct decrements for both arguments. -/
structure SubCtx (ctx : Noun) where
  dec_call_a : ∀ (a b : Nat), a > 0 →
    NockEval (subLoopCore a b ctx) subDecCallA (atom (a - 1))
  dec_call_b : ∀ (a b : Nat), b > 0 →
    NockEval (subLoopCore a b ctx) subDecCallB (atom (b - 1))

/-- **Sub loop invariant / correctness.** Running the `++sub` battery against
    `[subBat [[a b] ctx]]` where `b ≤ a` produces `atom (a - b)`.

    The loop decrements both `a` and `b` until `b` reaches 0, then returns `a`.
    A `~_` hint fires every iteration (stripped by op11_dynamic).

    Proved by induction on `b`.  The dec-calling mechanism is abstracted
    via `SubCtx`. -/
theorem sub_loop_inv (a b : Nat) (ctx : Noun) (hctx : SubCtx ctx) (hab : b ≤ a) :
    NockEval (subLoopCore a b ctx) subBat (atom (a - b)) := by
  revert a
  induction b with
  | zero =>
    intro a _; simp only [Nat.sub_zero]
    -- subBat = [11 [tag hintClue] subInnerBat] — strip hint via op11_dynamic
    apply NockEval.op11_dynamic
    · exact NockEval.autocons NockEval.op1
        (by have h := @NockEval.op0 (subLoopCore a 0 ctx) (atom 1); rw [fas_one] at h; exact h)
    · -- subInnerBat = [6 cond then else]; b=0 so condition is true
      change NockEval (subLoopCore a 0 ctx) (cell (atom 6) (cell _ (cell _ _))) (atom a)
      apply NockEval.op6_then
      · have : NockEval (subLoopCore a 0 ctx)
            (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 13))))
            (tis (cell (atom 0) (atom 0))) := by
          apply NockEval.op5; exact NockEval.op1
          have h := @NockEval.op0 (subLoopCore a 0 ctx) (atom 13)
          simp [subLoopCore, fas] at h; exact h
        simp [tis] at this; exact this
      · have h := @NockEval.op0 (subLoopCore a 0 ctx) (atom 12)
        simp [subLoopCore, fas] at h; exact h
  | succ b ih =>
    intro a hab
    -- Strip hint
    apply NockEval.op11_dynamic
    · exact NockEval.autocons NockEval.op1
        (by have h := @NockEval.op0 (subLoopCore a (b + 1) ctx) (atom 1)
            rw [fas_one] at h; exact h)
    · -- b+1 ≠ 0: condition false
      change NockEval (subLoopCore a (b + 1) ctx)
        (cell (atom 6) (cell _ (cell _ _))) (atom (a - (b + 1)))
      apply NockEval.op6_else
      · have : NockEval (subLoopCore a (b + 1) ctx)
            (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 13))))
            (tis (cell (atom 0) (atom (b + 1)))) := by
          apply NockEval.op5; exact NockEval.op1
          have h := @NockEval.op0 (subLoopCore a (b + 1) ctx) (atom 13)
          simp [subLoopCore, fas] at h; exact h
        simp [tis] at this; exact this
      · -- Recurse: [9 2 [10 [6 [DEC_A DEC_B]] [0 1]]]
        apply @NockEval.op9 _ (atom 2) _ (subLoopCore (a - 1) b ctx)
        · -- op10: edit sample [a, b+1] → [a-1, b]
          have dec_a := hctx.dec_call_a a (b + 1) (by omega)
          have dec_b := hctx.dec_call_b a (b + 1) (by omega)
          rw [show (b + 1) - 1 = b from by omega] at dec_b
          have new_sam := NockEval.autocons dec_a dec_b
          have slot1 : NockEval (subLoopCore a (b + 1) ctx)
              (cell (atom 0) (atom 1)) (subLoopCore a (b + 1) ctx) := by
            have h := @NockEval.op0 (subLoopCore a (b + 1) ctx) (atom 1)
            rw [fas_one] at h; exact h
          have edit := @NockEval.op10 _ (atom 6) _ _
            (cell (atom (a - 1)) (atom b)) (subLoopCore a (b + 1) ctx) new_sam slot1
          have : hax (atom 6) (cell (atom (a - 1)) (atom b)) (subLoopCore a (b + 1) ctx) =
              subLoopCore (a - 1) b ctx := by simp [subLoopCore, hax_six]
          rw [this] at edit; exact edit
        · -- Fire: fas 2 core = subBat, apply IH
          rw [show fas (atom 2) (subLoopCore (a - 1) b ctx) = subBat
                from by simp [subLoopCore, fas]]
          have := ih (a - 1) (by omega)
          rwa [show (a - 1) - b = a - (b + 1) from by omega] at this

/-- **Sub correctness.** Running `++sub` on `[a b]` with `b ≤ a` produces `a - b`.
    The dec-calling mechanism is abstracted via `SubCtx`. -/
theorem sub_correct (a b : Nat) (ctx : Noun) (hctx : SubCtx ctx) (hab : b ≤ a) :
    NockEval (cell subBat (cell (cell (atom a) (atom b)) ctx)) subBat (atom (a - b)) :=
  sub_loop_inv a b ctx hctx hab
