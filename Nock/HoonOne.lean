import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Notation

namespace Nock
open Noun

/-!
# Hoon %one Core — Nock Formulas

Nock formulas compiled from Hoon's standard library arms, obtained via
`!=` (zapwut) in the Hoon dojo.  Atom thousands-separators (dots) removed.

Convention: `C [a, b, c, d]` = `cell a (cell b (cell c d))`, mirroring
Hoon's right-associative bracket notation.

This file is proof-facing: it contains no `native_decide` and no `panic!`.
The runtime evaluator, the `decFormula → decGate` computation, and the two
`native_decide` bridge theorems live in `Nock.RuntimeBridge`, which nothing
here imports.
-/

/-- Right-associative cell list: mirrors `[a b c]` = `[a [b c]]` in Hoon/Nock.

    The `[]` arm is unreachable — every call site is a literal of length ≥ 1 —
    and is given an explicit value rather than `panic!` so that no proof-facing
    definition can consume `Inhabited.default`. -/
def C : List Noun → Noun
  | []      => atom 0
  | [x]     => x
  | x :: xs => cell x (C xs)

/-! ## `++dec` — decrement -/

/-- Battery of the `++dec` gate (axis 2 of the gate), as a kernel-visible term. -/
def decBat : Noun :=
  n! "[11 [[1851876717 [[1 [[1 1717658988] [7 [[0 1] [8 [[1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 [2 [0 1]]]]]]]]] [0 1]]] [6 [[5 [[1 0] [0 6]]] [[0 0] [8 [[1 0] [8 [[1 [6 [[5 [[0 30] [4 [0 6]]]] [[0 6] [9 [2 [10 [[6 [4 [0 6]]] [0 1]]]]]]]]] [9 [2 [0 1]]]]]]]]]]]]"

/-- Calling gate `[bat [sam ctx]]` with `arg` is equivalent (via NockEval) to
    running the battery against the sample-replaced core `[bat [arg ctx]]`.

    Stated for an arbitrary `Outcome o` in tail position: the op9/op10 chain is
    outcome-polymorphic, so this covers the crashing call as well as the
    returning one. -/
theorem callGate_gate_eval (bat sam ctx arg : Noun) {o : Outcome}
    (h : NockEval (cell bat (cell arg ctx)) bat o) :
    NockEval (cell bat (cell sam ctx))
             (C [atom 9, atom 2,
                 C [atom 10, C [atom 6, C [atom 1, arg]],
                    C [atom 0, atom 1]]])
             o := by
  simp only [C]
  -- op9: evaluate [10 [6 [1 arg]] [0 1]] to the edited core, then run arm 2
  refine NockEval.op9 ?_ (fasO_head bat (cell arg ctx)) h
  exact NockEval.op10 (NockEval.op0 (fasO_one _)) NockEval.op1 (haxO_six arg bat sam ctx)

/-! ## `++dec` correctness proof

We prove that the compiled Nock formula for `++dec`, when called with
argument `n + 1`, produces `atom n` via a valid `NockEval` derivation, and
that when called with `0` it produces `Outcome.exit` — a genuine crash.

### Proof structure

The dec gate's battery (`decBat`) executes:
1. **op11 dynamic hint** — discarded (the `~_` underflow hint)
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
-- `n!` elaborates to raw constructors, so these close by `rfl` and contribute
-- no axioms.  (The old proofs used `native_decide` here, which pulled in
-- `Lean.ofReduceBool`.)

def decBat_hintF : Noun :=
  n! "[[1 [[1 1717658988] [7 [[0 1] [8 [[1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 [2 [0 1]]]]]]]]] [0 1]]"

def decBat_guardBody : Noun :=
  n! "[6 [5 [1 0] [0 6]] [[0 0] [8 [1 0] [8 [1 [6 [5 [0 30] [4 [0 6]]] [0 6] [9 2 [10 [6 [4 [0 6]]] [0 1]]]]] [9 2 [0 1]]]]]]"

def decBat_pushLoop : Noun :=
  n! "[8 [1 0] [8 [1 [6 [5 [0 30] [4 [0 6]]] [0 6] [9 2 [10 [6 [4 [0 6]]] [0 1]]]]] [9 2 [0 1]]]]"

theorem guardBody_parts : decBat_guardBody = cell (atom 6) (cell
    (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 6))))
    (cell (cell (atom 0) (atom 0)) decBat_pushLoop)) := rfl

theorem pushLoop_parts : decBat_pushLoop = cell (atom 8) (cell (cell (atom 1) (atom 0))
    (cell (atom 8) (cell (cell (atom 1) decLoopBat)
      (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1))))))) := rfl

/-- The `~_` hint clue is a static cons, so it evaluates to a value whatever
    the subject.  Its value is discarded by `op11_dynamic`. -/
theorem dec_hint_eval (s : Noun) :
    ∃ r, NockEval s decBat_hintF (.val r) :=
  ⟨_, NockEval.autocons NockEval.op1 (NockEval.op0 (fasO_one s))⟩

-- Loop invariant helpers

private theorem dec_slot6_eval (b n : Nat) (ctx : Noun) :
    NockEval (decLoopCore b n ctx) (cell (atom 0) (atom 6)) (.val (atom b)) :=
  NockEval.op0 (by simp [decLoopCore, fasO])

private theorem dec_cond_eval (b n : Nat) (ctx : Noun) :
    NockEval (decLoopCore b n ctx)
      (cell (atom 5) (cell (cell (atom 0) (atom 30)) (cell (atom 4) (cell (atom 0) (atom 6)))))
      (.val (tisN (atom n) (atom (1 + b)))) :=
  NockEval.op5
    (NockEval.op0 (by simp [decLoopCore, fasO]))
    (NockEval.op4 (dec_slot6_eval b n ctx) (lusO_atom b))

private theorem dec_edit_core (b n : Nat) (ctx : Noun) :
    NockEval (decLoopCore b n ctx)
      (cell (atom 10) (cell (cell (atom 6) (cell (atom 4) (cell (atom 0) (atom 6))))
                            (cell (atom 0) (atom 1))))
      (.val (decLoopCore (b + 1) n ctx)) := by
  refine NockEval.op10
    (NockEval.op0 (fasO_one _))
    (NockEval.op4 (dec_slot6_eval b n ctx) (lusO_atom b)) ?_
  show haxO (atom 6) (atom (1 + b)) (decLoopCore b n ctx) = some (decLoopCore (b + 1) n ctx)
  simp [decLoopCore, haxO_six, Nat.add_comm]

private theorem tisN_eq_true (b : Nat) : tisN (atom (b + 1)) (atom (1 + b)) = atom 0 := by
  simp [tisN, Nat.add_comm]

private theorem tisN_eq_false (b n : Nat) (h : b + 1 < n) :
    tisN (atom n) (atom (1 + b)) = atom 1 := by
  refine tisN_neq _ _ ?_
  intro hc; simp at hc; omega

/-- **Dec loop invariant.** Running the loop battery against the loop core
    `[loopBat [b [decBat [n ctx]]]]` where `b < n` produces `atom (n - 1)`.

    Proved by induction on `n - b - 1` (remaining iterations). -/
theorem dec_loop_inv (b n : Nat) (ctx : Noun) (hb : b < n) :
    NockEval (decLoopCore b n ctx) decLoopBat (.val (atom (n - 1))) := by
  obtain ⟨d, hd⟩ : ∃ d, n = b + 1 + d := ⟨n - b - 1, by omega⟩
  subst hd
  induction d generalizing b with
  | zero =>
    -- Base: n = b + 1, condition =(n, +(b)) is true, return b
    simp only [Nat.add_zero, show b + 1 - 1 = b from by omega]
    change NockEval (decLoopCore b (b + 1) ctx)
      (cell (atom 6) (cell _ (cell _ _))) (.val (atom b))
    refine NockEval.op6_then ?_ (dec_slot6_eval b (b + 1) ctx)
    have h := dec_cond_eval b (b + 1) ctx
    rwa [tisN_eq_true] at h
  | succ d ih =>
    -- Step: n = b + 2 + d, condition false, recurse with b+1
    simp only [show b + 1 + (d + 1) - 1 = b + 1 + d from by omega]
    change NockEval (decLoopCore b (b + 1 + (d + 1)) ctx)
      (cell (atom 6) (cell _ (cell _ _))) (.val (atom (b + 1 + d)))
    refine NockEval.op6_else ?_ ?_
    · have h := dec_cond_eval b (b + 1 + (d + 1)) ctx
      rwa [tisN_eq_false b (b + 1 + (d + 1)) (by omega)] at h
    · -- Else: [9 2 [10 [6 [4 [0 6]]] [0 1]]] — edit b → b+1, fire
      refine NockEval.op9 (dec_edit_core b (b + 1 + (d + 1)) ctx) (fasO_head _ _) ?_
      have h1 : b + 1 + (d + 1) = (b + 1) + 1 + d := by omega
      rw [h1]
      have := ih (b + 1) (by omega)
      rwa [show (b + 1) + 1 + d - 1 = b + 1 + d from by omega] at this

/-- **Dec correctness.** Running the `++dec` battery against a gate core
    `[decBat [n+1 ctx]]` produces `atom n` via a valid `NockEval` derivation.

    Combined with `callGate_gate_eval`, this proves that calling `++dec`
    on any positive atom computes the correct decrement. -/
theorem dec_correct (n : Nat) (ctx : Noun) :
    NockEval (cell decBat (cell (atom (n + 1)) ctx)) decBat (.val (atom n)) := by
  -- Decompose formula via definitional equality (subject stays abstract)
  show NockEval (cell decBat (cell (atom (n + 1)) ctx))
    (cell (atom 11) (cell (cell (atom 1851876717) decBat_hintF) decBat_guardBody))
    (.val (atom n))
  -- Step 1: op11_dynamic — the hint computes, then its value is discarded
  obtain ⟨_, hhint⟩ := dec_hint_eval (cell decBat (cell (atom (n + 1)) ctx))
  refine NockEval.op11_dynamic hhint ?_
  -- Step 2: op6_else — underflow guard, n+1 ≠ 0 so take the else branch
  rw [guardBody_parts]
  refine NockEval.op6_else ?_ ?_
  · have h0 : NockEval (cell decBat (cell (atom (n + 1)) ctx))
                (cell (atom 1) (atom 0)) (.val (atom 0)) := NockEval.op1
    have h6 : NockEval (cell decBat (cell (atom (n + 1)) ctx))
                (cell (atom 0) (atom 6)) (.val (atom (n + 1))) :=
      NockEval.op0 (by simp [fasO])
    have eq := NockEval.op5 h0 h6
    rwa [show tisN (atom 0) (atom (n + 1)) = atom 1 from
      tisN_neq _ _ (by intro hc; injection hc with hc; omega)] at eq
  · -- Steps 3-5: push b=0, push loopBat, fire loop
    rw [pushLoop_parts]
    refine NockEval.op8 NockEval.op1 ?_   -- push b=0
    refine NockEval.op8 NockEval.op1 ?_   -- push loopBat (quoted by [1 loopBat])
    -- Subject is now decLoopCore 0 (n + 1) ctx (definitionally)
    show NockEval (decLoopCore 0 (n + 1) ctx)
      (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) (.val (atom n))
    refine NockEval.op9 (core := decLoopCore 0 (n + 1) ctx) (arm := decLoopBat)
      (NockEval.op0 (fasO_one _)) (fasO_head _ _) ?_
    have h := dec_loop_inv 0 (n + 1) ctx (by omega)
    simpa using h

/-- **Dec underflow crashes.**  This is the theorem the old semantics got
    *wrong*: because `fas`'s axis-0 arm was `panic!`, the guard's crash branch
    `[0 0]` "evaluated" to `atom 0`, and the kernel would certify `dec 0 = 0`.
    With `Outcome`, the only derivable outcome is `.exit`.

    The guard `?<  =(0 a)` tests `=(0, sample)`; with sample `0` the test is
    true, so op6 takes the *then* branch, which is the formula `[0 0]` —
    axis 0, an unconditional crash.  The `.exit` propagates outward through
    the tail-position outcome parameters of `op6_then` and `op11_dynamic`
    with no extra constructors. -/
theorem dec_underflow (ctx : Noun) :
    NockEval (cell decBat (cell (atom 0) ctx)) decBat .exit := by
  show NockEval (cell decBat (cell (atom 0) ctx))
    (cell (atom 11) (cell (cell (atom 1851876717) decBat_hintF) decBat_guardBody)) .exit
  obtain ⟨_, hhint⟩ := dec_hint_eval (cell decBat (cell (atom 0) ctx))
  refine NockEval.op11_dynamic hhint ?_
  rw [guardBody_parts]
  refine NockEval.op6_then ?_ ?_
  · -- guard test: =(0 sample) with sample = 0, so tisN (atom 0) (atom 0) = atom 0
    have h0 : NockEval (cell decBat (cell (atom 0) ctx))
                (cell (atom 1) (atom 0)) (.val (atom 0)) := NockEval.op1
    have h6 : NockEval (cell decBat (cell (atom 0) ctx))
                (cell (atom 0) (atom 6)) (.val (atom 0)) :=
      NockEval.op0 (by simp [fasO])
    have eq := NockEval.op5 h0 h6
    rwa [tisN_refl] at eq
  · -- then-branch is [0 0]: axis 0 crashes
    exact NockEval.op0_crash (fasO_zero _)

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
    NockEval (addLoopCore a b ctx) addDecCallF (.val (atom (a - 1)))

/-- **Add loop invariant.** Running the add battery against the loop core
    `[addBat [[a b] ctx]]` produces `atom (a + b)`.

    Proved by induction on `a` (which decreases each iteration).
    The dec-calling mechanism is abstracted via `AddCtx`. -/
theorem add_loop_inv (a b : Nat) (ctx : Noun) (hctx : AddCtx ctx) :
    NockEval (addLoopCore a b ctx) addBat (.val (atom (a + b))) := by
  -- Lift b into the IH by proving ∀ b first
  suffices h : ∀ b, NockEval (addLoopCore a b ctx) addBat (.val (atom (a + b))) from h b
  induction a with
  | zero =>
    -- a = 0: condition =(0, 0) true, return b
    intro b; simp
    change NockEval (addLoopCore 0 b ctx) (cell (atom 6) (cell _ (cell _ _))) (.val (atom b))
    refine NockEval.op6_then ?_ ?_
    · have h : NockEval (addLoopCore 0 b ctx)
          (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 12))))
          (.val (tisN (atom 0) (atom 0))) :=
        NockEval.op5 NockEval.op1 (NockEval.op0 (by simp [addLoopCore, fasO]))
      rwa [tisN_refl] at h
    · exact NockEval.op0 (by simp [addLoopCore, fasO])
  | succ a ih =>
    -- a = k+1: condition false, recurse with [k, b+1]
    intro b
    change NockEval (addLoopCore (a + 1) b ctx)
      (cell (atom 6) (cell _ (cell _ _))) (.val (atom (a + 1 + b)))
    refine NockEval.op6_else ?_ ?_
    · have h : NockEval (addLoopCore (a + 1) b ctx)
          (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 12))))
          (.val (tisN (atom 0) (atom (a + 1)))) :=
        NockEval.op5 NockEval.op1 (NockEval.op0 (by simp [addLoopCore, fasO]))
      rwa [show tisN (atom 0) (atom (a + 1)) = atom 1 from
        tisN_neq _ _ (by intro hc; injection hc with hc; omega)] at h
    · -- Edit sample to [dec(a+1), +(b)] = [a, b+1], fire battery
      refine NockEval.op9 (core := addLoopCore a (1 + b) ctx) (arm := addBat)
        ?_ (fasO_head _ _) ?_
      · -- op10: build the new sample via autocons [dec_call, op4]
        have slot13 : NockEval (addLoopCore (a + 1) b ctx)
            (cell (atom 0) (atom 13)) (.val (atom b)) :=
          NockEval.op0 (by simp [addLoopCore, fasO])
        have dec_a : NockEval (addLoopCore (a + 1) b ctx) addDecCallF (.val (atom a)) := by
          have h := hctx.dec_call (a + 1) b (by omega); simpa using h
        refine NockEval.op10
          (NockEval.op0 (fasO_one _))
          (NockEval.autocons dec_a (NockEval.op4 slot13 (lusO_atom b))) ?_
        show haxO (atom 6) (cell (atom a) (atom (1 + b))) (addLoopCore (a + 1) b ctx)
          = some (addLoopCore a (1 + b) ctx)
        simp [addLoopCore, haxO_six]
      · -- Fire: fasO 2 core = addBat, apply IH
        have := ih (1 + b)
        rwa [show a + (1 + b) = a + 1 + b from by omega] at this

/-- **Add correctness.** Running the `++add` battery against a gate core
    `[addBat [[m n] ctx]]` produces `atom (m + n)`, given a context where
    the dec-calling mechanism works (`AddCtx`).

    Combined with `callGate_gate_eval`, this proves that calling `++add`
    on any pair of atoms computes the correct sum. -/
theorem add_correct (m n : Nat) (ctx : Noun) (hctx : AddCtx ctx) :
    NockEval (cell addBat (cell (cell (atom m) (atom n)) ctx)) addBat (.val (atom (m + n))) :=
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

When `b > a` the gate crashes (it attempts `dec 0`).  The theorem below is
restricted to `b ≤ a`.  Unlike the old development — where the crash case was
merely *absent* from the relation — the crash is now expressible as an
`.exit` outcome; deriving it needs a `SubCtx` that also says what the dec call
does at zero, which is left for future work.
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
    NockEval (subLoopCore a b ctx) subDecCallA (.val (atom (a - 1)))
  dec_call_b : ∀ (a b : Nat), b > 0 →
    NockEval (subLoopCore a b ctx) subDecCallB (.val (atom (b - 1)))

/-- The `~_` hint clue for `++sub` is a static cons: it evaluates to a value
    whatever the subject. -/
private theorem sub_hint_eval (s : Noun) : ∃ r, NockEval s subHintClueF (.val r) :=
  ⟨_, NockEval.autocons NockEval.op1 (NockEval.op0 (fasO_one s))⟩

/-- **Sub loop invariant / correctness.** Running the `++sub` battery against
    `[subBat [[a b] ctx]]` where `b ≤ a` produces `atom (a - b)`.

    The loop decrements both `a` and `b` until `b` reaches 0, then returns `a`.
    A `~_` hint fires every iteration (stripped by op11_dynamic).

    Proved by induction on `b`.  The dec-calling mechanism is abstracted
    via `SubCtx`. -/
theorem sub_loop_inv (a b : Nat) (ctx : Noun) (hctx : SubCtx ctx) (hab : b ≤ a) :
    NockEval (subLoopCore a b ctx) subBat (.val (atom (a - b))) := by
  revert a
  induction b with
  | zero =>
    intro a _; simp only [Nat.sub_zero]
    -- subBat = [11 [tag hintClue] subInnerBat] — strip hint via op11_dynamic
    obtain ⟨_, hhint⟩ := sub_hint_eval (subLoopCore a 0 ctx)
    refine NockEval.op11_dynamic hhint ?_
    -- subInnerBat = [6 cond then else]; b=0 so the condition is true
    change NockEval (subLoopCore a 0 ctx) (cell (atom 6) (cell _ (cell _ _))) (.val (atom a))
    refine NockEval.op6_then ?_ ?_
    · have h : NockEval (subLoopCore a 0 ctx)
          (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 13))))
          (.val (tisN (atom 0) (atom 0))) :=
        NockEval.op5 NockEval.op1 (NockEval.op0 (by simp [subLoopCore, fasO]))
      rwa [tisN_refl] at h
    · exact NockEval.op0 (by simp [subLoopCore, fasO])
  | succ b ih =>
    intro a hab
    -- Strip hint
    obtain ⟨_, hhint⟩ := sub_hint_eval (subLoopCore a (b + 1) ctx)
    refine NockEval.op11_dynamic hhint ?_
    -- b+1 ≠ 0: condition false
    change NockEval (subLoopCore a (b + 1) ctx)
      (cell (atom 6) (cell _ (cell _ _))) (.val (atom (a - (b + 1))))
    refine NockEval.op6_else ?_ ?_
    · have h : NockEval (subLoopCore a (b + 1) ctx)
          (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 13))))
          (.val (tisN (atom 0) (atom (b + 1)))) :=
        NockEval.op5 NockEval.op1 (NockEval.op0 (by simp [subLoopCore, fasO]))
      rwa [show tisN (atom 0) (atom (b + 1)) = atom 1 from
        tisN_neq _ _ (by intro hc; injection hc with hc; omega)] at h
    · -- Recurse: [9 2 [10 [6 [DEC_A DEC_B]] [0 1]]]
      refine NockEval.op9 (core := subLoopCore (a - 1) b ctx) (arm := subBat)
        ?_ (fasO_head _ _) ?_
      · -- op10: edit sample [a, b+1] → [a-1, b]
        have dec_a := hctx.dec_call_a a (b + 1) (by omega)
        have dec_b := hctx.dec_call_b a (b + 1) (by omega)
        rw [show (b + 1) - 1 = b from by omega] at dec_b
        refine NockEval.op10
          (NockEval.op0 (fasO_one _)) (NockEval.autocons dec_a dec_b) ?_
        show haxO (atom 6) (cell (atom (a - 1)) (atom b)) (subLoopCore a (b + 1) ctx)
          = some (subLoopCore (a - 1) b ctx)
        simp [subLoopCore, haxO_six]
      · -- Fire: fasO 2 core = subBat, apply IH
        have := ih (a - 1) (by omega)
        rwa [show (a - 1) - b = a - (b + 1) from by omega] at this

/-- **Sub correctness.** Running `++sub` on `[a b]` with `b ≤ a` produces `a - b`.
    The dec-calling mechanism is abstracted via `SubCtx`. -/
theorem sub_correct (a b : Nat) (ctx : Noun) (hctx : SubCtx ctx) (hab : b ≤ a) :
    NockEval (cell subBat (cell (cell (atom a) (atom b)) ctx)) subBat (.val (atom (a - b))) :=
  sub_loop_inv a b ctx hctx hab

end Nock
