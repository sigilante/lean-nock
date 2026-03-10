import Nock.Basic
import Nock.Proofs
open Noun

/-!
# NockEval: Inductive Relational Semantics for Nock 4K

`NockEval subject formula result` holds iff running `formula` against
`subject` produces `result` according to the Nock 4K specification.

Each constructor corresponds to exactly one rule.  This is the foundation
for the zkVM proof: a ZK circuit encoding of Nock is a proof that a valid
`NockEval` derivation exists.

For opcode 6 (if-then-else) we give the high-level semantic reading
(test evaluates to loobean 0 → take branch c; to 1 → take branch d)
rather than the macro expansion in the spec.  They are equivalent and
the semantic form is far easier to reason about.

For opcode 9 (gate call) we unfold one step of the spec:
  *[a 9 b c] = *[*[a c] 2 [0 1] 0 b]
             = *[core fas(b core)]     where core = *[a c]
which is the form all gate-call proofs actually use.

For opcode 11 (hint) both cases discard the hint:
  static  (*[a 11 t   c]  = *[a c])
  dynamic (*[a 11 [t c] d] = *[[*[a c] *[a d]] 0 3] = *[a d])
-/

inductive NockEval : Noun → Noun → Noun → Prop where

  -- *[a [b c] d] = [*[a b c] *[a d]]   (auto-cons)
  | autocons {a b c fol r1 r2} :
      NockEval a (cell b c) r1 →
      NockEval a fol r2 →
      NockEval a (cell (cell b c) fol) (cell r1 r2)

  -- *[a 0 b] = /[b a]                   (slot)
  | op0 {a fol} :
      NockEval a (cell (atom 0) fol) (fas fol a)

  -- *[a 1 b] = b                         (constant)
  | op1 {a fol} :
      NockEval a (cell (atom 1) fol) fol

  -- *[a 2 b c] = *[*[a b] *[a c]]       (eval)
  | op2 {a b c r1 r2 r} :
      NockEval a b r1 →
      NockEval a c r2 →
      NockEval r1 r2 r →
      NockEval a (cell (atom 2) (cell b c)) r

  -- *[a 3 b] = ?*[a b]                  (cell test)
  | op3 {a fol r} :
      NockEval a fol r →
      NockEval a (cell (atom 3) fol) (wut r)

  -- *[a 4 b] = +*[a b]                  (increment)
  | op4 {a fol r} :
      NockEval a fol r →
      NockEval a (cell (atom 4) fol) (lus r)

  -- *[a 5 b c] = =[*[a b] *[a c]]       (equality test)
  | op5 {a b c r1 r2} :
      NockEval a b r1 →
      NockEval a c r2 →
      NockEval a (cell (atom 5) (cell b c)) (tis (cell r1 r2))

  -- *[a 6 b c d] = *[a c]  when *[a b] = 0  (if-then: loobean true)
  | op6_then {a b c d r} :
      NockEval a b (atom 0) →
      NockEval a c r →
      NockEval a (cell (atom 6) (cell b (cell c d))) r

  -- *[a 6 b c d] = *[a d]  when *[a b] = 1  (if-else: loobean false)
  | op6_else {a b c d r} :
      NockEval a b (atom 1) →
      NockEval a d r →
      NockEval a (cell (atom 6) (cell b (cell c d))) r

  -- *[a 7 b c] = *[*[a b] c]            (compose)
  | op7 {a b c r1 r} :
      NockEval a b r1 →
      NockEval r1 c r →
      NockEval a (cell (atom 7) (cell b c)) r

  -- *[a 8 b c] = *[[*[a b] a] c]        (push)
  | op8 {a b c r1 r} :
      NockEval a b r1 →
      NockEval (cell r1 a) c r →
      NockEval a (cell (atom 8) (cell b c)) r

  -- *[a 9 b c] = *[core /[b core]]      (gate call, core = *[a c])
  -- Derived from spec: *[*[a c] 2 [0 1] 0 b] = *[core fas(b, core)]
  | op9 {a b c core r} :
      NockEval a c core →
      NockEval core (fas b core) r →
      NockEval a (cell (atom 9) (cell b c)) r

  -- *[a 10 [b c] d] = #[b *[a c] *[a d]]  (edit-at-axis)
  | op10 {a b c d r1 r2} :
      NockEval a c r1 →
      NockEval a d r2 →
      NockEval a (cell (atom 10) (cell (cell b c) d)) (hax b r1 r2)

  -- *[a 11 t c] = *[a c]                (static hint: atom tag, no-op)
  | op11_static {a t c r} :
      NockEval a c r →
      NockEval a (cell (atom 11) (cell (atom t) c)) r

  -- *[a 11 [t c] d] = *[a d]            (dynamic hint: discard hint, return d)
  -- spec says *[[*[a c] *[a d]] 0 3] = fas(3, [r1 r2]) = r2 = *[a d]
  | op11_dynamic {a t c d r1 r2} :
      NockEval a c r1 →
      NockEval a d r2 →
      NockEval a (cell (atom 11) (cell (cell t c) d)) r2

-- ---------------------------------------------------------------------------
-- Basic sanity examples
-- ---------------------------------------------------------------------------

-- *[42 1 99] = 99
example : NockEval (atom 42) (cell (atom 1) (atom 99)) (atom 99) :=
  NockEval.op1

-- *[a 0 1] = a   (slot 1 = identity)
-- op0 gives result (fas (atom 1) a); rewrite with fas_one to get a
example (a : Noun) : NockEval a (cell (atom 0) (atom 1)) a := by
  have h := @NockEval.op0 a (atom 1)
  rw [fas_one] at h; exact h

-- *[a 4 0 1] = lus(a)  (increment the subject)
example (a : Noun) : NockEval a (cell (atom 4) (cell (atom 0) (atom 1))) (lus a) := by
  have hslot := @NockEval.op0 a (atom 1)
  rw [fas_one] at hslot
  exact NockEval.op4 hslot

-- *[[bat [sam ctx]] 10 [6 [1 arg]] [0 1]] = [bat [arg ctx]]   (sample edit)
example (bat sam ctx arg : Noun) :
    NockEval (cell bat (cell sam ctx))
             (cell (atom 10) (cell (cell (atom 6) (cell (atom 1) arg)) (cell (atom 0) (atom 1))))
             (cell bat (cell arg ctx)) := by
  have e1 : NockEval (cell bat (cell sam ctx)) (cell (atom 1) arg) arg :=
    NockEval.op1
  have e2 : NockEval (cell bat (cell sam ctx)) (cell (atom 0) (atom 1)) (cell bat (cell sam ctx)) := by
    have h := @NockEval.op0 (cell bat (cell sam ctx)) (atom 1)
    rw [fas_one] at h; exact h
  have e10 : NockEval (cell bat (cell sam ctx))
                 (cell (atom 10) (cell (cell (atom 6) (cell (atom 1) arg)) (cell (atom 0) (atom 1))))
                 (hax (atom 6) arg (cell bat (cell sam ctx))) :=
    NockEval.op10 e1 e2
  rw [hax_six] at e10; exact e10
