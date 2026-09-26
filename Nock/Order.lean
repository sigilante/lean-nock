import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
open Noun

/-!
# Evaluation order, pinned

The Nock specification does not fix the order in which a rule's operands are
evaluated.  It matters exactly when one operand crashes and another diverges:
then the order decides which bottom the formula reaches, and so which clause of
the three-valued jet contract applies.

`NockEval` follows the production runtimes, Vere and NockVM, which agree:

| rule | evaluated first |
| --- | --- |
| autocons `[[b c] d]` | the head `[b c]` |
| opcode 2 `[2 b c]` | the subject formula `b` |
| opcode 5 `[5 b c]` | `b` |
| opcode 10 `[10 [x c] d]` | the tree `d`, then the patch `c` |
| opcode 11 `[11 [t c] d]` | the clue `c` |

Each theorem below says the first-evaluated operand wins, whatever the other
does: if it diverges the formula diverges, and if it crashes the formula
crashes.  Opcode 10 is the one rule evaluated right to left.
-/

theorem order_autocons_diverges {a b c d : Noun} (h : Diverges a (cell b c)) :
    Diverges a (cell (cell b c) d) := by
  intro o hn
  cases hn with
  | crash_malformed hm => simp [Malformed] at hm
  | autocons h1 _ => exact h _ h1
  | autocons_crashL h1 => exact h _ h1
  | autocons_crashR h1 _ => exact h _ h1

theorem order_autocons_crashes {a b c d : Noun} (h : NockEval a (cell b c) .exit) :
    NockEval a (cell (cell b c) d) .exit :=
  NockEval.autocons_crashL h

theorem order_op2_diverges {a b c : Noun} (h : Diverges a b) :
    Diverges a (cell (atom 2) (cell b c)) := by
  intro o hn
  cases hn with
  | crash_malformed hm => simp [Malformed] at hm
  | op2 h1 _ _ => exact h _ h1
  | op2_crashL h1 => exact h _ h1
  | op2_crashR h1 _ => exact h _ h1

theorem order_op2_crashes {a b c : Noun} (h : NockEval a b .exit) :
    NockEval a (cell (atom 2) (cell b c)) .exit :=
  NockEval.op2_crashL h

theorem order_op5_diverges {a b c : Noun} (h : Diverges a b) :
    Diverges a (cell (atom 5) (cell b c)) := by
  intro o hn
  cases hn with
  | crash_malformed hm => simp [Malformed] at hm
  | op5 h1 _ => exact h _ h1
  | op5_crashL h1 => exact h _ h1
  | op5_crashR h1 _ => exact h _ h1

theorem order_op5_crashes {a b c : Noun} (h : NockEval a b .exit) :
    NockEval a (cell (atom 5) (cell b c)) .exit :=
  NockEval.op5_crashL h

/-- Opcode 10 evaluates the tree `d` before the patch `c`. -/
theorem order_op10_diverges {a x c d : Noun} (h : Diverges a d) :
    Diverges a (cell (atom 10) (cell (cell x c) d)) := by
  intro o hn
  cases hn with
  | crash_malformed hm => simp [Malformed] at hm
  | op10 h1 _ _ => exact h _ h1
  | op10_badaxis h1 _ _ => exact h _ h1
  | op10_crashTree h1 => exact h _ h1
  | op10_crashPatch h1 _ => exact h _ h1

theorem order_op10_crashes {a x c d : Noun} (h : NockEval a d .exit) :
    NockEval a (cell (atom 10) (cell (cell x c) d)) .exit :=
  NockEval.op10_crashTree h

theorem order_op11_diverges {a t c d : Noun} (h : Diverges a c) :
    Diverges a (cell (atom 11) (cell (cell t c) d)) := by
  intro o hn
  cases hn with
  | crash_malformed hm => simp [Malformed] at hm
  | op11_dynamic h1 _ => exact h _ h1
  | op11_dyn_crash h1 => exact h _ h1

theorem order_op11_crashes {a t c d : Noun} (h : NockEval a c .exit) :
    NockEval a (cell (atom 11) (cell (cell t c) d)) .exit :=
  NockEval.op11_dyn_crash h
