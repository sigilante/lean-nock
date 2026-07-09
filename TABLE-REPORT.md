# TABLE-REPORT: trial of the paper's Tables A and B

**Verdict: all ten formulas prove as stated. No discrepancies. No corrections proposed.**

That sentence is the one intended for the paper.

---

## What was tried

Per SPEC-PHASE4 §0, the `phi` formulas in `Nock/Comp.lean` were transcribed
verbatim from the manuscript's Tables A and B and were **not** edited at any
point. The `cw` model was likewise implemented exactly as §2.3 specifies.

Each word carries a single leaf theorem covering both the value and the crash
clause at once, since `cw w S` is by definition whichever of the two applies:

```lean
theorem leaf_correct (w : Word) (S : Noun) : NockEval S (phi w) (cw w S)
```

All ten `private` leaf lemmas (`leaf_dup` … `leaf_celq`) close, so
`leaf_correct` holds for every word and **every** subject noun — not merely
those satisfying a stack-depth invariant.

`#print axioms leaf_correct` → `[propext, Quot.sound]`.

## Independent corroboration

Before any proof was attempted, `phi` and `cw` were compared by computation:
`nockF 200 S (phi w)` against `some (cw w S)`, for all 10 words across a
280-noun subject corpus (atoms; all cells of depth ≤ 3 over the leaf set
`{0, 1, 7, [0 1], [1 1]}`, in both head-heavy and tail-heavy shapes). This
covers every arm of `cw`'s match tree, including all fifteen `.exit` arms.

**Mismatches: 0.** No subject produced `none` either, so no `phi w` diverges
on any tested subject — consistent with all ten being crash-total.

This was a deliberate check *against* the proofs rather than a substitute for
them: the computation exercises `nockF`, the proofs exercise `NockEval`, and
the two are tied together by `nockF_sound`/`nockF_complete`.

## Table A (stack shuffling)

| word | paper formula | effect | result |
| --- | --- | --- | --- |
| `dup`  | `[[0 2] 0 1]`         | `( a — a a )`     | ✅ proved |
| `drop` | `[0 3]`               | `( a — )`         | ✅ proved |
| `swap` | `[[0 6] [0 2] 0 7]`   | `( a b — b a )`   | ✅ proved |
| `over` | `[[0 6] 0 1]`         | `( a b — a b a )` | ✅ proved |
| `cons` | `[[[0 6] 0 2] 0 7]`   | `( h t — [h t] )` | ✅ proved |
| `head` | `[[0 4] 0 3]`         | `( c — h )`       | ✅ proved |
| `tail` | `[[0 5] 0 3]`         | `( c — t )`       | ✅ proved |

## Table B (arithmetic and predicates)

| word | paper formula | effect | result |
| --- | --- | --- | --- |
| `inc`  | `[[4 0 2] 0 3]`       | `( a — a+1 )` | ✅ proved |
| `eq`   | `[[5 [0 6] 0 2] 0 7]` | `( a b — ? )` | ✅ proved |
| `celq` | `[[3 0 2] 0 3]`       | `( a — ? )`   | ✅ proved |

## Notes for the authors

These are observations about the tables, not defects. Nothing here requires a
change to the manuscript's formulas.

**1. The `eq` argument order is real, and SPEC-PHASE4 §2.3 called it
correctly.** `phi .eq` evaluates `[0 6]` (the deeper element `a`) before
`[0 2]` (the top `b`), so the model must be `tisN a b`. Because `tisN` is
symmetric in *value*, `tisN b a` would still be extensionally correct, and a
value-level test would never catch the difference. It matters only because the
leaf proof closes definitionally in one order and not the other. If the paper
states the C routine as comparing top-then-deeper, that is a presentational
mismatch with the Nock formula's evaluation order, worth a footnote.

**2. Every Class A/B word is crash-total: none diverges.** Each `phi w` is a
finite composition of `op0`/`op3`/`op4`/`op5` and autocons, with no `op2`,
`op7`, `op8`, or `op9`, hence no recursion. So the three-valued outcome
collapses to two on these words, and `cw`'s `Outcome` codomain never needs the
divergence case. This is what makes the composition theorem's `Csem` total.
It stops being true the moment Class C admits a `dec`-like word — see below.

**3. The crash domains are strictly larger than "wrong stack depth."**
`head` and `tail` crash on a depth-1 stack, but also on `[[atom] r]` where the
depth is fine and the *head is an atom*. `inc` likewise crashes on `[[u v] r]`.
The tables express these as ⊥-domain columns relative to a stack invariant;
`cw` states them over arbitrary nouns, and the leaf theorems are correspondingly
stronger. No formula needed changing to make that work.

**4. Four words share one crash domain.** `swap`, `over`, `cons`, and `eq` all
crash exactly when `fasO (atom 6) S = none`, i.e. when the tail of the subject
is an atom — they are precisely the two-argument words, and each reaches for
the second element first. Checked by computation over the corpus: their crash
sets coincide with `{S | fasO (atom 6) S = none}` exactly, and the other six
words' do not. That four distinct formulas induce one common ⊥-domain seems
worth stating once in the paper rather than four times.

## Related: the `dec` ⊥-profile (Phase 3.5)

Not part of Tables A/B, but decided in the same pass, and directly relevant to
Class C. Hoon's compiled `++dec` (`decBat`) is **not** crash-total:

| input | outcome | theorem |
| --- | --- | --- |
| `atom (n+1)` | `.val (atom n)` | `dec_correct` |
| `atom 0` | `.exit` | `dec_underflow` |
| `cell _ _` | **divergence** | `dec_cell_diverges` |

On a cell the zero-guard passes (a cell is not `atom 0`), so the count-up loop
is entered, and its test `=(a +(b))` compares a cell against an atom — `atom 1`
at every iteration, forever.

As SPEC-PHASE4 §3 anticipates, this is a different formula from the Λ-emitted
guarded `dec` leaf, whose cell case is specified to `.exit`. They have
different ⊥ profiles and must remain distinct definitions. Concretely: a Class
C `dec` word modeled by `cw` (codomain `Outcome`, hence crash-total) **cannot**
be Hoon's `decBat`, because no `Outcome` denotes divergence. Whatever `Csem`
becomes in Phase 4b will need to accommodate that, or the guarded formula must
be the only `dec` a word may denote.
