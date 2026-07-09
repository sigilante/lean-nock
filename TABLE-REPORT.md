# TABLE-REPORT: trial of the paper's Tables A, B, and C

**Tables A and B — verdict: all ten formulas prove as stated. No discrepancies.**

**Table C, row `dec` — verdict: the printed listing is REFUTED. It fails on its
entire valid domain under both possible readings, and one reading additionally
breaks crash-totality. A correction is proposed in §C.4 and has passed the
oracle.**

Both sentences are intended for the paper.

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

---

# Table C, row `dec` — the listing is refuted

Unlike Tables A and B, this row's formula does **not** survive contact with the
kernel's evaluator. The trial was run under the §5 protocol: `phi` transcribed
verbatim, never edited; the table is the defendant.

## C.1 The defendant, verbatim

Guarded-dec, as printed:

```
[6 [3 0 2] [0 0] [6 [5 [1 0] 0 2] [0 0] <count-up>]]
```

Lift footnote:

```
φ_dec = [[7 [0 2] <guarded-dec>] 0 3]
```

Canonical `<count-up>`:

```
[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] [9 2 [0 2] [4 0 6] 0 7]] 9 2 0 1]
```

The listing admits two readings, because the guards' axis `2` is consistent
with either. **Both fail.**

## C.2 Reading A — guarded-dec runs on the bare atom, per the lift footnote

The lift's `[7 [0 2] …]` extracts the stack top and runs guarded-dec against
it. So guarded-dec's subject is a bare atom, and its guard `[3 0 2]` takes
axis 2 *of an atom*.

```
fasO (atom 2) (atom 5)  =  none
```

`op0_crash` → `op3_crash` → `op6_crash`. **Every valid input crashes.**

| subject | Table C says | `nockF 3000` gives | |
| --- | --- | --- | --- |
| `[1 77]` | `.val [0 77]` | `.exit` | ❌ |
| `[2 77]` | `.val [1 77]` | `.exit` | ❌ |
| `[5 77]` | `.val [4 77]` | `.exit` | ❌ |
| `[[1 2] 77]` | `.exit` | **`none` — diverges** | ❌ |
| `[0 77]` | `.exit` | `.exit` | ✅ (by accident) |
| `9` | `.exit` | `.exit` | ✅ (by accident) |

**The cell-argument row is the finding neither hand-check caught.** With a cell
top, `fasO (atom 2)` *succeeds* (it takes the cell's head), so the cellness
guard reads the wrong noun, returns `atom 1`, and passes. The zero guard then
also passes, and `<count-up>` runs against a cell — comparing a cell to an atom
forever. Confirmed `none` at fuel 50, 500, 5000.

So under Reading A the printed `φ_dec` is **not crash-total**, and therefore
not denotable as a `Word` at all: `not_denotable_of_diverges` excludes it, by
exactly the theorem the guard-emission rule is supposed to be enforcing. The
guard meant to reject cells is the reason the cell is accepted.

## C.3 Reading B — guarded-dec runs on the stack directly

Ignore the lift; let the guards see the stack, where axis 2 *is* the top. The
guards are then correct — and `<count-up>` inherits the stack as its subject.
Its loop test is `[5 [0 7] 4 0 6]`, and after the two `op8` pushes axis 7 holds
the **whole stack** `[a r]`, a cell, which the atom counter never equals.

| subject | Table C says | `nockF 3000` gives | |
| --- | --- | --- | --- |
| `[1 77]` | `.val [0 77]` | **`none` — diverges** | ❌ |
| `[2 77]` | `.val [1 77]` | **`none` — diverges** | ❌ |
| `[5 77]` | `.val [4 77]` | **`none` — diverges** | ❌ |
| `[[1 2] 77]` | `.exit` | `.exit` | ✅ |
| `[0 77]` | `.exit` | `.exit` | ✅ |
| `9` | `.exit` | `.exit` | ✅ |

Diverges at fuel 50, 500, 5000. **Every valid input diverges.**

The root cause, isolated:

```
nockF 3000 (cell (atom 5) (atom 77)) <count-up>  =  none        -- stack subject
nockF 3000 (atom 5)                  <count-up>  =  .val 4      -- bare atom subject
```

`<count-up>` is correct, and is built for a bare atom. The guards are correct
for a stack. They cannot both be right about the same subject: **guards wrong
or loop wrong, and the composite fails on the entire valid domain either way.**

## C.4 Proposed correction — for the humans to ratify

Keep the lift as printed; move the guards to axis 1, so they read the subject
guarded-dec actually receives (the bare atom):

```
[6 [3 0 1] [0 0] [6 [5 [1 0] 0 1] [0 0] <count-up>]]
```

- `[3 0 1]` is `?subject`: a cell top → `0` → crash branch; an atom → `1` → inner guard.
- `[5 [1 0] 0 1]` is `=(0 subject)`: zero → crash branch; else `<count-up>` on a
  genuine bare atom, the domain it was built for.
- Depth `< 1` still falls out of the lift's `[0 2]` for free: on a bare-atom
  stack, `fasO (atom 2) (atom _) = none`, so `op7`'s left operand crashes.

**Oracle result: 0 mismatches against Table C across a 48-subject corpus**
(every ⊥ arm, plus a spread of valid inputs). The corrected `φ_dec` is
crash-total, hence denotable as a `Word`.

## C.5 Independent convergence

Before the manuscript listing was available, this artifact derived a guarded
`dec` from the ⊥ domain alone: stack-native, guards at axis 2, with a
purpose-built loop core `[loopBat [b [a r]]]` (axes 14/15) rather than the
canonical `<count-up>`. It also passes at 0 mismatches, and the two formulas
**agree pointwise on all 48 subjects**.

They converged on the *denotation*, not on the *shape* — which is the useful
kind of convergence: two independent routes to the same ⊥ domain, one of which
keeps the manuscript's canonical `<count-up>` and lift intact. The correction
in §C.4 is preferred for the paper precisely because it changes two axes and
nothing else. The artifact will carry §C.4's formula, not its own.

## C.6 Note on provenance

The axes in the printed listing were hand-computed and survived seven editorial
passes. That is not a failure of care; it is a demonstration of what prose
review can and cannot check. Reviewing an axis for plausibility is not the same
as evaluating it against the lift printed two lines away, and `[3 0 2]` looks
entirely plausible next to a stack convention where axis 2 is the top.

This is the `hax_sixty` failure mode — a hand-computed axis under a subject
whose shape shifts — arriving in `dec` rather than in `while`, where it was
expected. It sharply raises the prior that the `while` schema's `L`, computed
the same way under a subject that *grows* under `op8`, is also wrong. `while`
gets the oracle before it gets a proof.
