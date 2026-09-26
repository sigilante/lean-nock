# TABLE-REPORT: trial of the paper's Tables A, B, C, and the Class D schemas

**Tables A and B — DISCHARGED (kernel).** All ten formulas prove as stated.
No discrepancies.

**Table C, row `dec` — the printed listing was REFUTED**; it fails on its entire
valid domain under both possible readings, and one reading additionally breaks
crash-totality (§C). The correction of §C.4 is now **DISCHARGED (kernel)** by
`leaf_dec`.

**Class D schemas (`ifte`, `while`) — DISCHARGED (kernel).** First confirmed by
oracle (676 runs, five fuel schedules, zero mismatches — §D), then **proved**:
`composition_term` gives `NockEval S (NT t) o ↔ CEval t S o` over the full term
algebra, and `composition_diverges` extends the agreement to divergence.

**Table C, rows `add` and `sub` — DISCHARGED (kernel)** by `leaf_add` and
`leaf_sub`. The paper names these rows' Nock formulas only as "inc-loop" and
"dec-loop", so there was no printed listing to put on trial; the formulas are
the artifact's (`Nock/Comp.lean`). The ⊥-domain column is transcribed into `cw`
and discharged as stated, over all nouns.

## Claim gradient

The three words are not interchangeable and the paper must respect the
difference:

| status | meaning | who says so |
| --- | --- | --- |
| **discharged** | a Lean theorem, kernel-checked | Tables A, B; Table C's `dec`, `add`, `sub` rows; the Class D schemas; named definitions |
| **confirmed** | agreement of two executable models over a corpus | *(nothing outstanding)* |
| **prose** | argued, not executed | everything else |

An oracle can refute (it did, in §C) and it can fail to refute. It cannot
discharge. The Class D schemas passed through both stages in order: the oracle
trial de-risked the design before the simulation-pair investment, and the proof
then discharged them.

**Manuscript action:** the Class D sentence — *"mechanized proof is in
progress"* — is now false in the good direction, and is flagged for the humans
to upgrade. The schemas are proved; cite `composition_term` and
`composition_diverges`.

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

---

# Class D schemas — acquitted by oracle

The `ifte` and `while` compilation schemas of DEFENDANT-CLASSD §2 (manuscript
Equations classd-ifte and classd-while) were put on trial under the §5 protocol:
transcribed verbatim, never corrected, the schema is the defendant.

**Verdict: no conviction on any claim.** `L` is not refuted by this corpus.

## D.1 Method

The trial compares two independent executable models of the same program:

- **Nock side** — `nockF fuel S (N t)`, the fuel interpreter of `Nock/Fuel.lean`,
  applied to the compiled formula. Tied to the `NockEval` relation by
  `nockF_sound` / `nockF_complete`.
- **C side** — `CsemF fuel t S`, a fueled transcription of the manuscript's C
  listings (`Nock/Oracle.lean`). Quarantined by import direction; nothing in the
  proof chain imports it.

`none` means *fuel exhausted* on both sides, never a semantic verdict. A
**mismatch** is two differing verdicts; an **asymmetry** is one side reaching a
verdict while the other does not. Asymmetry is the conviction column: it is how
a divergence-vs-crash disagreement would surface.

## D.2 Corpus

**26 programs × 26 subjects = 676 runs** per fuel schedule.

Programs cover all seven required probe classes plus nesting: `while`-in-body,
`while`-in-branch, `ifte`-in-body, `ifte`-in-test, sequenced continuations after
each, and the Class C `dec` word inside both a loop body and a continuation.

Subjects: atoms (`0,1,2,9`); depth-1 stacks with loobean, non-loobean-atom, and
cell tops; left-spine nouns of depth 0–3; counter-carrying stacks `[a [c rest]]`;
a two-cell stack; a depth-3 flat stack.

## D.3 Fuel schedule and results

| `(nockF, CsemF)` | agree | both `none` | **mismatch** | **asymmetric** |
| --- | --- | --- | --- | --- |
| 500 / 200 | 632 | 44 | **0** | **0** |
| 2 000 / 800 | 632 | 44 | **0** | **0** |
| 4 000 / 1 500 | 632 | 44 | **0** | **0** |
| 20 000 / 5 000 | 632 | 44 | **0** | **0** |
| 60 000 / 20 000 | 632 | 44 | **0** | **0** |

Counts are identical at every schedule. The 44 two-sided `none` are confined to
exactly the two designed-divergent programs and persist to the top schedule, so
they are divergence rather than fuel exhaustion.

## D.4 Mismatch table

*(empty)*

## D.5 Probe results

| class | probe | both sides |
| --- | --- | --- |
| 1 value paths | `while([dup,celq],[head])`, spine depth 0–3 | `.val`; exit value tracks iteration count |
| 2 ifte branches | flag `0` / flag `1` | `.val`, correct branch |
| 2 non-loobean | flag `atom 2`, `atom 9`, cell | `.exit` |
| 3 flag-pop on atom | `ifte` on atom subject; `while` test → atom | `.exit` |
| 4 crash in body | `while([dup,eq],[head])`, depths 1–3 | `.exit` |
| 4′ iteration-exact | counter `c`, spine depth 3, body `[head,swap,dec,swap]` | `c<3` → `.exit`; `c≥3` → `.val`, counter `c−3` |
| 5 divergence | two-sided `none`, fuels 10…5 000 | `none` |
| 6 nesting | while-in-body, while-in-branch, ifte-in-body, ifte-in-test | `.val` |
| 6 exit-stack convention | `while([dup,inc,eq],[])` + `[celq]` continuation | `.val` |
| 7 crash hides continuation | crash in loop, continuation `[inc]` | `.exit`; and `.val` when no crash |

Probe 4′ is the sharp one. It is fuel-independent and iteration-exact: an
off-by-one on either side flips a crash into a value, or shifts the returned
counter. It does neither. This is what licenses the word *iteration-exactly* in
the manuscript sentence.

Claims W1–W6 and I1 of DEFENDANT-CLASSD §3 are each exercised and none convicts.

## D.6 Errata in the suggested generators (not defects in the schemas)

Two of §5's suggested probe generators do not do what they were expected to.
Both are facts about the generators; neither bears on `L`.

**1. `while([dup,eq],[])` does not diverge.** Both sides return `.exit`, and
agree. The datum:

```
CsemF 50 [dup,eq] [A1, 0]  =  .val (cell (atom 0) (atom 0))
```

`[dup,eq]` is **net-0** arity — `dup` pushes, `eq` pops two and pushes one — so
the test *consumes* the stack top rather than preserving it. Its output stack is
`atom 0`, and the next iteration's `dup` crashes on that atom. The divergence
class was therefore exercised by `while([dup,dup,eq],[])`, which is net-+1,
preserves the stack, and has flag `0` always; and by the same test with a
non-empty body. Both give two-sided `none` at every fuel tried.

**2. `while([dup,celq],[head])` with continuation `[celq]` is not
discriminating.** `wut` is idempotent on the exit value, so a wrong `S′`
convention would yield the same noun. Replaced with a continuation of `[inc]`,
and with a test (`[dup,inc,eq]`) that is deliberately *not* stack-preserving, so
that a wrong exit-stack convention changes the value. Both agree.

## D.7 Status, precisely — now DISCHARGED

At the time of the trial the schemas were **confirmed (oracle)**, and the
manuscript sentence was:

> the compilation schemas of Equations (classd-ifte) and (classd-while) have
> been empirically confirmed against a fueled model of the C semantics over 676
> runs spanning value, crash, divergence, and nesting behavior,
> iteration-exactly; mechanized proof is in progress.

**That sentence is now understated.** Phase 4b closed the simulation pair:

```lean
theorem composition_term (t : Term) (S : Noun) (o : Outcome) :
    NockEval S (NT t) o ↔ CEval t S o

theorem composition_diverges (t : Term) (S : Noun) :
    Diverges S (NT t) ↔ CDiverges t S
```

Agreement on values, on crashes, **and on divergence** — the last as a
biconditional between two absence-of-derivation statements. That is the paper's
"equal least fixed points" made literal.

The oracle's role is unchanged and remains valuable: it refuted Table C's `dec`
row before any proof effort was spent, and it acquitted the Class D schemas
before the simulation-pair investment was made. Empirical confirmation is what
made the proof worth attempting; it is not what discharges it.

The regression is pinned: `Nock/Oracle.lean` re-runs `sweep 4000 1500` at build
time and prints `(632, 44, 0, 0)`.
