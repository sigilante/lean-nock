# Roadmap: remaining work against the companion paper

Status at `v0.6`: every claim the paper makes about the artifact is discharged.
Three items remain. They strengthen the paper, but none is needed for a claim
it already makes. Items 8 and 9 are artifact work; item 10 is a paper edit that
depends on a fact we should re-verify first.

---

## 8. A `+mock` model: make "the two-valued contract is unsound" a theorem

**Why.** The abstract says "we show that the naïve two-valued contract is
unsound", but the argument (paper §1) is prose. The ingredients are already
proved: `countUp_correct` (the canonical `dec` returns `n` on `n+1`) and
`countUp_zero_diverges` (it diverges at `0`). A C `dec` that bails `%exit` at
`0` meets the two-valued contract and is observably wrong under `+mock`. That
is the Vere `dec` incident (PR #960) as a theorem.

**Design** — new module `Nock/Mock.lean`, in the proof chain:

- `JetOut := val Noun | exit | bail | punt` — a jet's result: a value, a
  deterministic bail (`%exit`), a nondeterministic bail (`%intr`, `%meme`, …),
  or a punt to the formula.
- `JetEval (j : Noun → JetOut) (S F : Noun) : Outcome → Prop` — the jetted
  call: `val`/`exit` from the jet directly; `punt` runs `NockEval S F`; `bail`
  has no in-Nock outcome (the event fails), modeled as absence of derivation.
- `MockEval (E : Noun → Outcome → Prop) : Noun → Prop` — virtualization over
  an evaluator: a value `v` observes as `[0 v]`, a deterministic crash as
  `[2 ~]` (a *value*), and no outcome as no observation.
- `TwoValued F j := ∀ S v, NockEval S F (.val v) ↔ j S = .val v`.
- `ThreeValued F j` — Equations (1a)–(1c): values agree; `exit` iff
  `.exit`; `Diverges S F → j S ∈ {bail, punt}`.

**Theorems.**

```lean
theorem two_valued_unsound :
    ∃ F j, TwoValued F j ∧ ∃ S o,
      MockEval (JetEval j S F) o ∧ ¬ MockEval (NockEval S F) o
-- witness: F = countUp, j = native dec with exit at 0 and on cells, S = atom 0

theorem three_valued_sound {F j} (h : ThreeValued F j) (S : Noun) (o : Noun) :
    MockEval (JetEval j S F) o ↔ MockEval (NockEval S F) o
```

**Acceptance.** Both theorems in the manifest at `{propext, Quot.sound}`. The
paper cites `two_valued_unsound` in the abstract's "we show" and in §1 after
the three-valued contract, and `three_valued_sound` where the contract is
stated.

**Scope note.** `+mock` also services scry (opcode 12); that is not modeled
and does not bear on the argument.

**Effort.** Small: about 150–250 lines, no new infrastructure.

---

## 9. Ground lean-nock's semantics in pure-nock-lean and nockvm

**Why.** A reviewer's first question is "is your `NockEval` the real Nock?"
`nockchain/pure-nock-lean` (public, Apache-2.0) is an independent, audited
formalization with a differential harness against Nockchain's production
`nockvm`. Agreement with it grounds lean-nock twice over.

**Constraint.** pure-nock-lean needs Lean 4.31 plus Mathlib, and its headline
theorems use `Classical.choice`. lean-nock is on 4.28, has no dependencies,
and cites `{propext, Quot.sound}`. The bridge must **never** enter the proof
chain, and lean-nock must not take a Mathlib dependency.

**9.0 Feasibility (do first).**
1. Build lean-nock under `leanprover/lean4:v4.31.0`. The bridge package will
   compile lean-nock with its own toolchain. Fix any breakage on a branch;
   bump lean-nock's pin only if the fixes are trivial.
2. **Evaluation-order probe.** pure-nock-lean's semantics is a small-step
   machine (`Nock.Verb.next`, with `getIndex = maxPendingIdx`). lean-nock is
   left-to-right strict, matching Vere and NockVM. If pure-nock-lean reduces
   the rightmost pending redex first, the two disagree on crash vs.
   divergence. Witness: subject `0`, the autocons formula `[L [0 0]]` with
   `L` a diverging loop (e.g. `countUp`). lean-nock diverges, because the
   left operand never finishes; a right-first machine crashes on `[0 0]`.
   Run `evalProgram n (atom 0) ⌜[L [0 0]]⌝` for growing `n`. If this is a
   disagreement it is a **finding**, and it decides the shape of 9.2's
   theorem: full agreement, or agreement off divergence.

**9.1 Differential testing (cheap, do before any proof).**
- Add a `lake exe export-corpus` target that writes lean-nock's compiled
  formulas as `[subject formula]` lines in pure-nock-lean's `.nock` format
  (`diff/corpus/*.nock`). Cover: every `phi w` on the TABLE-REPORT subject
  corpus; the 26 Class D oracle programs × 26 subjects; the `Gate.lean` and
  `Rec.lean` examples.
- Add lean-nock's `nockF` as an engine in pure-nock-lean's `diff/compare.py`,
  or a sibling script, and run lean-nock ↔ pure-nock-lean on both corpora.
- With a Nockchain checkout:
  `NOCKCHAIN_ROOT=… scripts/gate-pure-nock.sh --with-nockvm-diff` on the
  exported corpus. This puts lean-nock's co-derived formulas in front of the
  production interpreter.

**9.2 Formal bridge.**
- A separate Lake package `bridge/`, with its own `lean-toolchain` (4.31) and
  lakefile. It requires lean-nock by path (`..`) and pure-nock-lean by git at
  tag `ncc/pure-nock-drop1.2.2`.
- `Bridge.lean`: a noun translation (both types are `atom Nat | cell`, so it
  is structural) and the verdict correspondence:

  ```lean
  theorem value_iff (a f v) : (∃ k, nockF k a f = some (.val v)) ↔
      ∃ n, Nock.Verb.evalProgram n ⟦a⟧ ⟦f⟧ = .value ⟦v⟧
  theorem crash_iff (a f)   : (∃ k, nockF k a f = some .exit) ↔
      ∃ n, Nock.Verb.evalProgram n ⟦a⟧ ⟦f⟧ = .crash
  ```

  These are restricted to formulas without opcode 11 unless bridged through
  pure-nock-lean's hint engine (`runHint`, `PureCompleteHint`). They may also
  be restricted off divergence, per 9.0.2.
- Audit tier `#audit_pure` with allow-list
  `{propext, Classical.choice, Quot.sound}`, used only in `bridge/`. Add a
  gate: no `Nock/` module imports anything from `bridge/`.
- CI: a separate job using the Mathlib cache (`lake exe cache get`), so the
  main job stays dependency-free.

**Known semantic seams to check** (each is either a lemma or a finding):
- opcode 6: lean-nock uses the semantic reading (a non-loobean test crashes),
  not the spec's macro expansion;
- opcode 9: lean-nock unfolds `*[*[a c] 2 [0 1] 0 b]` one step;
- opcode 11: lean-nock evaluates a dynamic clue strictly;
- opcode 10 at an invalid axis: both say crash (pure-nock-lean's finding is
  against nockvm, not lean-nock).

**Licensing.** Depend on pure-nock-lean; do not vendor its code into this MIT
repository. If any file is ever copied, carry its Apache-2.0 `NOTICE`.

**Effort.** 9.0–9.1: small to moderate. 9.2: moderate to large, since it
relates big-step to small-step and the size depends on 9.0.2.

---

## 10. Paper: replace the `eq` example (mss.tex §Ad Hoc, line ~133)

**Problem.** The paper says the mechanization "surfaced a live instance" of
divergences "for which no test at any coverage carries signal (the operand
order in `eq`)". But the order is invisible to every *observation*, not just
every test. `tisN` is symmetric in value, and whichever operand lookup runs
first, the formula crashes on exactly the same subjects. It mattered only to
how the proof closes (TABLE-REPORT, note 1). Calling it a divergence
overstates it.

**Better evidence, for harness caveat 2 (mote preservation, line ~198).**
pure-nock-lean's differential harness found that `nockvm` **panics** on an
opcode-10 edit at an invalid axis, where Nock specifies a deterministic crash.
Witnesses: `[42 10 [0 [1 99]] 0 1]`, `[[1 2] 10 [0 [1 [7 8]]] 0 1]`,
`[[1 2] 10 [4 [1 99]] 0 1]`, `[[1 2] 10 [5 [1 99]] 0 1]`. A panic is an abort,
not `%exit`, so `+mock` cannot turn it into `[%| trace]`. It is a live,
production instance of exactly the coarsening that caveat 2 warns about, and a
test (the differential harness) caught it.

**Before editing, verify.**
1. The finding is still open against current `nockchain` master. It was
   recorded at `d278ef85`; the remediation patch in pure-nock-lean's
   `patches/` is not an upstream PR.
2. What Vere does on the same four witnesses, so the paper doesn't imply
   something about Vere it hasn't checked.
3. The author approves citing the finding. It is public, but it is Zorp's.

**Proposed text** (to be finalized after verification):
- §Ad Hoc, line ~133: "Our own mechanization surfaced an instance of the
  adjacent class, a mismatch between the operand order of `eq`'s Nock formula
  and its C routine. No test can detect it because no observation can. It
  matters only to the proof, which closes in one order and not the other."
- Harness caveat 2, a footnote: "This is not hypothetical. A differential
  harness against a formal Nock semantics \citep{PureNockLean} found that
  NockVM aborts on an opcode-10 edit at an invalid axis, where Nock specifies
  a deterministic crash; under `+mock` the two are distinguishable."
- Add a `PureNockLean` entry to `mss.bib` (repository, tag, access date).

**Effort.** Small once the three checks are done.
