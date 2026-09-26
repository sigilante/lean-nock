# Roadmap: remaining work against the companion paper

Status at `v0.7`: every claim the paper makes about the artifact is
discharged, and items 8 and 10 are done. Item 9 remains: it strengthens the
paper, but no claim the paper makes depends on it.

---

## 8. A `+mock` model — DONE (`v0.7`, `Nock/Mock.lean`)

`two_valued_unsound`: the canonical count-up `dec`, jetted by native
decrement, agrees on every value (`natDec_twoValued`), yet under `+mock` the
jetted call on `0` observes `[2 ~]` while the formula diverges.
`three_valued_sound` / `three_valued_mock`: a jet meeting (1a)–(1c), with
punting allowed anywhere, is indistinguishable from its formula.
`word_jet_sound`: every Λ word, jetted by its C model, meets the contract.

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
2. **Evaluation-order probe — DONE (2026-09-26).** Each test program races a
   diverging operand (`countUp` on `0`) against a crashing one (`[0 0]`), per
   rule.
   - **Vere and NockVM** (by source reading: Vere `develop` `40a69573e9`,
     NockVM `73877be2`) evaluate left to right, except that opcode 10
     evaluates the tree before the patch.
   - **lean-nock** evaluated opcode 10 patch-first. It is **fixed**: now
     tree-first, pinned by `Order.lean`.
   - **pure-nock-lean** (its own evaluator files, Lean 4.31) evaluates
     autocons and opcodes 2 and 5 **right to left**, because its step
     function picks the pending redex with the largest depth-first index. It
     is tree-first on opcode 10, and it crashes on every opcode 11, since
     hints are outside its paper-domain interpreter. It therefore reaches the
     other bottom from both runtimes on crash-versus-divergence races.
     Reported to its maintainers.
   - **Consequence for 9.2:** a formal bridge can claim agreement only where
     no such race occurs, or once pure-nock-lean adopts the runtime order.

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

## 10. Paper: replace the `eq` example — DONE (paper edited at `v0.7`)

Verification, 2026-09-26:
1. **Still open in NockVM.** At `nockchain/nockchain` `origin/master`
   `73877be2`, `edit_with_space` (`crates/nockvm/rust/nockvm/src/interpreter.rs`)
   calls `.expect("0 is not allowed as an edit axis")` and
   `.expect("Invalid axis for edit")`. The opcode-10 dispatch validates
   argument shape (`BAIL_EXIT`) but never the axis, and nothing on the
   interpreter path catches the panic.
2. **Vere is correct.** At `urbit/vere` `develop` `40a69573e9`, `u3i_edit`
   (`pkg/noun/imprison.c`) bails `c3__exit` at axis 0 and when it descends
   into an atom.
3. The author approved citing the finding.
