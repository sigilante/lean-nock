# lean-nock ❖ Jet correctness for Nock, in Lean 4

A Lean 4 mechanization of **jet correctness** for the Nock 4K combinator
calculus: the companion artifact to *Jet-Accelerated Code and the Co-Design
Problem* (N. E. Davis, *Urbit Systems Technical Journal*).

A jet is a native routine that stands in for a Nock formula. Its contract is
three-valued: on every subject, the formula and the jet must agree on the value
returned, agree on deterministic crashes (`%exit`), and the jet may only bail
or punt where the formula diverges. Crashes are observable under virtualization
(`+mock`), so a two-valued contract is unsound.

This repository mechanizes the paper's **co-derivation** approach. A
concatenative source language Λ is compiled by two folds: `Λ_N` to Nock and
`Λ_C` to a big-step model of C. A composition theorem then reduces every proof
obligation to a small, closed set of leaf proofs plus the control-flow schemas.

Everything cited by the paper is kernel-checked. The footprint of every cited
theorem is within `{propext, Quot.sound}`, and the build fails if that ever
changes (see [Audit](#the-audit-manifest)).

---

## What is proved

| Paper claim | Status | Where |
| --- | --- | --- |
| Nock 4K semantics, three-valued (value / crash / divergence) | relation + fuel interpreter, sound, complete, deterministic | `Eval.lean`, `Fuel.lean` |
| Table A leaf contracts (`dup drop swap over cons head tail`) | **discharged**, over all nouns | `leaf_correct` |
| Table B leaf contracts (`inc eq cel?`) | **discharged**, over all nouns | `leaf_correct` |
| Table C: guarded `dec` (algorithm substitution) | **discharged** | `leaf_correct` (`leaf_dec`) |
| Composition over the free monoid of words | **discharged** | `composition`, `composition_agree` |
| Class D: `ifte` and `while` schemas; agreement on values and crashes | **discharged** | `composition_term` |
| Class D: agreement on divergence ("equal least fixed points") | **discharged** | `composition_diverges` |
| Hints are transparent to the composition theorem | **discharged, with a side condition**: a dynamic hint's clue must produce a value | `composition_hint`, `composition_hint_const`, `hint_not_transparent` |
| The Λ program packaged as a one-armed gate core (load/unload shim) | **discharged**, on values, crashes, and divergence | `gate_term`, `gate_diverges`, `gate_fire`, `gate_call` |
| Battery identity: the dispatch key depends only on the source term | **discharged** | `gate_battery` |
| Hoon's compiled `++dec`: value, underflow crash, divergence on a cell | **discharged** | `dec_correct`, `dec_underflow`, `dec_cell_diverges` |
| Hoon's `++dec` naively lifted is *not* a valid word (guards are necessary) | **discharged** | `liftGate_decBat_not_a_word` |

### What is *not* claimed

- **The C side is a model.** `cw` and `CEval` are Lean transcriptions of the
  paper's C listings, not compiled C. The gap between the model and Vere or
  NockVM is the paper's *harness contract*. That contract (mote-preserving
  strict sequencing, a load/unload bijection, exact bignums) is assumed, not
  proved.
- **Punting and nondeterministic bails are not modeled.** The mechanized
  agreement is the stronger biconditional: the C model diverges exactly when
  the Nock formula does. That strengthens the paper's clause (c), which only
  requires the jet to bail or punt where the formula diverges.
- **Class C beyond `dec`** (`add`, `sub`, `mul`, `div` as guarded words) is not
  yet mechanized. `HoonOne.lean` proves the value case of Hoon's compiled
  `++add`/`++sub`, which is a different artifact.
- **Named (recursive) definitions** are argued in the paper as instances of the
  `while` fixpoint schema; the term grammar here has no recursive definitions.

---

## Building and reproducing

Requires only [`elan`](https://github.com/leanprover/elan). The toolchain is
pinned by `lean-toolchain` (Lean 4.28.0). There are no dependencies: no
Mathlib, pure Lean 4 core.

```sh
# 1. Scrubbed build.  Elaborates the audit manifest, so a drifting axiom
#    footprint, a stray `sorry`, or a renamed cited theorem fails here.
rm -rf .lake/build && lake build

# 2. Repository discipline gates (quarantine direction, native_decide and
#    panic! containment, no sorry, no axiom declarations).
./scripts/gates.sh

# 3. Class D oracle: 676 runs (26 programs x 26 subjects), re-run at build time.
./scripts/oracle-check.sh
#    => oracle sweep: (632, 44, 0, 0)  (0 mismatches, 0 asymmetries)

# 4. Print every manifest footprint (informational).
./scripts/print-axioms.sh
```

CI runs all four on every pull request (`.github/workflows/ci.yml`).
`lake exec main` runs evaluator smoke tests, audits the quarantined bridge, and
re-runs the oracle sweep.

### The audit manifest

`Nock/Audit.lean` is elaborated as part of `lake build`. It **fails the build**
on three kinds of drift:

- an axiom footprint that grows beyond `{propext, Quot.sound}`;
- any `sorry` (it shows up as `sorryAx`);
- any rename or deletion of a manifest name, since the manifest doubles as the
  freeze list for theorems the paper cites.

Two modules are **quarantined**: nothing in the proof chain imports them, and
`scripts/gates.sh` enforces this.

- `Nock/RuntimeBridge.lean` uses `native_decide` to pin the `partial def nock`
  evaluator's output to the kernel-visible literals the proofs use. Its
  theorems trust the compiler (`Lean.ofReduceBool`), so they are audited
  separately by `#audit_bridge` in `Main.lean`.
- `Nock/Oracle.lean` is `CsemF`, a fueled executable model of the C listings.
  It is a testing oracle that refuted Table C's printed `dec` listing and then
  acquitted the Class D schemas before they were proved
  ([`TABLE-REPORT.md`](TABLE-REPORT.md)). An oracle can refute but cannot
  discharge.

### Citing this artifact

Cite a tag and its commit; theorem names in the audit manifest are frozen API.

```bibtex
@software{lean-nock,
  author  = {Davis, Neal},
  title   = {lean-nock: Mechanized Jet Correctness for Nock in {Lean} 4},
  year    = {2026},
  url     = {https://github.com/sigilante/lean-nock},
  version = {<TAG>},
  note    = {Tag \texttt{<TAG>}, commit \texttt{<COMMIT>}}
}
```

---

## Project structure

```
Nock/
  Basic.lean         — Noun; Option-valued primitives wut, lusO, tisN, fasO, haxO; runtime evaluator
  Proofs.lean        — Lemma library for fasO (slot) and haxO (edit)
  Eval.lean          — Outcome; NockEval, the three-valued big-step relation (the specification)
  Fuel.lean          — nockF fuel interpreter; soundness, completeness, determinism, divergence
  HoonOne.lean       — Hoon ++dec/++add/++sub compiled to Nock; the gate-call lemma
  DecDiverges.lean   — ++dec diverges on a cell; completes dec's ⊥ profile
  Comp.lean          — Words, their Nock formulas (Tables A–C), leaf contracts, monoid composition
  Shim.lean          — Calling a Hoon gate from a stack program; ++dec is provably not a word
  Term.lean          — Class D term algebra; Λ_N with the ifte / while schemas
  CEval.lean         — Big-step C model of the term algebra; forward simulation
  Backward.lean      — Backward simulation, by strong induction on fuel
  Composition.lean   — composition_term, composition_diverges
  Hint.lean          — Opcode-11 hint transparency, and when it fails
  Gate.lean          — A Λ program packaged as a one-armed gate core (deployment)
  Audit.lean         — Build-enforced axiom manifest and API freeze list
  Notation.lean      — n! bracket-notation macro for Noun literals
  RuntimeBridge.lean — native_decide bridge;  QUARANTINED
  Oracle.lean        — Fueled C model (CsemF); the Class D trial;  QUARANTINED
Main.lean            — Smoke tests; audits the bridge; runs the oracle sweep
scripts/             — gates.sh, oracle-check.sh, print-axioms.sh
SPEC*.md, DEFENDANT-CLASSD.md, TABLE-REPORT.md — design records and trial reports
```

`nockF` is proof-chain-legal and load-bearing: it supplies the height measure
for the backward simulation, since `NockEval` is `Prop`-valued and has none.
The quarantine governs `CsemF`, the C-side oracle, not `nockF`.

---

## Architecture

### The specification: `NockEval`

`NockEval subject formula outcome : Prop` has one constructor per Nock 4K rule,
plus explicit crash-propagation constructors.

```lean
inductive Outcome
  | val  : Noun → Outcome
  | exit : Outcome

inductive NockEval : Noun → Noun → Outcome → Prop where
  | crash_malformed : Malformed f = true → NockEval a f .exit
  | op0       : fasO fol a = some r → NockEval a (cell (atom 0) fol) (.val r)
  | op0_crash : fasO fol a = none   → NockEval a (cell (atom 0) fol) .exit
  | op9       : NockEval a c (.val core) → fasO b core = some arm →
                NockEval core arm o →
                NockEval a (cell (atom 9) (cell b c)) o
  -- ... one constructor per opcode, plus its crash-propagation variants
```

| outcome | representation |
| --- | --- |
| returns a noun `n` | `Outcome.val n` |
| deterministic crash, `%exit` | `Outcome.exit` |
| diverges | *no derivation exists*: `Diverges a f := ∀ o, ¬ NockEval a f o` |

Evaluation is left-to-right and strict, matching Vere and NockVM. The
crash-propagation constructors encode that order, which is what makes the
relation deterministic (`NockEval.deterministic`).

Crashes were once represented by absence, which was unsound rather than merely
incomplete. `panic!` reduces to `Inhabited.default = atom 0` in Lean's logic,
so the relation certified that `dec 0` returns `0`. The `Option`-valued
primitives plus `Outcome.exit` close that hole.

`partial def nock` compiles to an `opaque` constant, so it is for `#eval` only.
`nockF : Nat → Noun → Noun → Option Outcome` is the transparent evaluator:
`none` means fuel exhausted, not a verdict. `nockF_sound`, `nockF_complete`,
and `diverges_iff_fuel` tie it to the relation.

### Co-derivation

`Comp.lean` defines the words, their Nock formulas `phi w` (transcribed
verbatim from the paper's tables, which were put on trial rather than assumed),
and a model `cw w` of each C routine.

```lean
theorem leaf_correct (w : Word) (S : Noun) : NockEval S (phi w) (cw w S)
theorem composition  (p : Prog) (S : Noun) : NockEval S (N p) (Csem p S)
```

`Term.lean` extends the free monoid to the Class D term algebra
`p ::= ε | w·p | ifte(q₁,q₂)·p | while(p_t,p_b)·p`. `CEval` is a big-step
semantics for the C listings.

```lean
theorem composition_term (t : Term) (S : Noun) (o : Outcome) :
    NockEval S (NT t) o ↔ CEval t S o
theorem composition_diverges (t : Term) (S : Noun) :
    Diverges S (NT t) ↔ CDiverges t S
```

The fixpoint argument is discharged operationally, as a simulation pair:
forward by derivation induction (`ceval_sound`), backward by strong induction
on interpreter fuel (`nockeval_complete`).

### Deployment

Runtimes dispatch jets on cores `[battery payload]`, keyed on the battery, and
register them with `%fast` hints.

`Gate.lean` packages a compiled term as the one-armed core
`[gateArm t [sam ctx]]`. Its arm is `[7 [[0 6] [1 0]] [7 Λ_N(t) [0 2]]]`: load
the sample as the stack `[sam ~]`, run, and unload the top.

- `gate_term` and `gate_diverges` carry the composition theorem through the
  shim, against a C model with the same load/unload (`CGate`).
- `gate_fire` covers firing via `[9 2 0 1]`, and `gate_call` covers a
  Hoon-style call that edits the sample.
- `gate_battery` states that the battery is `gateArm t` whatever the sample and
  context.

`Hint.lean` settles when a hint leaves the proof untouched.

- A static hint `[11 t f]` is always transparent.
- A dynamic hint `[11 [t c] f]`, the shape `%fast` takes, is transparent **only
  when the clue formula `c` produces a value**. If `c` crashes, the hinted
  formula crashes regardless of `f` (`hint_not_transparent`). If `c` diverges,
  so does the hinted formula.
- Constant clues `[1 k]` are always transparent (`composition_hint_const`).

---

## Key technical notes

- **No Mathlib.** Pure Lean 4 core; use `omega` in place of `ring`.
- `fasO` and `haxO` compile by well-founded recursion and do not reduce under
  `rfl`. Use the named lemmas (`fasO_head`, `fasO_six`, `haxO_six`, …), not
  `decide`.
- `NockEval.op0` leaves `fasO` unreduced; rewrite at the call site with the
  matching `fasO_*` lemma.
- `haxO_six` is the gate-call key: editing axis 6 (the sample) of
  `[bat [sam ctx]]` leaves the battery and context intact.
- Inversion on a `NockEval` derivation plus `NockEval.deterministic` is the
  standard idiom for "the only possible outcome is …"; see `Gate.lean` and
  `Shim.lean`.
