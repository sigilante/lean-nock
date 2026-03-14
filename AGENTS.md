# AGENTS.md — Project Context for AI Assistants

Updated after sub correctness proof (post-`75b81f7`, 2026-03-13).

---

## Project: Nock 4K Formal Verification in Lean 4

Formal verification of a Nock 4K interpreter and Hoon standard-library gates,
with the goal of producing a zero-knowledge proof of correct Nock execution.
Recapitulates and extends the Aleo/Leo Nock zkVM project in Lean 4.

## Architecture

- **Proof target**: `NockEval subject formula result : Prop` — inductive relation
  with 14 constructors (one per Nock 4K rule).  All formal reasoning goes through
  this; the `partial def nock` evaluator is for `#eval` testing only.
- **No Mathlib** — pure Lean 4 core; `omega` in place of `ring`.
- **No `sorry`, no custom axioms** — only `propext`, `Quot.sound`.

## Module map

| File | Contents |
|---|---|
| `Nock/Basic.lean` | `Noun` type; `wut`, `lus`, `tis`, `fas`, `hax`; `partial def nock` |
| `Nock/Proofs.lean` | 17 lemmas for `fas` and `hax` (base, recursion, corollaries) |
| `Nock/Eval.lean` | `NockEval` inductive relation + sanity examples |
| `Nock/HoonOne.lean` | `decFormula`, `decGate`, `callGate_gate_eval`, `dec/add/sub` loop invariants + correctness |
| `Nock/Notation.lean` | `n!` macro: compile-time Nock bracket notation parser |
| `Main.lean` | `#eval` smoke tests |

## What's proved

- All Nock primitives (`wut`, `lus`, `tis`, `fas`, `hax`) have full lemma libraries.
- `NockEval` relation is complete (all 14 Nock rules).
- `callGate_gate_eval`: generic gate-call lemma (op9 + op10 sample replacement).
- `decGate` pinned to kernel-transparent `n!` literal via `native_decide`.
- `hax_six`: the key sample-replacement lemma for gate calls.
- **`dec_loop_inv`**: loop invariant for `++dec` — induction on remaining iterations.
  Axioms: `propext`, `Quot.sound` only.
- **`dec_correct`**: full correctness — `NockEval [decBat [n+1 ctx]] decBat (atom n)`.
  Axioms: adds `native_decide` dependencies (`Lean.ofReduceBool`, `Lean.trustCompiler`,
  `Classical.choice`) for structural decomposition of `decBat`.
- **`add_loop_inv`** / **`add_correct`**: `NockEval [addBat [[m n] ctx]] addBat (atom (m+n))`.
  Parametric over `AddCtx ctx` — abstracts the dec-calling mechanism (axis 2398 of 8191).
  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- **`sub_loop_inv`** / **`sub_correct`**: `NockEval [subBat [[a b] ctx]] subBat (atom (a-b))` for `b ≤ a`.
  Parametric over `SubCtx ctx` — abstracts two dec calls (axes 28 and 29).
  Battery includes `~_` hint (op11_dynamic) on every iteration.
  Crash for `b > a` modeled as absence of `NockEval` derivation.
  Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## What's not yet proved

- `AddCtx`/`SubCtx` instances for a concrete verified core (dec wiring).
- Determinism of `NockEval`.
- `mul`, `div`, `lth` correctness (Tier 1 arithmetic).
- Algebraic laws (Tier 2).
- Fuel-based interpreter `nockF` and soundness/completeness bridge.
- Circuit correspondence (Tier 3 / zkVM goal).

## Proof roadmap

### Tier 1 — Arithmetic correctness
1. ~~dec loop invariant~~ ✓
2. ~~dec correctness~~ ✓
3. ~~add loop invariant + correctness~~ ✓ (parametric over `AddCtx`)
4. ~~sub loop invariant + correctness~~ ✓ (parametric over `SubCtx`, crash as absence)
5. **Verified core** — concrete `Noun` with dec at right axis; `AddCtx`/`SubCtx` instances.
6. **mul/div/lth** — same pattern; mul will need `AddCtx` + `MulCtx`.

### Tier 2 — Semantic infrastructure
7. **Determinism** — `NockEval s f r₁ → NockEval s f r₂ → r₁ = r₂`, by induction on derivation.
8. **Fuel interpreter** — `nockF : Nat → Noun → Noun → Option Noun`, total transparent `def`.
   Soundness: `nockF fuel s f = some r → NockEval s f r`.
   Completeness: `NockEval s f r → ∃ fuel, nockF fuel s f = some r`.
9. **Algebraic laws** — commutativity of add, distributivity, cancellation `sub (add n k) n = k`.

### Tier 3 — zkVM circuit (6 phases)
Architecture follows Kattis et al. 2025 (`/refs/2025-1110.pdf`): two RAP tables
(compute + memory) linked by LogUp IO consistency, over Goldilocks field.

10. **Phase 1: Finite field infra** — `ZMod p`, Goldilocks field, degree-3 extension,
    polynomial evaluation, Schwartz-Zippel lemma.
11. **Phase 2: Noun Polynomial Representation** — NPR encoding of `Noun` as polynomial
    tuples `(size, data_poly, dyck_poly)`. Fingerprinting, collision bounds, recursive
    decomposition via `cons` (3 algebraic checks per node). Atom size bound `< p`.
12. **Phase 3: RAP formalization** — `structure RAP` with trace, transition constraints,
    satisfiability. Multiset equality (LogUp). One-hot opcode encoding.
13. **Phase 4: NockVM circuit** — `RAPNockComp` (compute table, one opcode per row,
    57e+13 columns, 20e+13 degree-4 gates) and `RAPNockMem` (memory table, noun validity
    + axis verification, 54e+5 columns). IO matching via LogUp accumulators.
14. **Phase 5: Soundness + completeness** — Crown theorems:
    `circuit_sound`: RAP satisfied → `NockEval` holds.
    `circuit_complete`: `NockEval` derivation (bounded size) → satisfying RAP trace.
15. **Phase 6: Witness generation** (optional) — executable Lean code producing
    concrete field-element traces from `NockEval` derivations, exportable to prover backends.

### Key zkVM limitations (details in README.md)
- **Atom size bound**: atoms must fit in F_p (64 bits for Goldilocks); multi-limb for larger.
- **Fixed trace length**: RAP rows fixed a priori; recursive composition not formalized.
- **OP10 gap**: reference paper excludes `#` (tree edit); our proofs use it heavily (hax_six).
  Must either inline OP10 as read+cons or extend memory table to RAM.
- **Hints are no-ops**: jet-accelerated crypto (SHA-256 etc.) requires full Nock expansion.
- **Lean verifies circuit design, does not produce executable ZK proofs.**

## Key technical notes

- `simp [fas]` works; `simp [nock]` does not (`nock` is opaque).
- `NockEval.op0` leaves `fas` unreduced — rewrite with the appropriate `fas_*` lemma.
- `hax_six` is the gate-call key: replaces axis 6 (sample) preserving battery and context.
- `n!` literals are kernel-transparent; `native_decide` bridges opaque `nock` results.
- Loop invariant does NOT require fuel — construct `NockEval` derivations directly.
- **Dec proof pattern** (reusable for add/mul/etc.):
  1. Define `xxxLoopBat` (loop body formula) and `xxxLoopCore` (loop subject).
  2. Prove helper lemmas: condition eval, slot access, core edit (op10+hax_six).
  3. Prove loop invariant by induction on `n - b` with `obtain ⟨d, hd⟩; subst; induction d`.
  4. Prove `xxx_correct` by tracing through outer gate: op11→op6→op8→op8→op9→loop_inv.
  5. Use `show` for definitional rewrites (formula decomposition without touching subject).

## Reference

- `/refs/2025-1110.pdf` — Aleo/Leo partial proof system (comparison target).
