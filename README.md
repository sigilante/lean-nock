# Nock zkVM — Lean 4 Formal Verification

Formal verification of a [Nock 4K](https://developers.urbit.org/reference/nock/definition)
interpreter and Hoon standard-library gates in Lean 4, with the goal of producing a
zero-knowledge proof of correct Nock execution.

This work recapitulates and extends the
[Aleo/Leo Nock zkVM project](https://github.com/aleo-org/nock-leo) in Lean 4,
using an inductive relational semantics as the proof target.

---

## Building and running

**Requirements:** [elan](https://github.com/leanprover/elan) (installs Lean automatically via `lean-toolchain`)

```sh
# Build the entire library (downloads Lean 4.28.0 on first run)
lake build

# Run the evaluator smoke tests
lake exec main

# Check a specific module
lake env lean Nock/Eval.lean
```

All proofs are kernel-checked. No `sorry`, no custom axioms — only Lean 4's
standard foundations (`propext`, `Quot.sound`):

```sh
# Verify the axiom footprint of a key theorem
lake build Nock.HoonOne
# then in a scratch file: #print axioms callGate_gate_eval
```

---

## Project structure

```
Nock/
  Basic.lean    — Noun type; wut, lus, tis, fas, hax primitives; nock evaluator
  Proofs.lean   — Proved lemmas for fas and hax (tree navigation and edit)
  Eval.lean     — NockEval inductive relation (the proof target)
  HoonOne.lean  — Hoon ++dec gate compiled to Nock; callGate helper; gate-call theorem
Main.lean       — Evaluator smoke tests (#eval)
```

---

## Architecture

### The proof target: `NockEval`

`NockEval subject formula result : Prop` is an inductive relation with one
constructor per Nock 4K rule.  It is **the formal specification of Nock execution**
and the direct target for zkVM proofs.

```lean
inductive NockEval : Noun → Noun → Noun → Prop where
  | op0  : NockEval a (cell (atom 0) fol) (fas fol a)
  | op1  : NockEval a (cell (atom 1) fol) fol
  | op9  : NockEval a c core →
           NockEval core (fas b core) r →
           NockEval a (cell (atom 9) (cell b c)) r
  -- ... one constructor per opcode
```

A ZK proof that a Nock computation happened is precisely a proof that a
`NockEval` derivation exists.  Each constructor maps to a circuit constraint.

### Why not `partial def nock`?

`partial def` in Lean 4 compiles to `opaque` — the kernel cannot see the body,
so no equations can be proved about it.  The `nock` evaluator in `Basic.lean`
is kept for `#eval` testing only.  All formal reasoning goes through `NockEval`.

To connect the evaluator to the relation (soundness + completeness), a
fuel-based `def nockF (fuel : Nat) : Noun → Noun → Option Noun` is planned —
see [Roadmap](#roadmap) below.

### Primitive layers

`fas` (tree address) and `hax` (tree edit) are transparent `def`s with full
lemma libraries:

| Layer | Theorems |
|---|---|
| `fas` base cases | `fas_one`, `fas_head`, `fas_tail` |
| `fas` recursion | `fas_rec_even`, `fas_rec_odd` |
| `fas` corollaries | `fas_four` … `fas_seven` |
| `hax` base case | `hax_one` |
| `hax` recursion | `hax_rec_even`, `hax_rec_odd` |
| `hax` corollaries | `hax_two`, `hax_three`, `hax_six` |

`hax_six` is the key lemma for gate calls: replacing axis 6 (sample) in a
standard gate `[battery [sample context]]` leaves the battery intact.

---

## Roadmap

### Tier 1 — Arithmetic correctness (immediate)

Prove that each Hoon gate, compiled to Nock, computes the correct mathematical
function via a `NockEval` derivation.

| Gate | Target theorem |
|---|---|
| `++dec` | `NockEval decCore (atom (n+1)) (atom n)` |
| `++add` | `NockEval addCore (cell (atom m) (atom n)) (atom (m+n))` |
| `++mul` | `NockEval mulCore (cell (atom m) (atom n)) (atom (m*n))` |
| `++div` | `n = (div n d) * d + (mod n d)`, `mod n d < d` |
| `++lth` | `NockEval lthCore ... (atom 0) ↔ m < n` |

### Tier 2 — Algebraic laws

Prove the compiled gates satisfy algebraic identities:
commutativity and associativity of `add`, distributivity of `mul` over `add`,
cancellation `sub (add n k) n = k`.

### Tier 3 — zkVM circuit (the goal)

- **Soundness**: circuit accepts trace → `NockEval` holds
- **Completeness**: every `NockEval` derivation → satisfying circuit assignment
- **Computation witnesses**: typed ZK witness for specific computations (e.g. `dec 42 = 41`)

### Infrastructure prerequisites

- **Fuel-based interpreter** (`nockF : Nat → Noun → Noun → Option Noun`):
  a total transparent `def` enabling soundness/completeness proofs connecting
  the evaluator to `NockEval`
- **`dec` loop invariant**: the immediate next proof target; establishes the
  pattern used by all higher arithmetic

### Out of scope (for now)

- Cryptographic jets (SHA-256 etc.) — Nock formulas are too large
- Hoon type system soundness (`++nest`, `++mull`) — multi-year project
- Divergence / `~` (requires fuel semantics to state)

---

## Key technical notes

- **No Mathlib** — pure Lean 4 core only; use `omega` in place of `ring`
- **`simp [fas]` works; `simp [nock]` does not** — `fas`/`hax` are transparent `def`s; `nock` is opaque
- **Proof recipe for `fas`/`hax` recursion**: bridge with `omega`, then `simp only [fas/hax, h]; rw [if_pos/neg]`
- **`NockEval.op0` leaves `fas` unreduced** — rewrite at the call site with the appropriate `fas_*` lemma
- **`hax_six` is the gate-call key**: `hax (atom 6) arg (cell bat (cell sam ctx)) = cell bat (cell arg ctx)`
