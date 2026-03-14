# Nock 4K ❖ Lean 4 Formal Verification

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

### Tier 1 — Arithmetic correctness

Prove that each Hoon gate, compiled to Nock, computes the correct mathematical
function via a `NockEval` derivation.

| Gate | Status | Theorem |
|---|---|---|
| `++dec` | **done** | `NockEval [decBat [n+1 ctx]] decBat (atom n)` |
| `++add` | **done** | `NockEval [addBat [[m n] ctx]] addBat (atom (m+n))` (parametric `AddCtx`) |
| `++sub` | **done** | `NockEval [subBat [[a b] ctx]] subBat (atom (a-b))` for `b ≤ a` (parametric `SubCtx`) |
| `++mul` | planned | same pattern; calls `++add`, needs `MulCtx` |
| `++div` | planned | `n = (div n d) * d + (mod n d)`, `mod n d < d` |
| `++lth` | planned | `NockEval lthCore ... (atom 0) ↔ m < n` |

### Tier 2 — Semantic infrastructure

- **Verified core** — concrete `Noun` with dec at correct axes; `AddCtx`/`SubCtx` instances
- **Determinism** — `NockEval s f r₁ → NockEval s f r₂ → r₁ = r₂`
- **Fuel interpreter** — `nockF : Nat → Noun → Noun → Option Noun`, total and transparent;
  soundness (`nockF fuel s f = some r → NockEval s f r`) and
  completeness (`NockEval s f r → ∃ fuel, nockF fuel s f = some r`)
- **Algebraic laws** — commutativity/associativity of add, distributivity, cancellation

### Tier 3 — zkVM circuit (the goal)

Formalize a zero-knowledge proof system for Nock execution in Lean 4.
The goal: given a claim "program P on input I produces output O",
produce a succinct proof verifiable without re-executing P.

See the [zkVM architecture](#zkvm-architecture) section below for the full plan.

### Out of scope (for now)

- Cryptographic jets (SHA-256 etc.) — Nock formulas are too large for in-circuit proof
- Hoon type system soundness (`++nest`, `++mull`) — multi-year project
- Divergence / `~` (requires fuel semantics to state)
- Executable ZK prover — we verify the *circuit design*, not build a prover

---

## zkVM Architecture

### Overview

A ZK proof of Nock execution is a proof that a valid `NockEval` derivation
exists for a given (subject, formula, result) triple.  The derivation tree is
the *witness*; the circuit checks that every node in the tree applies a valid
Nock rule.

Following [Kattis et al. 2025](/refs/2025-1110.pdf), the circuit is split into
two independently verifiable tables linked by IO consistency:

```
                ┌──────────────┐
                │ Compute Table│  — verifies opcode resolution
                │  (NockEval   │     one opcode per row
                │   derivation)│
                └──────┬───────┘
                       │  IO: memory read requests
                       │  (multiset equality via LogUp)
                ┌──────┴───────┐
                │ Memory Table │  — verifies noun validity
                │  (tree       │     and axis lookups
                │   structure) │
                └──────────────┘
```

Both tables are arithmetized as RAPs (Randomized AIR with Preprocessing) over
the Goldilocks field (p = 2^64 - 2^32 + 1), compilable to SNARKs via standard
IOP frameworks.

### Phase 1 — Finite field and polynomial infrastructure

New modules for arithmetic over finite fields and polynomials:

```lean
-- Nock/Field.lean
def ZMod (p : Nat) := Fin p           -- integers mod p
instance : Field (ZMod p)             -- ring/field operations
def Goldilocks := ZMod (2^64 - 2^32 + 1)

-- Nock/Poly.lean
def Poly (F : Type) := List F         -- coefficient representation
def eval (f : Poly F) (x : F) : F     -- polynomial evaluation
```

Key results needed:
- Schwartz-Zippel lemma (collision bound for polynomial identity testing)
- Extension field `K` of degree 3 over Goldilocks (for 192-bit security)

### Phase 2 — Noun Polynomial Representation (NPR)

Encode nouns as polynomial tuples for succinct in-circuit representation
([Kattis §4.4](/refs/2025-1110.pdf)):

```lean
-- A noun (proper binary tree with λ leaves) is encoded as:
structure NPR (F : Type) where
  size : Nat                    -- λ (number of leaves)
  data : Poly F                 -- leaf values: Σ dᵢ Xⁱ⁻¹
  dyck : Poly F                 -- tree structure: Σ wᵢ Xⁱ⁻¹  (Dyck word)

-- Fingerprint: evaluate at random r ∈ K
def fingerprint (n : NPR F) (r : K) : K × K × K :=
  (r ^ n.size, eval n.data r, eval n.dyck r)
```

Key results needed:
- **Collision bound**: `Pr[fn(n₁;r) = fn(n₂;r) | n₁ ≠ n₂] ≤ 2(2Λ-1)/|K|`
- **Recursive decomposition**: `n = cons(nL, nR)` ↔ three algebraic equations
  on NPR polynomials (Lemma 4.8 in the reference)
- **Noun ↔ NPR bijection**: our `Noun` type maps to/from `NPR Goldilocks`
  (with an atom size bound — see Limitations)

### Phase 3 — Constraint system formalization

Define what a RAP is in Lean and what it means for a trace to satisfy one:

```lean
-- Nock/Circuit.lean
structure RAP (F : Type) where
  num_cols    : Nat                         -- trace width
  num_rows    : Nat                         -- trace length (power of 2)
  constraints : List (TraceRow F → TraceRow F → F)  -- transition gates
  -- constraint C is satisfied iff C(row_i, row_{i+1}) = 0

-- A trace satisfies a RAP iff all constraints vanish on all adjacent rows
def satisfies (trace : Matrix F) (rap : RAP F) : Prop :=
  ∀ i < rap.num_rows - 1, ∀ C ∈ rap.constraints,
    C (trace.row i) (trace.row (i+1)) = 0
```

Also formalize:
- **Multiset equality** (LogUp argument) for IO consistency between tables
- **One-hot encoding** for opcode selection columns

### Phase 4 — NockVM circuit specification

Define the concrete compute and memory table RAPs:

**Compute table** (`RAPNockComp`):
- One row per opcode resolution in the `NockEval` derivation tree
- Columns: opcode selector (one-hot), subject NPR, formula NPR, output NPR,
  subformula NPRs, memory request registers, IO accumulator
- Transition constraints verify each opcode maps (subject, formula) → output
  correctly, given the subformula evaluations
- Memory requests for OP0 (slot lookups): root + axis → child

**Memory table** (`RAPNockMem`):
- Verifies noun validity via recursive `cons` decomposition (Thm 4.9)
- Verifies axis lookups via batch counting (`axis_indicator`, `axis_counts`)
- One row per tree node traversed + memory record verified

**IO matching**:
- Compute table emits memory read requests into a LogUp accumulator
- Memory table resolves them, linked by multiset equality
- Terminal constraint: both accumulators equal zero

### Phase 5 — Soundness and completeness

The crown theorems connecting `NockEval` to the circuit:

```lean
-- Soundness: circuit satisfaction implies semantic correctness
theorem circuit_sound (trace_comp trace_mem : Matrix Goldilocks)
    (h_comp : satisfies trace_comp RAPNockComp)
    (h_mem  : satisfies trace_mem  RAPNockMem)
    (h_io   : io_consistent trace_comp trace_mem) :
    NockEval (decode_subject trace_comp)
             (decode_formula trace_comp)
             (decode_output trace_comp)

-- Completeness: every NockEval derivation has a satisfying trace
theorem circuit_complete (s f r : Noun)
    (h : NockEval s f r)
    (h_bound : noun_size s + noun_size f ≤ MAX_SIZE) :
    ∃ tc tm, satisfies tc RAPNockComp ∧
             satisfies tm RAPNockMem ∧
             io_consistent tc tm ∧
             decode_subject tc = s ∧
             decode_formula tc = f ∧
             decode_output tc = r
```

Proof strategy:
- **Soundness** by induction on trace rows, showing each row's constraints
  force a valid `NockEval` constructor application
- **Completeness** by induction on the `NockEval` derivation, constructing
  trace rows for each constructor

### Phase 6 — Witness generation (optional)

Given a concrete `NockEval` derivation (e.g., `dec_correct 42`), generate
the actual field-element traces that satisfy the RAPs.  This would be
executable Lean code producing ZK witnesses exportable to a prover backend
(Plonky3, Halo2, etc.).

---

## Limitations and open problems

### Atom size bound

Nock atoms are arbitrary-precision `Nat`.  ZK circuits operate over a finite
field F_p.  The NPR encodes each atom as a single field element, requiring
atoms < p.  With the Goldilocks field (p ≈ 2^64), this bounds atoms to 64
bits.  Larger atoms require multi-limb representation, which multiplies
constraint counts per arithmetic operation.

**Impact on our proofs**: `dec_correct`, `add_correct`, `sub_correct` are
stated over unbounded `Nat`.  The circuit theorems will carry an explicit
bound `n < p`, and the bridge theorems will have this as a hypothesis.

### Fixed trace length

A RAP has a fixed number of rows (a power of 2).  The prover must know the
maximum trace length before proving.  Programs exceeding this length cannot
be proved in a single proof.  Recursive proof composition (folding schemes
like Nova/Sangria) could lift this bound but are not formalized here.

### OP10 (tree edit / `hax`)

The reference paper's NockVMROM explicitly **excludes OP10** (`#`, tree edit).
Our semantic proofs rely heavily on OP10 — every gate call uses `hax_six`.
Supporting OP10 in the circuit requires extending the memory table to handle
writes (not just reads), which the reference paper leaves to future work.

This is the single largest gap between our semantic layer and the circuit
layer.  Two approaches:
1. **Inline OP10**: expand `hax` operations into sequences of reads + cons,
   producing a larger but OP10-free derivation tree
2. **Extend the memory table**: add write semantics with timestamp ordering,
   turning ROM verification into RAM verification

### Hint semantics (opcode 11)

Both our `NockEval` and the reference circuit treat hints as no-ops.  This
means jet-accelerated computations (SHA-256, ed25519, secp256k1) cannot be
proved via their jet — the full Nock formula must be expanded.  For
cryptographic jets, these formulas are impractically large (millions of Nock
steps).  Practical deployment would require either:
- Specialized sub-circuits for each jet
- A "jet registry" with pre-verified circuit gadgets

### Crash completeness

Our proofs handle crashes by *absence*: `sub_correct` requires `b ≤ a`, and
no `NockEval` derivation exists when `b > a`.  The circuit must also correctly
*reject* invalid computations.  This requires either:
- Explicit crash states in the circuit (the Zorp approach: `⊥` in the
  transition function)
- A fuel-based interpreter returning `none`, with a soundness proof that
  `none` implies no `NockEval` derivation exists

### No Mathlib

Building finite field theory, polynomial arithmetic, Schwartz-Zippel, and
extension fields from scratch is substantial.  We may eventually need to:
- Import a minimal Mathlib subset (`ZMod`, `Polynomial`, `Finset`)
- Or prove lightweight versions sufficient for our specific field/degree

### Lean as verifier, not prover

This project produces a *verified circuit specification* — a Lean proof that
the RAP constraints correctly capture `NockEval` semantics.  It does **not**
produce an executable ZK prover.  To generate actual ZK proofs, the circuit
specification would need to be exported to a prover implementation (Plonky3,
Halo2, or the Zorp prover).

---

## Key technical notes

- **No Mathlib** — pure Lean 4 core only; use `omega` in place of `ring`
- **`simp [fas]` works; `simp [nock]` does not** — `fas`/`hax` are transparent `def`s; `nock` is opaque
- **Proof recipe for `fas`/`hax` recursion**: bridge with `omega`, then `simp only [fas/hax, h]; rw [if_pos/neg]`
- **`NockEval.op0` leaves `fas` unreduced** — rewrite at the call site with the appropriate `fas_*` lemma
- **`hax_six` is the gate-call key**: `hax (atom 6) arg (cell bat (cell sam ctx)) = cell bat (cell arg ctx)`
