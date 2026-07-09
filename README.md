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

All proofs are kernel-checked, with no `sorry`. The proof chain rests only on
Lean 4's standard foundations — `propext`, `Quot.sound`, and (where `simp`
introduces it) `Classical.choice`:

```sh
# Verify the axiom footprint of a key theorem
lake build Nock.HoonOne
# then in a scratch file: #print axioms dec_correct
```

One module is exempt. `Nock/RuntimeBridge.lean` uses `native_decide` to assert
that the noun computed by the `partial def nock` evaluator equals the
kernel-visible `n!` literal the proofs reason about. Those two theorems depend
on `Lean.ofReduceBool` and `Lean.trustCompiler`: they are checked by running
compiled code, not by the kernel. Nothing in the proof chain imports that
module, so `#print axioms dec_correct` stays free of `ofReduceBool`. The
invariant is enforceable by grep:

```sh
grep -rn "by native_decide" Nock/   # only Nock/RuntimeBridge.lean
grep -rn "panic!" Nock/             # only inside `partial def nock`
```

---

## Project structure

```
Nock/
  Basic.lean         — Noun type; wut, lusO, tisN, fasO, haxO primitives; nock evaluator
  Proofs.lean        — Proved lemmas for fasO and haxO (tree navigation and edit)
  Eval.lean          — Outcome type; NockEval inductive relation (the proof target)
  Fuel.lean          — nockF fuel interpreter; soundness, completeness, determinism, divergence
  HoonOne.lean       — Hoon ++dec/++add/++sub compiled to Nock; gate-call theorem
  Notation.lean      — n! bracket-notation macro for Noun literals
  RuntimeBridge.lean — native_decide bridge; NOT importable by the proof chain
Main.lean            — Evaluator smoke tests (#eval)
```

The dependency edge that matters: `RuntimeBridge` imports `HoonOne`, never the
reverse.  `Nock.lean` re-exports everything *except* `RuntimeBridge`.

---

## Architecture

### The proof target: `NockEval`

`NockEval subject formula outcome : Prop` is an inductive relation with one
constructor per Nock 4K rule, plus explicit crash constructors.  It is **the
formal specification of Nock execution** and the direct target for zkVM proofs.

```lean
inductive Outcome
  | val  : Noun → Outcome
  | exit : Outcome

inductive NockEval : Noun → Noun → Outcome → Prop where
  | crash_malformed : Malformed f = true → NockEval a f .exit
  | op0       : fasO fol a = some r → NockEval a (cell (atom 0) fol) (.val r)
  | op0_crash : fasO fol a = none   → NockEval a (cell (atom 0) fol) .exit
  | op1       : NockEval a (cell (atom 1) fol) (.val fol)
  | op9       : NockEval a c (.val core) → fasO b core = some arm →
                NockEval core arm o →
                NockEval a (cell (atom 9) (cell b c)) o
  -- ... one constructor per opcode, plus its crash-propagation variants
```

Note the shape of `op9`: its outcome `o` is passed through unchanged from the
tail-position subcomputation.  Only an intermediate result that a rule itself
*consumes* (like `core` above) needs a `.val` hypothesis and a matching
explicit crash constructor.

A ZK proof that a Nock computation happened is precisely a proof that a
`NockEval` derivation exists.  Each constructor maps to a circuit constraint.

### Why not `partial def nock`?

`partial def` in Lean 4 compiles to `opaque` — the kernel cannot see the body,
so no equations can be proved about it.  The `nock` evaluator in `Basic.lean`
is kept for `#eval` testing only.  All formal reasoning goes through `NockEval`.

`Nock/Fuel.lean` connects a *transparent* evaluator to the relation:
`nockF : Nat → Noun → Noun → Option Outcome`, where `none` means fuel
exhausted (no verdict) and `some .exit` means a real crash.  `nockF_sound`
and `nockF_complete` prove the two agree, which in turn yields determinism
and a statable notion of divergence.

### Primitive layers

`fasO` (tree address) and `haxO` (tree edit) are transparent, `Option`-valued
`def`s with full lemma libraries.  They return `none` exactly where Nock
crashes: axis 0, an axis into an atom, a cell axis.

| Layer | Theorems |
|---|---|
| `fasO` base cases | `fasO_one`, `fasO_head`, `fasO_tail`, `fasO_zero` |
| `fasO` recursion | `fasO_rec_even`, `fasO_rec_odd` |
| `fasO` corollaries | `fasO_four` … `fasO_seven` |
| `haxO` base case | `haxO_one`, `haxO_zero` |
| `haxO` recursion | `haxO_rec_even`, `haxO_rec_odd` |
| `haxO` corollaries | `haxO_two`, `haxO_three`, `haxO_six` |

The recursion equations and `haxO_two`/`haxO_three` are stated conditionally on
the sub-lookup succeeding (`fasO ... = some t`) rather than with `.get!`, which
would reintroduce the `Inhabited.default` hole the `Option` refactor closes.

`haxO_six` is the key lemma for gate calls: replacing axis 6 (sample) in a
standard gate `[battery [sample context]]` leaves the battery intact.  It is
unconditional — the gate shape guarantees both sibling lookups succeed.

Note that `fasO` and `haxO` compile by well-founded recursion, so they do not
reduce under `rfl`.  Use the named lemmas, not `decide`.

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

Nock computations are three-valued, and `NockEval` now represents all three:

| outcome | representation |
| --- | --- |
| returns a noun `n` | `Outcome.val n` |
| crashes | `Outcome.exit` |
| diverges | *no derivation exists* |

Crashes used to be represented by absence too, which was unsound rather than
merely incomplete. The primitives `fas`, `hax`, `lus`, `tis` handled their
crash arms with `panic!`, and in Lean's logic `panic!` reduces to
`Inhabited.default`, which for `Noun` is `atom 0`. So the relation certified
that axis-0 lookup returns `0`, that incrementing a cell returns `0`, and —
worst — that `dec 0` returns `0`. `Option`-valued primitives plus
`Outcome.exit` close that hole; `dec_underflow` now proves the crash.

Divergence remains absence-of-derivation, which is standard for a big-step
semantics, but it is no longer *unstatable*. `Nock/Fuel.lean` gives a fuel
interpreter `nockF : Nat → Noun → Noun → Option Outcome` and proves it agrees
with the relation (`nockF_sound`, `nockF_complete`, `nockF_mono`), whence:

- `NockEval.deterministic` — a subject and formula admit at most one outcome.
  Proved by pushing both derivations through the *function* `nockF` at a
  common fuel, not by double induction on the derivations.
- `diverges_iff_fuel : Diverges a f ↔ ∀ k, nockF k a f = none`.

Determinism depends on evaluation being left-to-right and strict: the
crash-propagation constructors encode that order, and a "right operand crashes
first" variant anywhere would give some formulas two distinct outcomes.

The circuit must correctly *reject* invalid computations, which now has a
target to match: the `Outcome.exit` arm of the relation.

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
