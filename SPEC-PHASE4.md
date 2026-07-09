# SPEC-PHASE4: dec Divergence and the Composition Theorem (Classes A & B)

**Status:** approved for implementation. Design decisions are final; if a
proof cannot close as specified, stop and report — do not redesign the
semantics or edit the normative tables to make a proof pass.

**Base:** the merged `outcome-refactor` tree (PR #1, commits a61ac2e +
f2f42c9). Toolchain Lean 4.28.0, no Mathlib, no new dependencies. All grep
gates from SPEC.md §8 remain in force and are re-checked at the end of every
phase.

---

## 0. Scope statement (what this work claims and does not claim)

Phase 4a mechanizes the **Nock side and the composition schema** of the
co-derivation pipeline. The C side is a **shallow model**: Lean functions
(`cw : Word → Noun → Outcome`) standing in for the C routines. The theorem
proved is "the compiled Nock formula agrees with the modeled semantics of the
C routine, for every word and every subject noun." The gap between the model
`cw` and any actual C implementation is deliberately **outside** this
development — it is the trusted base of the companion paper (Class C leaf
proofs and the harness contract). Do not add language to README or docstrings
claiming verified C, a verified compiler to C, or verified jets. The accurate
claim: *the composition schema is kernel-checked; the C routines are modeled,
not compiled.*

A second purpose of 4a is adversarial: **the paper's Tables A and B are on
trial.** The `phi` formulas below are transcribed verbatim from the
manuscript. If a leaf proof fails, the finding is that the *paper's table is
wrong* — report it (§5); never adjust `phi` to make a proof close.

---

## 1. Phase 3.5 — `dec` divergence on cell input

**Motivation.** Hoon's compiled `++dec` has a three-point ⊥ profile:
`atom (n+1) → .val (atom n)` (proved), `atom 0 → .exit` (proved), and
`cell → divergence` — the zero-guard passes (a cell ≠ `atom 0`), and the
count-up loop's test `=(a +(b))` compares a cell against an atom forever.
This phase proves the third point, completing the profile: the first
machine-checked statement of a Nock formula's full value/crash/divergence
behavior.

**New file:** `Nock/DecDiverges.lean`, importing `Nock.HoonOne` and
`Nock.Fuel`.

### 1.1 Sample-generalized loop infrastructure

The existing helpers (`decLoopCore`, `dec_cond_eval`, `dec_edit_core`) are
parametric in `n : Nat`. Do **not** modify them or the proofs that use them.
Add parallel generalized versions (the edit and slot lookups never inspect
the sample, so the proofs are near-identical):

```lean
/-- Loop core with an arbitrary noun in the sample slot (axis 30). -/
def decLoopCoreG (b : Nat) (sam ctx : Noun) : Noun :=
  cell decLoopBat (cell (atom b) (cell decBat (cell sam ctx)))

theorem decLoopCoreG_atom (b n : Nat) (ctx : Noun) :
    decLoopCoreG b (atom n) ctx = decLoopCore b n ctx := rfl

private theorem dec_cond_evalG (b : Nat) (sam ctx : Noun) :
    NockEval (decLoopCoreG b sam ctx)
      (cell (atom 5) (cell (cell (atom 0) (atom 30))
                           (cell (atom 4) (cell (atom 0) (atom 6)))))
      (.val (tisN sam (atom (1 + b))))
-- same proof shape as dec_cond_eval: op5 of (op0, axis 30) and (op4 of
-- (op0, axis 6), lusO_atom).

private theorem dec_slot6_evalG (b : Nat) (sam ctx : Noun) :
    NockEval (decLoopCoreG b sam ctx) (cell (atom 0) (atom 6)) (.val (atom b))

private theorem dec_edit_coreG (b : Nat) (sam ctx : Noun) :
    NockEval (decLoopCoreG b sam ctx)
      (cell (atom 10) (cell (cell (atom 6) (cell (atom 4) (cell (atom 0) (atom 6))))
                            (cell (atom 0) (atom 1))))
      (.val (decLoopCoreG (b + 1) sam ctx))
```

### 1.2 The key inequality

```lean
theorem tisN_cell_atom (x y : Noun) (m : Nat) :
    tisN (cell x y) (atom m) = atom 1 := by simp [tisN]
```

### 1.3 The loop lemma — derivation induction with index generalization

This is the technically novel proof of the phase. The statement must be
generalized over the counter **and stated as an implication from index
equalities**, because Lean's structural induction on an indexed derivation
only produces usable IHs when the indices are variables:

```lean
private theorem dec_loop_cell_aux (x y ctx : Noun) :
    ∀ {s f o}, NockEval s f o →
      ∀ b, s = decLoopCoreG b (cell x y) ctx → f = decLoopBat → False := by
  intro s f o h
  induction h with
  ...
```

Recipe for the cases (all others are dismissed by formula-shape mismatch —
substituting `f = decLoopBat`, whose head is `atom 6`, contradicts every
constructor whose formula index has a different head; `crash_malformed` is
dismissed because `Malformed decLoopBat = false` closes by `decide` on the
concrete literal — `decide`, not `rfl`, per the WF-recursion trap):

- **`op6_then`**: hypothesis says the test derived `.val (atom 0)`. Construct
  the canonical test derivation
  `dec_cond_evalG b (cell x y) ctx : ... (.val (tisN (cell x y) (atom (1+b))))`,
  rewrite with `tisN_cell_atom` to get `.val (atom 1)`, apply
  `NockEval.deterministic` against the hypothesis, contradiction by
  `Outcome.val` injectivity (`simp` closes it).
- **`op6_nonloob`**: same construction; determinism forces `r = atom 1`,
  contradicting the constructor's `r ≠ atom 1` hypothesis.
- **`op6_crash`**: test derived `.exit`; determinism against the `.val`
  construction, contradiction.
- **`op6_else`** — the live case. The else-branch sub-derivation targets the
  recursion arm `[9 2 [10 [6 [4 0 6]] [0 1]]]`. `cases` on it:
  - **`op9`**: its core sub-derivation targets the op10 edit formula.
    Determinism against `dec_edit_coreG b` forces
    `core = decLoopCoreG (b+1) (cell x y) ctx`; the `fasO (atom 2) core`
    hypothesis rewrites (via `fasO_head`) to `some decLoopBat`; injectivity
    gives the arm = `decLoopBat`; the arm sub-derivation now has exactly the
    generalized indices at `b + 1` — apply the induction hypothesis with
    `b + 1`, `rfl`, `rfl`.
  - **`op9_badaxis`**: determinism forces the core as above;
    `fasO (atom 2) (decLoopCoreG ...) = some decLoopBat` (by `fasO_head`)
    contradicts the `= none` hypothesis.
  - **`op9_crash`**: the edit sub-derivation derived `.exit`; determinism
    against `dec_edit_coreG`, contradiction.
  - remaining constructors: formula-shape mismatch.

**Pitfall (normative):** before `induction h`, the equalities must be *taken
as hypotheses*, not substituted — that is the entire reason for the
`∀ b, s = _ → f = _ → False` phrasing. In each case, `subst`/`injection` the
equalities *after* the case split. If the implementer instead states the
lemma with concrete indices and tries `induction`, Lean will reject the
motive or produce useless IHs; that is not a semantic problem, it is the
signal to return to this recipe.

### 1.4 The theorems

```lean
theorem dec_loop_cell_diverges (b : Nat) (x y ctx : Noun) :
    Diverges (decLoopCoreG b (cell x y) ctx) decLoopBat :=
  fun o h => dec_loop_cell_aux x y ctx h b rfl rfl

theorem dec_cell_diverges (x y ctx : Noun) :
    Diverges (cell decBat (cell (cell x y) ctx)) decBat
```

For `dec_cell_diverges`: intro `o h`, unfold `decBat` with the same `show`
trick as `dec_correct`/`dec_underflow`, then invert the derivation layer by
layer, pruning with determinism at each step exactly as in §1.3:

1. `cases h` — only `op11_dynamic` / `op11_dyn_crash` / `crash_malformed`
   match the formula head. `crash_malformed`: `decide`. `op11_dyn_crash`: the
   hint computation derived `.exit`; the existing `dec_hint_eval` (HoonOne)
   provides a `.val` derivation on this subject — determinism, contradiction.
2. In `op11_dynamic`: the tail derivation targets `decBat_guardBody`
   (rewrite with `guardBody_parts`). `cases`: guard test evaluates to
   `.val (tisN (atom 0) (cell x y))` = `.val (atom 1)` by construction (op5
   of op1 and the axis-6 slot; `tisN` on unequal nouns — add
   `tisN_atom_cell : tisN (atom m) (cell x y) = atom 1` alongside §1.2).
   Prune `op6_then`/`op6_nonloob`/`op6_crash` by determinism; `op6_else`
   survives.
3. The else branch is `decBat_pushLoop` (rewrite with `pushLoop_parts`); two
   `op8` layers — in each, the pushed formula is `[1 _]`, whose only
   derivations are `op1` (`.val`) and none crashing, so `op8_crash` cases are
   pruned by determinism against `op1`; after both pushes the subject is
   `decLoopCoreG 0 (cell x y) ctx` **definitionally** (verify with a `show`).
4. The final layer is `[9 2 [0 1]]`: `op9` gives (via `fasO_one`,
   determinism) the loop core and `fasO_head` the loop battery; the arm
   sub-derivation contradicts `dec_loop_cell_diverges 0`. `op9_badaxis` /
   `op9_crash` pruned as in §1.3.

### 1.5 Acceptance (Phase 3.5)

- `dec_cell_diverges` and `dec_loop_cell_diverges` proved, no `sorry`.
- `#print axioms dec_cell_diverges` ⊆ {propext, Quot.sound,
  Classical.choice}.
- Existing theorems untouched (no edits to `HoonOne.lean` proofs; new
  lemmas may be added to `Proofs.lean`/`HoonOne.lean` but nothing removed
  or restated).
- README gains one line in the dec section: the complete ⊥ profile
  (value / %exit / divergence) is now machine-checked.

---

## 2. Phase 4a — Words, leaf contracts, and the composition theorem

**New file:** `Nock/Comp.lean`, importing `Nock.Eval`, `Nock.Proofs`,
`Nock.Fuel`.

### 2.1 The word set

```lean
inductive Word
  | dup | drop | swap | over | cons | head | tail   -- Class A
  | inc | eq | celq                                  -- Class B  (celq = cel?)
  deriving DecidableEq, Repr
```

### 2.2 Nock formulas — NORMATIVE, transcribed from the paper's tables

Stack convention: the subject is the stack, `S = [top rest]`; in the effect
notation `( a b — ... )` the **rightmost element is the top**.

```lean
def phi : Word → Noun
  | .dup  => cell (cell (atom 0) (atom 2)) (cell (atom 0) (atom 1))
      -- [[0 2] 0 1]        ( a — a a )
  | .drop => cell (atom 0) (atom 3)
      -- [0 3]              ( a — )
  | .swap => cell (cell (atom 0) (atom 6))
                  (cell (cell (atom 0) (atom 2)) (cell (atom 0) (atom 7)))
      -- [[0 6] [0 2] 0 7]  ( a b — b a )
  | .over => cell (cell (atom 0) (atom 6)) (cell (atom 0) (atom 1))
      -- [[0 6] 0 1]        ( a b — a b a )
  | .cons => cell (cell (cell (atom 0) (atom 6)) (cell (atom 0) (atom 2)))
                  (cell (atom 0) (atom 7))
      -- [[[0 6] 0 2] 0 7]  ( h t — [h t] )
  | .head => cell (cell (atom 0) (atom 4)) (cell (atom 0) (atom 3))
      -- [[0 4] 0 3]        ( c — h )
  | .tail => cell (cell (atom 0) (atom 5)) (cell (atom 0) (atom 3))
      -- [[0 5] 0 3]        ( c — t )
  | .inc  => cell (cell (atom 4) (cell (atom 0) (atom 2)))
                  (cell (atom 0) (atom 3))
      -- [[4 0 2] 0 3]      ( a — a+1 )
  | .eq   => cell (cell (atom 5) (cell (cell (atom 0) (atom 6))
                                       (cell (atom 0) (atom 2))))
                  (cell (atom 0) (atom 7))
      -- [[5 [0 6] 0 2] 0 7]  ( a b — ? )
  | .celq => cell (cell (atom 3) (cell (atom 0) (atom 2)))
                  (cell (atom 0) (atom 3))
      -- [[3 0 2] 0 3]      ( a — ? )
```

**Do not edit these.** If a leaf proof fails, follow §5.

### 2.3 The shallow C model — NORMATIVE

Total over **all** nouns; the crash cases below *are* the ⊥-domain column of
the paper's tables, now stated over arbitrary nouns rather than relative to a
stack invariant. Argument-order note: in `eq`, the formula evaluates
`[0 6]` first, so the model must be `tisN a b` (deeper element first), not
`tisN b a` — `tisN` is symmetric in value but the leaf proof closes
definitionally only in this order.

```lean
def cw : Word → Noun → Outcome
  | .dup,  cell a r                  => .val (cell a (cell a r))
  | .dup,  atom _                    => .exit
  | .drop, cell _ r                  => .val r
  | .drop, atom _                    => .exit
  | .swap, cell b (cell a r)         => .val (cell a (cell b r))
  | .swap, cell _ (atom _)           => .exit
  | .swap, atom _                    => .exit
  | .over, cell b (cell a r)         => .val (cell a (cell b (cell a r)))
  | .over, cell _ (atom _)           => .exit
  | .over, atom _                    => .exit
  | .cons, cell t (cell h r)         => .val (cell (cell h t) r)
  | .cons, cell _ (atom _)           => .exit
  | .cons, atom _                    => .exit
  | .head, cell (cell h _) r         => .val (cell h r)
  | .head, cell (atom _) _           => .exit
  | .head, atom _                    => .exit
  | .tail, cell (cell _ t) r         => .val (cell t r)
  | .tail, cell (atom _) _           => .exit
  | .tail, atom _                    => .exit
  | .inc,  cell (atom n) r           => .val (cell (atom (1 + n)) r)
  | .inc,  cell (cell _ _) _         => .exit
  | .inc,  atom _                    => .exit
  | .eq,   cell b (cell a r)         => .val (cell (tisN a b) r)
  | .eq,   cell _ (atom _)           => .exit
  | .eq,   atom _                    => .exit
  | .celq, cell a r                  => .val (cell (wut a) r)
  | .celq, atom _                    => .exit
```

### 2.4 fasO crash-lemma library

Add to `Nock/Proofs.lean` (batch of one-liners, each by `simp [fasO]` —
never `rfl`, per the well-founded-recursion trap):

```lean
theorem fasO_two_atom   (n : Nat) : fasO (atom 2) (atom n) = none
theorem fasO_three_atom (n : Nat) : fasO (atom 3) (atom n) = none
theorem fasO_four_atom  (n : Nat) : fasO (atom 4) (atom n) = none
theorem fasO_four_atomhead (m : Nat) (r : Noun) :
    fasO (atom 4) (cell (atom m) r) = none
theorem fasO_five_atom  (n : Nat) : fasO (atom 5) (atom n) = none
theorem fasO_five_atomhead (m : Nat) (r : Noun) :
    fasO (atom 5) (cell (atom m) r) = none
theorem fasO_six_atom   (n : Nat) : fasO (atom 6) (atom n) = none
theorem fasO_six_atomtail (x : Noun) (t : Nat) :
    fasO (atom 6) (cell x (atom t)) = none
theorem fasO_seven_atom (n : Nat) : fasO (atom 7) (atom n) = none
theorem fasO_seven_atomtail (x : Noun) (t : Nat) :
    fasO (atom 7) (cell x (atom t)) = none
```

### 2.5 Leaf theorems

One strong statement per word — value clause, crash clause, and (with
`NockEval.deterministic`) exclusivity, all at once:

```lean
theorem leaf_correct (w : Word) (S : Noun) : NockEval S (phi w) (cw w S)
```

Proof: `cases w <;> cases S` (and inner `cases` mirroring `cw`'s match
tree exactly). Value cases assemble constructors with the named `fasO_*`
lemmas (e.g. `dup` on `cell a r`:
`NockEval.autocons (NockEval.op0 (fasO_head a r)) (NockEval.op0 (fasO_one _))`).
Crash cases use `autocons_crashL`/`autocons_crashR`/`op0_crash`/`op4_cell`
with the §2.4 library. Implement as ten named `private` lemmas
(`leaf_dup`, `leaf_drop`, ...) dispatched by a top-level `cases w`, so a
single failing word is isolated for the §5 report.

### 2.6 The compilers and the composition theorem

```lean
abbrev Prog := List Word

def N : Prog → Noun
  | []     => cell (atom 0) (atom 1)                    -- [0 1]
  | w :: p => cell (atom 7) (cell (phi w) (N p))        -- [7 φ_w N(p)]

def Csem : Prog → Noun → Outcome
  | [],     S => .val S
  | w :: p, S =>
    match cw w S with
    | .val S' => Csem p S'
    | .exit   => .exit
```

Explicit `match`, no `Outcome.bind` instance — consistent with `nockF` and
keeps the induction syntactic.

```lean
theorem composition (p : Prog) (S : Noun) : NockEval S (N p) (Csem p S) := by
  induction p generalizing S with
  | nil => exact NockEval.op0 (fasO_one S)
  | cons w p ih =>
    simp only [N, Csem]
    cases hcw : cw w S with
    | val S' =>
      exact NockEval.op7 (hcw ▸ leaf_correct w S) (by rw [hcw] at *; exact ih S')
    | exit =>
      exact NockEval.op7_crash (hcw ▸ leaf_correct w S)

theorem composition_agree (p : Prog) (S : Noun) {o : Outcome}
    (h : NockEval S (N p) o) : o = Csem p S :=
  NockEval.deterministic h (composition p S)
```

(The tactic details in `cons` are indicative, not normative — any proof of
the stated theorems is acceptable. The *statements* are normative.)

### 2.7 Sanity examples (required, in `Comp.lean`)

```lean
-- "dup inc": duplicate then increment the copy — [n r] → [n+1 [n r]]
example (n : Nat) (r : Noun) :
    NockEval (cell (atom n) r) (N [.dup, .inc])
             (.val (cell (atom (1 + n)) (cell (atom n) r))) := ...
-- crash hides the tail: swap on a depth-1 stack, composed with drop
example (n : Nat) :
    NockEval (cell (atom n) (atom 0)) (N [.swap, .drop]) .exit := ...
```

Both should be `composition_agree`-driven or direct — implementer's choice.

### 2.8 Acceptance (Phase 4a)

- `leaf_correct` (all ten), `composition`, `composition_agree`, both sanity
  examples: proved, no `sorry`.
- `#print axioms composition` ⊆ {propext, Quot.sound, Classical.choice}.
- Grep gates hold tree-wide.
- `TABLE-REPORT.md` produced per §5, even if empty of discrepancies.

---

## 3. Phase 4b — DO NOT START

Class C leaf wiring (guarded-dec as a `Word`, the gate-convention shim),
Class D (`ifte`/`while`, the term algebra, fixpoint schema), and any
`CEval`-style non-total C model are Phase 4b and require a design review
first. In particular: the Class C `dec` leaf uses the **Λ-emitted guarded
formula** (cell → `.exit`), *not* Hoon's `decBat` (cell → divergence, per
Phase 3.5). These are different formulas with different ⊥ profiles; keep
them as distinct definitions and do not "unify" them.

---

## 4. Pitfalls

- **WF-recursion does not reduce under `rfl`.** `fasO`/`haxO` proofs go
  through `simp [fasO]`/`simp [haxO]` or the named lemma library. `Malformed`
  on concrete formulas closes by `decide`.
- **Never** `.get!`, `panic!`, `default`, or `Option.get!` in proof-facing
  code (SPEC.md §7 stands).
- The §1.3 index-generalization phrasing is load-bearing; do not "simplify"
  the aux lemma to concrete indices.
- `cw`'s match tree is the case tree of every leaf proof — implement it
  exactly as written so the proofs mirror it.
- Determinism-pruning pattern throughout: construct the canonical
  derivation, `NockEval.deterministic`, `injection`/`simp`. This appears
  ~15 times in Phase 3.5; factor a `have`-block idiom, not a new tactic.

## 5. Table-trial reporting protocol

If any `phi w` fails its leaf proof: (1) do **not** modify `phi`; (2) find
the smallest counterexample subject `S` and the outcome each side actually
takes (`nockF` with generous fuel on the formula; `cw` by computation);
(3) record in `TABLE-REPORT.md`: word, paper formula, expected vs. actual,
counterexample, and — only as a *proposal* — the corrected formula with its
own leaf proof in a clearly marked section. The paper's table is corrected
by the humans, not by the artifact. If all ten prove as stated,
`TABLE-REPORT.md` says so in one line; that sentence goes in the paper.

## 6. Definition of done

1. `lake build` clean on 4.28.0 from a scrubbed `.lake/build`; no `sorry`;
   no new axiom declarations.
2. Grep gates: `panic` only in `partial def nock`; `native_decide` code
   only in `Nock/RuntimeBridge.lean`.
3. Phase 3.5: `dec_cell_diverges` proved; axiom footprint reported.
4. Phase 4a: ten leaf theorems + `composition` + `composition_agree` +
   sanity examples proved; axiom footprints reported.
5. `TABLE-REPORT.md` present.
6. README: dec ⊥-profile line (§1.5); a Composition section stating the
   §0 scope boundary in exactly its terms (schema kernel-checked, C modeled).
