# SPEC-PHASE4B-PROOFS: The Term-Algebra Composition Theorem

**Status:** approved for implementation. Marking scheme per protocol: every
instruction is tagged **NORMATIVE** (deviations halt, except
motive-strengthening, which proceeds with a flag and site documentation) or
**GUIDANCE** (implementer's craft; restructure freely, keep the stated
theorem statements). Public theorem *statements* are NORMATIVE everywhere.
The deviation axis stands: strengthening a motive cannot make a false
theorem provable — proceed and flag; weakening can — halt.

**Base:** master after PR #4. Toolchain 4.28.0, no Mathlib, all grep gates
in force.

**What this phase proves:** the paper's Class D composition claim as a
kernel-checked biconditional — `NockEval S (NT t) o ↔ CEval t S o` over the
full term algebra, plus its divergence corollary. This upgrades the Class D
schemas from confirmed (oracle, 676/676) to discharged (kernel).

---

## 0. Architecture ruling (read first — it explains everything below)

Two induction traps were live in this design, and the architecture is
chosen to make both structurally impossible:

1. **Forward** (`CEval → NockEval`): the naive induction's while case needs
   the L-refire derivation, which is *not* recoverable from the IH's
   conclusion without deep inversion. Fix: strengthen the motive with a
   second conjunct carrying the loop-level fact, so the recursion site is an
   *immediate* sub-derivation. (Same class of fix as the SPEC-PHASE4 §1.3
   correction — this time it is in the spec, not discovered against it.)
2. **Backward** (`NockEval → CEval`): derivation induction here would need
   IHs at nested inversion depth — the §1.3 trap exactly. `NockEval` is
   Prop-valued, so no height measure exists on derivations. Fix: **do not
   induct on the derivation at all.** Convert it to fuel via
   `nockF_complete` and induct on the fuel, which measures *every* nested
   recursion uniformly. Phase 2's interpreter was built as a determinism
   corollary machine; here it becomes the induction measure for the
   simulation. `nockF` is proof-chain-legal (it always was — the quarantine
   governs `CsemF`, the C-side oracle, not `nockF`).

Consequences: **no mutual inductives, no unfold-lemma library, no
"compiled formulas are recognizable" lemma.** All three were candidate
designs; all three are superseded. Do not introduce them.

---

## 1. Migration and naming — NORMATIVE

New file `Nock/Term.lean`: `Term`, the term compiler, `Nifte`, `Nwhile`,
`Lwhile` move here from `Nock/Oracle.lean`, verbatim per DEFENDANT-CLASSD
§1–§2 (they are oracle-acquitted; no edits). `Oracle.lean` then imports
`Nock.Term` and deletes its private copies; the quarantine direction is
unchanged (nothing in the proof chain imports Oracle — grep gate).

Naming: the term compiler is **`NT : Term → Noun`**. The existing
`N : Prog → Noun` in `Comp.lean` is frozen (public statements are API);
do not rename, do not touch its theorems. A docstring on `NT` maps it to
the paper's `Λ_N`/`N` over the term algebra.

Embedding (in `Term.lean`):

```lean
def Term.ofProg (p : Prog) : Term := p.foldr .seq .nil
theorem NT_ofProg (p : Prog) : NT (Term.ofProg p) = N p   -- induction on p
```

## 2. `CEval` — NORMATIVE, verbatim

New file `Nock/CEval.lean`. Big-step, divergence by absence, left-to-right
strict, transcribing the manuscript's C listings. Fifteen constructors;
implement exactly:

```lean
inductive CEval : Term → Noun → Outcome → Prop where
  | nil {S} : CEval .nil S (.val S)

  | seq {w p S S' o} :
      cw w S = .val S' → CEval p S' o → CEval (.seq w p) S o
  | seq_crash {w p S} :
      cw w S = .exit → CEval (.seq w p) S .exit

  -- ifte: flag on top (in the subject index), consumed; branch on the
  -- remainder; the branch's exit stack feeds the continuation
  | ifte_then {q₁ q₂ p r T o} :
      CEval q₁ r (.val T) → CEval p T o →
      CEval (.ifte q₁ q₂ p) (cell (atom 0) r) o
  | ifte_then_crash {q₁ q₂ p r} :
      CEval q₁ r .exit → CEval (.ifte q₁ q₂ p) (cell (atom 0) r) .exit
  | ifte_else {q₁ q₂ p r T o} :
      CEval q₂ r (.val T) → CEval p T o →
      CEval (.ifte q₁ q₂ p) (cell (atom 1) r) o
  | ifte_else_crash {q₁ q₂ p r} :
      CEval q₂ r .exit → CEval (.ifte q₁ q₂ p) (cell (atom 1) r) .exit
  | ifte_nonloob {q₁ q₂ p f r} :
      f ≠ atom 0 → f ≠ atom 1 →
      CEval (.ifte q₁ q₂ p) (cell f r) .exit
  | ifte_atom {q₁ q₂ p n} :
      CEval (.ifte q₁ q₂ p) (atom n) .exit

  -- while: self-recursive on the same term index; test maps S to
  -- [flag S']; 0 → body then re-enter, 1 → exit stack feeds continuation
  | while_step {t b p S S' S'' o} :
      CEval t S (.val (cell (atom 0) S')) →
      CEval b S' (.val S'') →
      CEval (.while t b p) S'' o →
      CEval (.while t b p) S o
  | while_exit {t b p S S' o} :
      CEval t S (.val (cell (atom 1) S')) →
      CEval p S' o →
      CEval (.while t b p) S o
  | while_test_crash {t b p S} :
      CEval t S .exit → CEval (.while t b p) S .exit
  | while_body_crash {t b p S S'} :
      CEval t S (.val (cell (atom 0) S')) → CEval b S' .exit →
      CEval (.while t b p) S .exit
  | while_flag_atom {t b p S n} :
      CEval t S (.val (atom n)) → CEval (.while t b p) S .exit
  | while_nonloob {t b p S f S'} :
      CEval t S (.val (cell f S')) → f ≠ atom 0 → f ≠ atom 1 →
      CEval (.while t b p) S .exit
```

Notes fixing intent: the flag lives in the *subject index* for ifte
(mirroring how the C `pop` reads it) and in the *test's derived value* for
while (mirroring `p_t`'s output). An infinite loop has no finite
`while_step` chain, hence no derivation — divergence by absence, both
sides. Non-loobean means anything other than `atom 0`/`atom 1`; a cell
flag and `atom n, n ≥ 2` both land in `ifte_nonloob`/`while_nonloob`.

## 3. Forward direction — statement NORMATIVE, recipe GUIDANCE

```lean
theorem ceval_sound_aux {t S o} (h : CEval t S o) :
    NockEval S (NT t) o ∧
    (∀ t' b' p, t = .while t' b' p →
      ∃ oL, NockEval (cell (Lwhile t' b') S) (Lwhile t' b') oL ∧
        ((oL = .exit ∧ o = .exit) ∨
         (∃ E, oL = .val E ∧ NockEval E (NT p) o)))

theorem ceval_sound {t S o} (h : CEval t S o) : NockEval S (NT t) o :=
  (ceval_sound_aux h).1
```

The second conjunct is the loop-level fact: the L-firing's own outcome
`oL`, plus its link to the composite outcome `o` through the continuation.
**NORMATIVE: do not drop or weaken it** — it is what makes `while_step`'s
recursion an immediate-IH use. Recipe (GUIDANCE): induction on `h`.

- `while_step`: IH₃'s conjunct 2 (at `S''`, via `rfl`) supplies the inner
  L-derivation and link. Assemble the L-firing at `S` by constructor
  application only: inner op8 pins `[7 [0 3] NT t']` (op7 of `op0
  fasO_tail`-shaped slot 3, then IH₁.1); the subject is now
  `[[flag S'] L S]` — flag via `fasO_four`, `S'` via `fasO_five`, `L` via
  `fasO_six` (all on `cell (cell _ _) _` shapes; the lemmas exist);
  continue branch: op9 whose core-formula is the autocons of `[0 6]` and
  `[7 [0 5] NT b']` (IH₂.1), core `[L S'']`, arm via `fasO_head`, arm
  derivation = IH₃'s `oL`-derivation. Same `oL`, same link. Conjunct 1
  then wraps: op8/op1, op9/`fasO_one`/`fasO_head`, and op7 discharging the
  link (op7 in the value case, op7_crash in the exit case).
- `while_exit`: no self-recursion; the exit branch is `[0 5]` (`fasO_five`),
  `oL = .val S'`, link right disjunct with IH₂.1 as the continuation.
- while crash constructors: `oL = .exit` through the corresponding crash
  path (`op6_crash` for test-crash; body-crash rides `autocons_crashR`
  into `op9_crash`; flag-atom is `fasO 4` failing → `op0_crash` →
  `op6_crash`; nonloob is `op6_nonloob`).
- ifte cases: conjunct 2 vacuous. `cases` already fixed the subject shape;
  assemble op7 over `Nifte` — test `[0 2]` via `fasO_head`
  (`ifte_atom`: `fasO_two_atom` → `op0_crash` → `op6_crash` → `op7_crash`),
  branch pre-compose `[0 3]` via `fasO_tail`, then IHs.
- `nil`/`seq`: exactly the Phase 4a composition proof, one term-level.

## 4. Backward direction — statements NORMATIVE, recipe GUIDANCE

```lean
def LoopBack (t b : Term) (S : Noun) (o : Outcome) : Prop :=
  ∀ p : Term,
    (o = .exit → CEval (.while t b p) S .exit) ∧
    (∀ E, o = .val E → ∀ {o'}, CEval p E o' → CEval (.while t b p) S o')

theorem backward_fuel : ∀ k : Nat,
    (∀ {t : Term} {S o}, nockF k S (NT t) = some o → CEval t S o) ∧
    (∀ {t b : Term} {S o},
       nockF k (cell (Lwhile t b) S) (Lwhile t b) = some o →
       LoopBack t b S o)

theorem nockeval_complete {t : Term} {S o}
    (h : NockEval S (NT t) o) : CEval t S o :=
  let ⟨k, hk⟩ := nockF_complete h
  (backward_fuel k).1 hk
```

`LoopBack` packages the loop outcome parametrically over continuations —
`o` here is the *L-firing's* outcome; the two clauses discharge it into
`while_*` constructors for any `p`. Packaging is GUIDANCE (a sum-typed
conclusion is acceptable); the two-part `backward_fuel` shape is
NORMATIVE — it is the anti-§1.3 device: every recursive obligation (a
term-level call inside a schema, or the L-refire) appears in `nockF`'s
computation at strictly smaller fuel, so strong induction on `k` supplies
every IH at every nesting depth, uniformly. Do not flatten to the
term-only half; the L-refire is not term-shaped.

Recipe (GUIDANCE): strong induction on `k`
(`Nat.strong_induction_on` or structural with `nockF_mono` where offsets
disagree). `k = 0` is vacuous (`nockF 0 = none`). At `k+1`: for the term
half, `cases t`; unfold `nockF` one layer at a time with
`simp only [nockF]` and case each recursive result via
`match h' : nockF … with` — the schema spines are concrete, so the
`Malformed` checks and `fasO` lookups inside `nockF` reduce (`decide` /
the named lemmas; never `rfl` on the WF-recursive `fasO`). Each surviving
branch hands you recursive `nockF` facts at smaller fuel: term-shaped ones
go to the IH's first half, `Lwhile`-shaped ones to its second, and the
results assemble into `CEval` constructors (subject-indexed ifte
constructors want `cases S` early). For the loop half, the L spine
unfolds to: test at term fuel (IH half 1), flag three-way case
(`while_flag_atom` / `while_nonloob` / loobean split), exit via `[0 5]`
(populate `LoopBack`'s value clause with `while_exit`), continue via body
(IH half 1) then L-refire (IH half 2 at smaller fuel; compose
`LoopBack`s with `while_step`). Do not compute exact fuel offsets as
constants; carry them as hypotheses and let `omega` close the ordering
obligations.

## 5. Determinism and the headline theorems — NORMATIVE

```lean
theorem ceval_det {t S o₁ o₂} (h₁ : CEval t S o₁) (h₂ : CEval t S o₂) :
    o₁ = o₂ :=
  NockEval.deterministic (ceval_sound h₁) (ceval_sound h₂)
```

Transfer only — **do not prove `CEval` determinism directly** (a direct
proof is a 15×15 case bash the architecture exists to avoid).

```lean
theorem composition_term (t : Term) (S : Noun) (o : Outcome) :
    NockEval S (NT t) o ↔ CEval t S o :=
  ⟨nockeval_complete, ceval_sound⟩

def CDiverges (t : Term) (S : Noun) : Prop := ∀ o, ¬ CEval t S o

theorem composition_diverges (t : Term) (S : Noun) :
    Diverges S (NT t) ↔ CDiverges t S
```

`composition_diverges` is the paper's "equal least fixed points" made
literal: agreement on values, on crashes, *and on divergence*, as a
biconditional. It follows from `composition_term` by contraposition on
both sides — one-liner, but it is the sentence the manuscript's Class D
proof-burden paragraph gets to cite, so it gets its own name.

Embedding compatibility (GUIDANCE on proof, NORMATIVE on statements):

```lean
theorem ceval_ofProg (p : Prog) (S : Noun) :
    CEval (Term.ofProg p) S (Csem p S)         -- induction on p
theorem composition_ofProg (p : Prog) (S : Noun) {o}
    (h : NockEval S (N p) o) : o = Csem p S    -- via NT_ofProg + transfer
```

The second must be derivable from the new machinery and must agree with
the frozen Phase 4a `composition_agree` — it is the regression check that
the term algebra conservatively extends the monoid.

## 6. Out of scope — DO NOT START

Class C beyond dec (`add`/`sub`/`mul` guarded formulas are new defendants;
the humans supply them from the manuscript pipeline). Verified
`CsemF`-vs-`CEval` agreement (puts fuel adjacent to the C model; the
oracle's role is empirical by design). `%fast` hint wrapping in `NT`.
Any Hoon-subset front end.

## 7. Audit and reporting

Manifest additions (all target `[propext, Quot.sound]`;
`Classical.choice` tolerated only with documented inheritance):
`ceval_sound`, `nockeval_complete`, `composition_term`,
`composition_diverges`, `ceval_det`, `NT_ofProg`, `ceval_ofProg`,
`composition_ofProg`.

On completion: TABLE-REPORT's claim-gradient table upgrades Class D from
*confirmed (oracle)* to *discharged (kernel)*, citing `composition_term`
and `composition_diverges`; the manuscript's "mechanized proof is in
progress" sentence is flagged for the humans to upgrade. Raw report
format as standing: footprints, gates, and any deviation flags before
interpretation.

## 8. Pitfalls

- The two strengthened motives (§3 conjunct 2, §4 two-part statement) are
  the anti-§1.3 devices. Every recursion in this design is either an
  immediate sub-derivation or a smaller fuel — if you find yourself
  needing an IH you don't have, the design is being departed from, not
  refined; stop and re-read §0.
- `nockF` unfolding discipline: one layer per `simp only [nockF]`, name
  every recursive result with `match h' : …`, close fuel-order side goals
  with `omega`, never chase concrete offsets.
- `fasO`/`haxO` never reduce by `rfl`; `Malformed` on concrete schema
  heads does reduce (`decide`), including heads with term-dependent tails
  (the match inspects only the head).
- `cases S` before working ifte cases; the constructors are
  subject-indexed by design.
- `Csem`/`cw` are total functions — `cases hcw : cw w S` style from
  Phase 4a carries over to the `seq` cases unchanged.
