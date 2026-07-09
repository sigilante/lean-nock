# SPEC-PHASE4B-STATEMENTS: guarded `dec` and the gate shim

**Status:** definitions and theorem statements only — no proof recipes. Per the
Phase 4a ruling: public theorem statements, the relation, and the normative
tables move only with your approval; private proof machinery is mine, provided
a fix *strengthens* and is documented at the site.

**Scope.** Class C leaf (`dec`) and the gate shim. The Class D term algebra
(`ifte`/`while`) and the `CEval` relation are deferred to
SPEC-PHASE4B-CLASSD, to be drafted *after* the `while` oracle trial (§6).

**Quarantine invariant.** Not disjoint imports — **import direction**. The
oracle module legitimately imports `Word`, `phi`, `cw`; the proofs do too. The
invariant is that **nothing in the proof chain imports the oracle**, ever. Same
discipline as `Nock/RuntimeBridge.lean`, same grep gate.

**Naming, ruled.** `mkGate` is the gate *core* constructor; `liftGate` is the
*formula* that calls a gate from a stack. Names are API from this point.

---

## 1. The defendant: Table C's `dec` row, as printed

Transcribed verbatim, never edited. **Refuted by oracle** — see §5 and
`TABLE-REPORT.md` §C.

```
guarded-dec  =  [6 [3 0 2] [0 0] [6 [5 [1 0] 0 2] [0 0] <count-up>]]
φ_dec        =  [[7 [0 2] <guarded-dec>] 0 3]
<count-up>   =  [8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] [9 2 [0 2] [4 0 6] 0 7]] 9 2 0 1]
```

The listing admits two readings — the guards' axis `2` is consistent with
either — and **both fail on the entire valid domain**:

| reading | guards see | `<count-up>` sees | failure |
| --- | --- | --- | --- |
| **A** (per the lift footnote) | the bare atom | the bare atom ✓ | `[3 0 2]` takes axis 2 of an atom → **every valid input crashes**; and on a cell top the guard reads the cell's *head*, passes, and the loop **diverges** |
| **B** (guards on the stack) | the stack ✓ | the stack | axis 7 is the whole stack `[a r]`, a cell the counter never equals → **every valid input diverges** |

Reading A additionally destroys crash-totality, so the printed `φ_dec` is not
denotable as a `Word` at all — excluded by `not_denotable_of_diverges` (§3),
which is the very theorem the guard-emission rule exists to enforce. *The guard
meant to reject cells is the reason the cell is accepted.*

## 2. The correction — NORMATIVE, adopted

Keep the lift and `<count-up>` exactly as printed; move the two guards from
axis 2 to axis 1, so they read the subject guarded-dec actually receives.

```lean
/-- Canonical count-up, verbatim from the manuscript.  Core is `[bat [b a]]`:
    axis 2 = battery, 6 = counter, 7 = the argument.  Built for a BARE ATOM. -/
def countUp : Noun :=
  n! "[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] [9 2 [0 2] [4 0 6] 0 7]] 9 2 0 1]"

/-- Λ-emitted domain guards, corrected to axis 1.

      [6 [3 0 1]           -- ?subject : 0 when the argument is a cell
         [0 0]             --   then: crash
         [6 [5 [1 0] 0 1]  -- =(0 subject)
            [0 0]          --   then: crash (underflow)
            <count-up>]]   --   else: count up on a genuine bare atom
-/
def decGuarded : Noun :=
  cell (atom 6) (cell (n! "[3 0 1]")
    (cell (n! "[0 0]")
      (cell (atom 6) (cell (n! "[5 [1 0] 0 1]") (cell (n! "[0 0]") countUp)))))

/-- Lift a unary atom operation to a stack word: run `g` on the top, cons the
    result back onto the rest.  This is the manuscript's lift, unchanged.

    The depth guard is free: on a bare-atom stack `fasO (atom 2) (atom _) = none`,
    so `op7`'s left operand crashes. -/
def liftUnary (g : Noun) : Noun :=
  cell (cell (atom 7) (cell (cell (atom 0) (atom 2)) g)) (cell (atom 0) (atom 3))
```

`Word` gains one constructor; `phi` and `cw` gain one arm each.

```lean
inductive Word
  | dup | drop | swap | over | cons | head | tail   -- Class A
  | inc | eq | celq                                 -- Class B
  | dec                                             -- Class C   ← new
  deriving DecidableEq, Repr

def phi : Word → Noun
  | ...
  | .dec => liftUnary decGuarded

/-- Table C row for `dec`.  NORMATIVE — do not edit to fit a proof. -/
def cw : Word → Noun → Outcome
  | ...
  | .dec, atom _              => .exit                     -- depth < 1
  | .dec, cell (atom 0) _     => .exit                     -- underflow
  | .dec, cell (cell _ _) _   => .exit                     -- cell argument
  | .dec, cell (atom (n+1)) r => .val (cell (atom n) r)
```

## 3. Guarded `dec` — theorem statements

**No new theorem statement is required.** Adding a Class C word widens `Word`;
`leaf_correct`, `composition`, and `composition_agree` are unchanged and now
quantify over eleven words instead of ten. That is the whole content of the
guard-emission rule being a type-level invariant rather than a side condition.

```lean
theorem leaf_correct (w : Word) (S : Noun) : NockEval S (phi w) (cw w S)
```

Two free corollaries, checked to compile against the Phase 4a tree
(`#print axioms` → `[propext, Quot.sound]` for both):

```lean
/-- Every `Word` denotes a crash-total formula: `leaf_correct` supplies a
    derivation at *every* subject, so no subject diverges. -/
theorem word_crash_total (w : Word) (S : Noun) : ¬ Diverges S (phi w) :=
  fun hd => hd _ (leaf_correct w S)

/-- Hence a formula that diverges anywhere is not denotable as a `Word`. -/
theorem not_denotable_of_diverges {f S : Noun} (hd : Diverges S f) :
    ¬ ∃ w : Word, phi w = f
```

## 4. The gate shim

```lean
/-- A Hoon gate core: `[battery [sample context]]`. -/
def mkGate (bat sam ctx : Noun) : Noun := cell bat (cell sam ctx)

/-- Lift a gate to a stack word.  On `S = [a rest]`: build `[bat [a ctx]]`,
    fire arm 2, cons the result onto `rest`.

      [[9 2 [[1 bat] [[0 2] [1 ctx]]]] [0 3]] -/
def liftGate (bat ctx : Noun) : Noun :=
  cell (cell (atom 9) (cell (atom 2)
         (cell (cell (atom 1) bat) (cell (cell (atom 0) (atom 2)) (cell (atom 1) ctx)))))
       (cell (atom 0) (atom 3))

/-- How a gate's outcome lifts to a stack outcome. -/
def liftOut (r : Noun) : Outcome → Outcome
  | .val v => .val (cell v r)
  | .exit  => .exit

/-- **The calling theorem.**  Outcome-polymorphic: it carries the value case and
    the crash case at once, since `liftGate`'s autocons is strict in its left
    operand and `op9` passes its tail outcome through. -/
theorem liftGate_correct (bat ctx a r : Noun) (o : Outcome)
    (h : NockEval (mkGate bat a ctx) bat o) :
    NockEval (cell a r) (liftGate bat ctx) (liftOut r o)
```

Then the pair that gives the guard-emission rule its teeth. `decBat` is Hoon's
compiled `++dec`; `dec_correct` / `dec_underflow` / `dec_cell_diverges` are its
⊥ profile.

```lean
theorem liftGate_decBat_agrees (n : Nat) (r ctx : Noun) :
    NockEval (cell (atom (n+1)) r) (liftGate decBat ctx) (.val (cell (atom n) r))

theorem liftGate_decBat_underflow (r ctx : Noun) :
    NockEval (cell (atom 0) r) (liftGate decBat ctx) .exit

/-- On a cell argument the naive lift *diverges*: `liftGate` is strict in the
    gate's outcome, and `decBat` has none. -/
theorem liftGate_decBat_cell_diverges (x y r ctx : Noun) :
    Diverges (cell (cell x y) r) (liftGate decBat ctx)

/-- **The refusal.**  Hoon's `++dec`, naively lifted, is not denotable as a
    `Word`.  Not a limitation of the model — the model correctly rejecting an
    unguarded formula.  `phi .dec` is denotable precisely because Λ emitted the
    domain guards (and, per §2, emitted them at the right axis). -/
theorem liftGate_decBat_not_a_word (x y r ctx : Noun) :
    ¬ ∃ w : Word, phi w = liftGate decBat ctx :=
  not_denotable_of_diverges (liftGate_decBat_cell_diverges x y r ctx)
```

## 5. Oracle results (already run; proofs unblocked)

Trial protocol: transcribe `phi` verbatim; the table is the defendant; produce
a counterexample, never an edit.

| formula | corpus | result |
| --- | --- | --- |
| printed `φ_dec`, **Reading A** | 6 stacks | valid inputs `.exit`; cell arg **diverges** — ❌ refuted |
| printed guarded-dec, **Reading B** | 6 stacks | invalid arms correct; valid inputs **diverge** — ❌ refuted |
| **corrected** `φ_dec` (§2) | 48 subjects, every ⊥ arm | **0 mismatches** ✅ |
| artifact's independent stack-native `dec` | 48 subjects | **0 mismatches** ✅ |
| corrected vs. independent, pointwise | 48 subjects | **identical** ✅ |

Root cause isolated:

```
nockF 3000 (cell (atom 5) (atom 77)) countUp  =  none      -- stack subject: diverges
nockF 3000 (atom 5)                  countUp  =  .val 4    -- bare atom: correct
fasO (atom 2) (atom 5)                        =  none      -- Reading A's guard crashes
```

`<count-up>` is correct and built for a bare atom; the guards are correct for a
stack. They cannot both be right about the same subject.

**Independent convergence.** Before the manuscript listing was available, this
artifact derived a guarded `dec` from the ⊥ domain alone — stack-native, guards
at axis 2, purpose-built loop core `[loopBat [b [a r]]]` (axes 14/15). It also
passes at 0 mismatches and agrees pointwise with §2 on all 48 subjects. The two
converged on the *denotation*, not the *shape*. §2 is adopted because it changes
two axes of the manuscript and nothing else; the artifact discards its own.

## 6. Deferred to SPEC-PHASE4B-CLASSD

Drafted after the `while` oracle trial.

- `CEval` as a **relation** (ratified), divergence by absence on both sides.
- The **simulation pair**: forward (`CEval t S o → NockEval S (N t) o`, induction
  on the `CEval` derivation) and backward (`NockEval S (N t) o → CEval t S o`,
  induction on `NockEval` derivations of compiled terms). Backward needs
  inversion lemmas characterizing `N`'s image; a "compiled formulas are
  recognizable" characterization prunes most constructor cases wholesale.
- `CEval` determinism is **not** to be proved: it transfers through the
  simulation pair from `NockEval.deterministic`.
- `Term` (the `ifte`/`while` algebra), `N`'s extension, the `while` fixpoint schema.
- The fueled `CsemF` **oracle**, in its own module, imported by nothing in the
  proof chain.

**Prior, updated.** The `dec` row's axes were hand-computed and survived seven
editorial passes. The `while` schema's axes (flag at 4, stack′ at 5, `L` at 6,
the autocons core rebuild) were computed the same way, under a subject that
*grows* under `op8` — strictly harder than the straight-line lookups of Tables
A and B, and harder than `dec`, which just failed. `while` gets the oracle
before it gets a proof.
