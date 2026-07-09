# DEFENDANT-CLASSD: Verbatim Schemas and Oracle Trial Protocol

**Status:** the Nock schemas and C listings in §2–§4 are transcribed verbatim
from the manuscript and are ON TRIAL under the §5 protocol of SPEC-PHASE4.
Do not correct them, however obviously; a failure is a finding about the
paper. The Term encoding in §1 is RULED (a design decision, not a
transcription) — implement as written.

Provenance note for the record: the while axis walk in §3 was hand-computed
by the same method, by the same author, as the convicted dec listing —
under a subject that is rebound **twice** (nested opcode 8), which is the
strictly harder case. The author's stated prior: acquittal more likely than
not (the walk survives two rechecks made with the rebinding lesson fresh),
but the reference class supports material conviction probability. The
oracle rules; the prior is recorded only so the verdict can be scored
against it.

---

## 1. Term encoding — RULED

Continuation-carrying terms, mirroring the paper's grammar
`p ::= ε | w·p | ifte(q₁,q₂)·p | while(p_t,p_b)·p` exactly:

```lean
inductive Term
  | nil   : Term                          -- ε
  | seq   : Word → Term → Term            -- w · p
  | ifte  : Term → Term → Term → Term     -- ifte(q₁, q₂) · p   (q₁ q₂ cont)
  | while : Term → Term → Term → Term     -- while(p_t, p_b) · p (test body cont)
  deriving Repr
```

`Prog = List Word` embeds by `p.foldr .seq .nil`; an embedding lemma
(`N (embed p) = N p` up to the shared fold, and `CsemF` agreement) is a
Phase 4b proof item, NOT an oracle prerequisite.

Rationale (recorded, not negotiable): nested-list encodings
(`ifte : List Term → List Term → Term`) buy nothing and cost nested
induction principles; the continuation-carrying form keeps `N` a single
structural fold and makes the backward-simulation inversion grammar as
small as possible.

## 2. `N` over `Term` — schemas verbatim

```lean
def N : Term → Noun
  | .nil          => cell (atom 0) (atom 1)                 -- [0 1]
  | .seq w p      => cell (atom 7) (cell (phi w) (N p))     -- [7 φ_w N(p)]
  | .ifte q₁ q₂ p => cell (atom 7) (cell (Nifte q₁ q₂) (N p))
  | .while t b p  => cell (atom 7) (cell (Nwhile t b) (N p))
```

where, transcribed from the manuscript (Equations classd-ifte and
classd-while):

**ifte** — `Λ_N(ifte(q₁, q₂)) = [6 [0 2] [7 [0 3] Λ_N(q₁)] [7 [0 3] Λ_N(q₂)]]`

```lean
def Nifte (q₁ q₂ : Term) : Noun :=
  cell (atom 6) (cell
    (cell (atom 0) (atom 2))
    (cell (cell (atom 7) (cell (cell (atom 0) (atom 3)) (N q₁)))
          (cell (atom 7) (cell (cell (atom 0) (atom 3)) (N q₂)))))
```

**while** — `Λ_N(while(p_t, p_b)) = [8 [1 L] 9 2 0 1]` with

```
L = [8 [7 [0 3] Λ_N(p_t)]
       [6 [0 4]
          [9 2 [0 6] [7 [0 5] Λ_N(p_b)]]
          [0 5]]]
```

```lean
def Lwhile (t b : Term) : Noun :=
  cell (atom 8) (cell
    (cell (atom 7) (cell (cell (atom 0) (atom 3)) (N t)))
    (cell (atom 6) (cell
      (cell (atom 0) (atom 4))
      (cell (cell (atom 9) (cell (atom 2)
              (cell (cell (atom 0) (atom 6))
                    (cell (atom 7) (cell (cell (atom 0) (atom 5)) (N b))))))
            (cell (atom 0) (atom 5))))))

def Nwhile (t b : Term) : Noun :=
  cell (atom 8) (cell
    (cell (atom 1) (Lwhile t b))
    (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))))
```

Note the parse commitment in `Lwhile`'s continue branch:
`[9 2 [0 6] [7 [0 5] Λ_N(p_b)]]` reads as `[9 2 [[0 6] [7 [0 5] …]]]` —
opcode 9, axis `2`, core-formula an **autocons** of `[0 6]` (recovers `L`)
with `[7 [0 5] Λ_N(p_b)]` (new stack from `S′`). If the Lean transcription
above mis-parenthesizes the manuscript's bracket text, that is MY
transcription error, not a manuscript conviction — flag it separately.

## 3. The manuscript's axis-walk claims (enumerated for verdict localization)

These are the specific claims the oracle adjudicates; a conviction should
name which one fails:

- **W1**: outer 8 pins `L`; subject becomes `[L S]`; `9 2 0 1` fires `L`
  against `[L S]`.
- **W2**: inside `L`, the stack sits at axis 3 (so `[7 [0 3] N(p_t)]`
  evaluates `p_t` against `S`).
- **W3**: after the inner 8 pins `t = *[S N(p_t)] = [flag S′]`, the subject
  is `[t L S]`: flag at axis **4**, `S′` at axis **5**, `L` at axis **6**.
- **W4**: exit branch `[0 5]` returns `S′`.
- **W5**: continue branch rebuilds the core as `[L S″]` with
  `S″ = *[S′ N(p_b)]` and fires arm 2, i.e. the loop re-enters with the new
  stack and the same `L`.
- **W6**: opcode 6 on a non-loobean flag crashes (inherited from the ISA),
  and a flag that is a cell, or an atom ≥ 2, is non-loobean.
- **I1** (ifte): flag at axis 2, remainder at axis 3; each branch
  pre-composes `[0 3]`, so branches run on the remainder with the flag
  consumed.

## 4. The C-side defendant and `CsemF`

The C listings from the manuscript, verbatim — these are what `CsemF`
transcribes:

**ifte:**
```c
noun f = pop(m);
if (!is_loobean(f))  bail(m);
if (f == 0) { /* C(q1) */ } else { /* C(q2) */ }
```

**while:**
```c
for (;;) {
  /* C(p_t) */
  noun f = pop(m);
  if (!is_loobean(f))  bail(m);
  if (f != 0)  break;
  /* C(p_b) */
}
```

Semantic conventions carried from the manuscript prose:

- **ifte(q₁,q₂)**: flag occupies the top and is consumed; `0` selects q₁,
  `1` selects q₂, anything else crashes; branches execute on the remainder;
  the branch's result feeds the continuation.
- **while(p_t,p_b)**: `p_t : stack → [flag stack′]`, flag consumed; on `0`
  run `p_b` on `stack′` and repeat (i.e. re-enter at `p_t`); on `1` exit
  yielding `stack′`; anything else crashes. The exit stack feeds the
  continuation.
- `pop` on a stack that is an atom bails deterministically (matches the
  Nock side, where the flag lookup crashes).

`CsemF : Nat → Term → Noun → Option Outcome` — the fueled oracle.
Requirements, not implementation: fuel decrements on every recursive call
including the `while` re-entry; `none` = fuel exhausted only (never used
for a semantic verdict); crash cases return `some .exit`; results must be
monotone in fuel by construction (no proof required — the oracle is not in
the proof chain). Indicative clause for `while` (the C listing is
normative; if this sketch and the listing disagree, the listing wins):

```lean
| k+1, .while t b p, S =>
    match CsemF k t S with
    | none => none
    | some .exit => some .exit
    | some (.val T) =>
      match T with
      | atom _ => some .exit                    -- no flag to pop
      | cell (atom 0) S' =>
          match CsemF k b S' with
          | none => none
          | some .exit => some .exit
          | some (.val S'') => CsemF k (.while t b p) S''
      | cell (atom 1) S' => CsemF k p S'        -- exit; run continuation
      | cell _ _ => some .exit                  -- non-loobean flag
```

(`atom n, n ≥ 2` falls into the last-but-one wildcard — make sure the
transcription crashes it; loobean means exactly `atom 0` or `atom 1`.)

**Quarantine (import direction, same discipline as RuntimeBridge):**
`CsemF` lives in its own module; nothing in the proof chain imports it,
ever; it may import `Term`/`N`/`cw`. Grep gate accordingly.

## 5. Probe classes for the corpus

Build the corpus from the existing Word set (no literal-push word exists;
flags must be computed). Known-useful generators, verified expressible:

- `[dup, celq]` — flag `0` iff top is a cell (spine-descent test).
- `[dup, eq]` — flag always `0` (tisN a a): the divergence generator.
- `[dup, inc, eq]` — flag always `1` on atom tops (tisN a (1+a)); crashes
  on cell tops (inc): an always-exit test with its own crash arm.

Required probe classes, each on both the Nock side (`nockF`, escalating
fuel) and the C side (`CsemF`, same fuels):

1. **Value paths**: data-dependent iteration counts — e.g.
   `while([dup,celq],[head])` walks the left spine to the first atom leaf;
   run over nouns of varying spine depth, including depth 0 (immediate
   exit... check: on atom top the flag is `1` → exit with `S′`; confirm
   which stack the convention hands the continuation).
2. **ifte both branches**, and non-loobean flags of BOTH kinds: atom ≥ 2
   and cell flags (W6/I1).
3. **Flag-pop on an atom stack** (test/`p_t` output an atom, or ifte on an
   atom subject): crash agreement on both sides.
4. **Crash inside a branch / inside a loop body**:
   `while([dup,eq],[head])` — test always `0`, body eventually heads an
   atom: terminates by `.exit` on every finite noun, at an
   iteration count equal to spine depth. Verify `.exit` agreement AND that
   both sides exit at the same fuel-independent point (mismatched
   iteration-of-crash is a conviction even when both eventually exit).
5. **Divergence**: `while([dup,eq],[])` — `none` on both sides at fuels
   {10, 50, 200, 1000, 5000}; and the divergence must be two-sided (a side
   that returns anything convicts).
6. **Nesting**: while-in-body, while-in-branch, ifte-in-test, and a
   sequenced continuation after each (the continuation is where a wrong
   exit-stack convention will surface — probe with a continuation that
   inspects the stack, e.g. `[celq]`, so a wrong `S′` changes the value).
7. **Continuation after crash**: crash in the loop must hide the
   continuation on both sides (strictness through the fold's 7).

Corpus size and specific subjects are the implementer's craft, per the
Table A/B precedent (280 nouns, every match arm). The seven classes above
are the floor, not the ceiling.

## 6. Verdict format

As already agreed and recorded: raw first — corpus description, fuel
schedule, mismatch table (or its emptiness), no interpretation and no
proposed fix in the same message. Convictions localize against §3's claim
labels (W1–W6, I1) where the evidence permits. Acquittal arrives in the
identical format. Either number goes in the paper.
