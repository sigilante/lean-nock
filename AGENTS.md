# AGENTS.md — context for AI assistants

## Project

A Lean 4 mechanization of **jet correctness** for Nock 4K. It is the companion
artifact to *Jet-Accelerated Code and the Co-Design Problem* (N. E. Davis,
*Urbit Systems Technical Journal*). The scope is the paper's three-valued jet
contract and its co-derivation approach: a source language Λ compiled both to
Nock (`Λ_N`) and to a big-step C model (`Λ_C`), with a composition theorem
between them. See `README.md` for the claim-by-claim status table.

## Invariants — do not break

- **Axiom footprint.** Every theorem in `Nock/Audit.lean` must stay within
  `{propext, Quot.sound}`. The manifest is elaborated by `lake build` and
  throws on drift. Never widen the allow-list to make a build pass.
  - `simp` on `Nat`/`Noun` disequalities can silently pull in
    `Classical.choice`; prefer `Noun.noConfusion`, `omega`, or named lemmas.
- **Frozen names.** Manifest names are cited by the paper. Renaming or deleting
  one fails the build, which is deliberate. New cited theorems go into the
  manifest.
- **Quarantine direction.** `Nock/RuntimeBridge.lean` (`native_decide`) and
  `Nock/Oracle.lean` (fueled C oracle) may import the proof chain; nothing in
  the proof chain may import them. `scripts/gates.sh` enforces this.
- **No `sorry`, no `axiom`, no `panic!`** outside the runtime evaluator
  `partial def nock` in `Nock/Basic.lean`.
- **The tables are defendants.** `phi` formulas are transcribed verbatim from
  the paper and are never edited to make a proof close. A formula that fails is
  reported (see `TABLE-REPORT.md`), not fixed silently.
- **No Mathlib.** Pure Lean 4 core.

## Verify

```sh
rm -rf .lake/build && lake build && ./scripts/gates.sh && ./scripts/oracle-check.sh
```

## Proof idioms

- `NockEval` is the specification; `nockF` is the transparent fuel evaluator
  tied to it by `nockF_sound` / `nockF_complete`. `partial def nock` is opaque
  and is for `#eval` only.
- Divergence is absence of derivation: `Diverges a f := ∀ o, ¬ NockEval a f o`.
- To show an outcome is the only one possible: `cases` on the derivation,
  discharge `crash_malformed` with `simp [Malformed, <defs>]`, and rule out
  impossible branches with `NockEval.deterministic` against a known derivation.
  See the private `no_val_exit` / `det_val` helpers in `Nock/Gate.lean`.
- `fasO` and `haxO` do not reduce under `rfl`; use the `fasO_*` / `haxO_*`
  lemmas in `Nock/Proofs.lean`.

## Open work (see README "What is not claimed")

- Class C `mul` / `div` as guarded words (`dec`, `add`, `sub` are done).
- A `+mock` model making the unsoundness of the two-valued contract a theorem.
- A quarantined bridge to `nockchain/pure-nock-lean`'s evaluator. It needs
  Mathlib and admits `Classical.choice`, so it must never enter the proof chain.
- Adding a `Word` constructor: extend `cw` exhaustively (no wildcard arms),
  add a `leaf_*` lemma, and add a bullet to `leaf_correct`.
